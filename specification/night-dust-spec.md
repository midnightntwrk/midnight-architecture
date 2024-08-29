# Night & Dust Specification draft

The intention of this draft is to sketch the high-level workings of unshielded
tokens, Night, and Dust. This document will be later refined to include the
full details of their workings.

## Unshielded tokens, basics

We construct an unshielded UTXO token set, for Night, extensible to other token
types. UTXOs, or unspent transaction outputs, are data recording inividual
transaction outputs, each having a value and an owner. As we are extending
these with token types, they also have an associated token type in our model.

### Preliminaries

To start with, we define some basic types. Note that Midnight uses SHA-256 as
its primary hash function. To simplify in this spec, we will assume that all
data is hashable. We make the hash's output type `Hash<T>` parametric over the
input type `T`, to capture structurally which data is used to produce which
outputs. `...` signals that a part goes beyond the scope of this spec.

We then define:

```rust
type Hash<T> = [u8; 32]; // The SHA-256 output block

// Contract address derivation is beyond the scope of this document, aside from
// it being a hash.
type ContractAddress = Hash<...>;

// Each contract address can issue multiple token types, each having a 256-bit
// domain separator
type TokenType = Hash<(ContractAddress, [u8; 32])>;

// NIGHT is a `TokenType`, but it is *not* a hash output, being defined as zero.
const NIGHT: TokenType = [0u8; 32];
```

We also need to assume public key cryptography. We use Schnorr over Secp256k1,
as specified in [BIP 340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki).

```rust
type SigningKey = secp256k1::Scalar;
type VerifyingKey = secp256k1::Point;
type Signature = secp256k1::schnorr::Signature;
```

### Building UTXOs

We define the basic structure of an individual UTXO, define the data for
creating a new UTXO output, which is just the UTXO itself, and for spending a
UTXO. The latter acts not just as a standalone transaction part, but
encompasses other data – this is because a spend comes with conditions on what
it is used for. Defining the composition of these is beyond this document.
Finally, the state maintained for UTXOs at any time is simply a set of all
UTXOs.

```rust
struct Utxo {
    value: u128,
    owner: Hash<VerifyingKey>,
    type_: TokenType,
    nonce: [u8; 32],
}

type UtxoOutput = Utxo;

struct UtxoSpend<T> {
    sign_over: T,
    spend: Utxo,
    owner: VerifyingKey,
    // signature over: (sign_over, spend)
    signature: Signature,
}

struct UtxoState {
    utxos: Set<Utxo>,
}
```

A transaction would consist of a chain of `UtxoSpend<T>`, where `T` would be a
fragment containing either more `UtxoSpend`s, or `UtxoOutput`s, and contract
interactions. This would have to be balanced in that the sum of the spends must
be greater than or equal to the sum of the outputs. The effect would be the
removal of each of the spends from the `UtxoState` (which must be unique and
present), and the insertion of the outputs into the `UtxoState` (which must be
unique and *not* present). Note that transactions will be fully defined
elsewhere.

### Faerie dust, atomic exchange, and replay protection

One thing of note is the presence of the `nonce` field above. Any UTXO system
needs to disambiguate different UTXOs of the same value, owned by the same
key. Typically, UTXOs are disambiguated by the originating transaction's hash,
and the output number in this transaction. Importantly, these are both
guaranteed to be unique: If the inputs are unique, and can only be spent once,
the transaction's hash must also be unique. This directly prevents replay
attacks, as any replayed transaction will attempt to double-spend UTXOs that
have already been spent, and cannot be re-created. As all transaction must pay
for fees, and must be balanced, all transactions must have at least one input
UTXO.

This approach is directly incompatible with intents however, that is,
transactions which are not necessarily balanced. Crucially, we do envision use
cases where transactions have no unshielded inputs. While our fee payments
could be designed to also prevent replays in isolation, we also envision use
cases where a user does not directly cover their fees, but relies on a
third-party to do so. It is therefore entirely possible for users to create
outputs *with no corresponding inputs*, and for this to be legitimate.

As a result, we instead rely on a user-selected nonce, with the caveat that
this can lead to replay attacks and loops: 

FIXME: on no, can we even prevent the replays?

## Dust

Dust is designed to be *resettable*. That is, the entire Dust subsystem state
can be deleted without significant impact on users. Note that some impact is
likely unavoidable, but this is considered an acceptable cost.

Due to this, Dust makes heavy use of SNARK friendly cryptography, and the
current proof system's base curve `C`.

Dust public keys are a (snark-friendly) hash of dust secret keys:

```rust
type DustSecretKey = C::Scalar;
// Nb. C::Hash<T> = C::Scalar. The hash function is assumed to be Poseidon
// over C
type DustPublicKey = C::Hash<DustSecretKey>;
```

A dust output consists of its value, owner, nonce, and creation time. Note
that, unusually, negative values *are permitted* here. This is used to allow
redirection of dust generation for free, by effectively incurring a debt. In
all other cases, created outputs must have a positive value.

```rust
struct DustOutput {
    value: i128,
    owner: DustPublicKey,
    nonce: C::Hash<(Hash<()>, u32, C::Scalar)>,
    seq: u32,
    ctime: Timestamp,
}
```

The nonce is defined as `nonce = C::hash((night_utxo.nonce, n, key))`, where
`night_utxo` is the corresponding Night UTXO that created this Dust output, and
`n` is the sequence number `seq` in this Dust evolution (0 at the initial
creation), and `key` is the owner's public key if `n = 0`, and the owner's
*secret* key otherwise. This ensures that the `DustOutput` is publicly
computable if and only if it is the initially created one, and is only
computable by the owner otherwise.

### Dust generation

In addition to dust outputs, dust generation information is needed to compute
the balance of the dust output at the time it is spent. This consists of a
Merkle tree with leaves containing the (Dust) owner of a UTXO, the *initial*
(Night) nonce, the value of corresponding Night UTXO, and the time the Night
UTXO was spent. The final value is set to `Timestamp::MAX` if it *has not yet
been spent*.

```rust
struct DustGenerationInfo {
    value: u128,
    owner: DustPublicKey,
    nonce: Hash<()>,
    dtime: Timestamp,
}
```

Additionally, a set of `(value, owner, nonce)` tuples is maintained, to prevent
creation of multiple outputs with the same nonce, which could constitute a
faerie-gold-like attack.

```rust
struct DustGenerationUniquenessInfo {
    value: u128,
    owner: DustPublicKey,
    nonce: Hash<()>,
}

struct DustGenerationState {
    generating_tree: MerkleTree<DustGenerationInfo>,
    generating_tree_first_free: usize,
    generating_set: Set<DustGenerationUniquenessInfo>,
    night_indices: Map<UtxoOutput, usize>,
    historic_roots: Map<Timestamp, MerkleTreeRoot>,
}
```

`historic_roots` tracks past versions of `generating_tree` that are still permitted
to prove against. This is regularly filtered, so only the most recent roots are
valid, within a validity window `dust_validity`. `night_indices` tracks the
position of each Night utxo in the `generating_tree`, allowing these to be
updated with the correct `dtime` when the corresponding Night utxo is spent.

### Spending Dust

Dust will follow Zerocash commitment/nullifier structure. Each `DustOutput` has
two projections, a `DustCommitment` and a `DustNullifier`, both produced using
the `C::hash`. The nullifier set is a set of the former, and the commitment set
a Merkle tree of the latter. As the dust *genreation* set has faerie-gold
attack mitigation, no mitigation is needed for Dust itself.

```rust
struct DustPreProjection<T> {
    value: i128,
    owner: T,
    nonce: C::Hash<(Hash<()>, u32, C::Scalar)>,
    ctime: Timestamp,
}

type DustCommitment = C::Hash<DustPreProjection<DustPublicKey>>;
type DustNullifier = C::Hash<DustPreProjection<DustSecretKey>>;
```

A Dust transaction will always be a 1-to-1 transfer, consuming one `DustOutput`
and producing another. The transaction must be associated with a time `t`, and
output a public fee payment `v_fee`. The input `inp: DustOutput`'s value must
be recomputed for time `t`, and the associated `gen: DustGenerationInfo`. The
function to compute this will be discussed separately, and is assumed here,
it's result is `v_in: i128`.

The output `out: DustOutput` is defined as (where the output `value` *must* be
non-negative):

```rust
fn updated_value(inp: DustOutput, gen: DustGenerationInfo) -> i128;

out = DustOutput {
    value: updated_value(inp, gen) - v_fee,
    owner: inp.owner,
    nonce: transient_hash(gen.nonce, inp.seq + 1, dust_sk),
    seq: inp.seq + 1,
    ctime: t,
}
```

The public state of Dust is simply a commitment Merkle tree, a nullifier set,
and the historic roots & first free. To simplify the fee payment transaction
fragment, the timestamps used in the Dust historic roots, and the generation
historic roots should be the same.

```rust
struct DustState {
    commitments: MerkleTree<DustCommitment>,
    commitments_first_free: usize,
    nullifiers: Set<DustNullifier>,
    historic_roots: Map<Timestamp, MerkleTreeRoot>,
}
```

A Dust payment then consists of:
- Some data to sign over
- A timestamp `t`
- A value `v_fee`
- A Dust nullifier (for the spent Dust)
- A Dust commitment (for the new Dust output)
- A ZK proof (more on that below)

```rust
struct DustSpend<T> {
    sign_over: T,
    t: Timestamp,
    v_fee: u128,
    nullifier: DustNullifier,
    commitment: DustCommitment,
    proof: Proof,
}
```

When applying this, the proof is checked against `transient_hash(sign_over)`,
`t`, `dust_root = <dust state>.historic_roots[t]`, `gen_root = <gen
state>.historic_roots[t]`, `v_fee`, `nullifier`, and `commitment`. *Private*
inputs to the proof are:

- The secret key `sk`
- The input `inp: DustOutput` and its Merkle path `inp_path`
- The relevant `gen: DustGenerationInfo`, and its Merkle path `gen_path`

Then the proof asserts that:
- `gen` is under `gen_root` at `gen_path`
- `inp` is under `inp_root` at `inp_path`
- `inp`'s nullifier is `nullifier`
- `out` is computed as above
- `out`'s commitment is `commitment`

When applying, the nullifier is inserted into `<dust state>.nullifiers`, with a
transaction failure if it already exists.

### Spending Night

The spending of Night should affect the `DustGenerationState`. This requires a
change to the semantics of UTXO outputs, and a change to the transaction, as
this must nominate an output `DustPublicKey`. Night transfers should still be
able to operate solely on Night addresses, which implies that even regular Dust
transfers need to de-register any generation from spent UTXOs.

```rust
struct GeneratingUtxoOutput {
    regular: Utxo,
    generation_owner: DustPublicKey,
}
```

This can be used over `UtxoOutput` to also update `DustGenerationState`, by
inserting a new generation information corresponding to the new UTXO output.
Finally, any spend where `type_ == NIGHT` should try to update the
`DustGenerationState` to set the `dtime` of any corresponding generation
information (if this does not exist, this is a no-op).

In order to permit Night to be transferable *without* having Dust, a basic
{1,2}-to-{1,2} UTXO transfer will be permitted to *not* have Dust funding it.
The output Night will be placed in 'cooldown', where any attempt to spend it
will be considered invalid for as much time as it would take to generate the
fees. The output Dust (if any) will be given a negative balance to account for
these fees. The cooldown period must be less than a given threshold to prevent
spending of small UTXOs that will not cover their own fees in any reasonable
amount of time (suggestion: 1 month).

This consists of a new `CooldownState`, tracking Night UTXOs and when they
become spendable:

```rust
struct CooldownState {
    time_spendable: Map<Utxo, Timestamp>,
}
```

This is updated if an unfunded transaction is deemed eligible for cooldown by
adding its outputs to the cooldown set, with the same timestamp computed to
when they jointly can cover the unfunded transaction's fees.

It is checked and updated on a Night spend, by ensuring that if the spent UTXO
is a key in the map, that it's timestamp is in the past. If so, the entry is
removed. If the timestamp is in the future, the transaction is invalid.

#### Updating the Dust states

When a Night UTXO `utxo` is spent, the generation state `gen:
DustGenerationState` is updated by setting
`gen.generating_tree[gen.night_indices[utxo]].dtime` (if it exists) to the current block's
time.

When a new *generating* Night UTXO `utxo` is created, the generation state `gen:
DustGenerationState` is updated by:

- Inserting `DustGenerationInfo { value: utxo.regular.value, owner: utxo.generation_owner, nonce: utxo.regular.nonce, dtime: Timestamp::MAX }` into `gen.generating_tree[gen.generating_tree_first_free]`
- Inserting `DustGenerationuniquenessInfo { value: utxo.regular.value, owner: utxo.generation_owner, nonce: utxo.regular.nonce }` into `gen.generating_set`, failing if it is already present
- Setting `gen.night_indices[utxo.regular] = gen.generating_tree_first_free`
- Incrementing `gen.generating_tree_first_free`

(`historic_roots` should be updated at a block level, not a transaction level, so is left out here)

A new Dust output is also created, and its commitment inserted into the `DustState`. This output is defined as:

```rust
utxo = DustOutput {
    value: value,
    owner: utxo.generation_owner,
    nonce: transient_hash(utxo.regular.nonce, 0, utxo.generation_owner),
    seq: 0,
    ctime: t,
}
```

where `t` is the block time, and `value` is `0`, unless the output is a
cooldown output, in which case it is `-fee`, where `fee` is the (part of) the
transaction fee this Dust output covers.
