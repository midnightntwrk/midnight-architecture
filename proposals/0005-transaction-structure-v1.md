# Proposal 0005: Transaction Structure (Version 1)

This proposal captures Midnight's initial transaction structure, as planned for
the 2022 devX workshop. It is not to be taken as a binary specification, but an
overview of the types of transactions, the parts that make up transactions, and
how their assembly and verification functions.

# Problem Statement
Since Midnight pivoted to fully focus on privacy in smart contracts,
transactions have largely been mocked, and where they existed, largely
consisted just of a single contract call, often without accompanying proofs. To
emphasise Midnight's practical applicability, it is important to have a
transaction structure that, while not necessarily final, is cryptographically
sound, and allows for contract-to-contract interaction and for the existence of
privacy-preserving funds.

# Proposed Changes

## Data Types

The following data types make up a `Transaction`:

### `Transaction`

A `Transaction` consists of a `ZSwapOffer`, a set of `CriticalSection`s, and a
`BindingRandomness`.

**Merging**: A `Transaction` can be merged with another transaction by:
* Merging their respective `ZSwapOffer`s.
* Merging their respective `CriticalSection`s.
* Multiplying their respective `BindingRandomness`'s.

This is only permissible if:
* The intersection of `CriticalSection`s is empty.
* The resulting transaction would not contain multiple `CriticalSections`
  containing `ContractCall`s to the same address. (This is fine *within* a
  `CriticalSection`!)

**Validation**: A transaction is valid if:
* Its components are valid.
* The sum of its `HomomorphicCommitment`s can be opened with the
  `ZSwapOffer`s `deltas`, and the `BindingRandomness`.
* `deltas'` is balanced. That is, it does not have positive values for any type.
* `deltas'` is defined in terms of the `ZSwapOffer`'s `deltas`:
  * `deltas'(type) = deltas(type) + adjustment(type)`.
  * `adjustment(<transaction_tickets>)` is the sum of all public oracle query costs in `CriticalSection`s, as well a cost proportional to the size of the transaction.
  * `adjustment(H(<address>))` is **minus** the sum of all `x` in `mint(x)`
    kernel queries by contract `<address>`, where `H` is a hash-to-type
    function.
* Any `claim_zswap_note` or `claim_zswap_nullifier` kernel call in the
  `CriticalSection`s is unique and corresponds to a note or nullifier present
  in `ZSwapOffer`.

**Effects**: A transaction has the effect of its parts, which are commutative.

### `ZSwapOffer`

A `ZSwapOffer` consists of a set of `ZSwapInput`s, a set of `ZSwapOutput`s, a
set of `ZSwapIO`s, and a mapping from coin types to values.

**Merging**: A `ZSwapOffer` is merged with another by:
* Taking the unions of each of the sets.
* Summing the values of each key in the mappings (filling missing keys with zero).

This is only permissible if:
* The intersections of each pair of sets is empty.

**Validation**: An offer is valid if:
* Its components are valid.

**Effects**: A ZSwap offer has the effect of its parts, which are commutative.

### `ZSwapInput`

A `ZSwapInput` consists of a nullifier, a `HomomorphicCommitment`, an
optional contract address, a Merkle tree root, and a ZK proof.

**Validation**: An input is valid if its proof is valid with respect to the
other fields, the Merkle tree root is a valid past root of note
commitments, and the nullifier not yet recorded in state.

The proof demonstrates that the nullifier is a valid nullifier for a note
present in the Merkle tree with the given root, that its creator either knew
its secret key, or that it is associated with the given contract address, and
that the `HomomorphicCommitment` is equal to $g^r H(\mathsf{ty})^{-v}$, where
$\mathsf{ty}$ is the type of the coin, $v$ its value, and $r$ arbitrary.

**Effects**: A ZSwap input has the effect of adding the nullifier to the state's nullifier set.

### `ZSwapOutput`

A `ZSwapOutput` consists of a note commitment, a `HomomorphicCommitment`, an
optional contract address, an optional coin ciphertext, and a ZK proof.

**Validation**: An input is valid if its proof is valid with respect to the
other fields, and the ciphertext is the expected length.

The proof demonstrates that the note commitment is to a note of type
$\mathsf{ty}$ and value $v$, and that the `HomomorphicCommitment` is equal to
$g^r H(\mathsf{ty})^v$ for arbitrary $r$. Further, if the note is
contract-owned, it proves that the contract address is correctly revealed, and
the note is binding to the coin ciphertext.

**Effects**: A ZSwap output has the effect of inserting the note commitment into
the Merkle tree of valid notes commitments at the first free index.

### `ZSwapIO`

A `ZSwapIO` is for coins created and spent in the same transaction, and
consists of all fields of both `ZSwapInput` and `ZSwapOutput`, except the
Merkle tree, which is taken to be the sparse tree containing just the note
commitment of the `ZSwapOutput`. The contract address field is only present
once, while the note has two value commitments, one positive and one negative,
and two proofs are present.

**Validation**: The `ZSwapIO` validates if both its `ZSwapInput` and
`ZSwapOutput` parts validate.

*Observation*: This looks like it permits arbitrary-value (including more than
circulating supply!) flash loans within a transaction as a part of the system
design? Is that a problem?

**Effects**: A ZSwap IO has the effects of its corresponding input/output parts.

### `CriticalSection`

A `CriticalSection` is a sequence of either `ContractCall`s, or
`ContractDeploy`s, and a `HomomorphicZeroCommitment`.

**Validation**: A critical section is valid if all of its `ContractCall`s/`ContractDeploy`s
(validated in sequence) are valid, the `HomomorphicZeroCommitment` is valid, and
any `claim_contract_call` kernel calls in `ContractCall` parts resolve.
A `claim_contract_call(addr, entry_point, comm)` part resolves if and only if:
1. A subsequent `ContractCall` to `addr`, `entry_point` and with communications commitment `comm` exists
2. The kernel call is unique in the `CriticalSection`.

**Effects**: A critical section has the stateful effects of its `Contract{Call,Deploy}`s, applied in sequence.

**Costs**: The `CriticalSection` has a cost equivalent to the sum of its `ContractCall`s.

### `ContractCall`

A `ContractCall` consists of a contract address, a bitstring identifying its
entry point, a public oracle transcript, a communications commitment, and a ZK
proof.

The public oracle transcript is a vector of (optional) query/result pairs, where
queries follow the structure specified in [the micro ADT query
language](./0004-micro-adt-language.md), and results are Abcird values.

**Validation**: A contract call is valid if its zk-proof is valid, and its
effects are successfully applied to the current state. The proof is validated as follows:
1. Verification data, and transcript structure is retrieved from the ledger state using the contract address and entry point as keys.
2. The transcript is checked to adhere to the transcript structure.
3. The public input vector is initialized as `[H(contract_address, entry_point, bind_comm), comm_comm] ++ encode(transcript)`,
   where `bind_comm` is the binding commitment in the current `CriticalSection`s
   `HomomorphicZeroCommitment`, `H` is a fixed but arbitrary hashing function,
   and `encode` is the canonical Abcird encoding of the public oracle
   transcript.
4. The PI vector and proof  are validated with the verification data.

**Effects**: The effects of a contract call are the effects of the sequence of
ADT queries in the transcript applied to the contract specified by the contract
address's state. Exceptions to this are kernel-type calls, which *have no
effect* on this level, as they are handled at either the `Transaction` or
`CriticalSection` level. An ADT query succeeds if it can be sensibly carried
out, and produces the same result as recorded in the transcript when applied in sequence.

**Costs**: The `ContractCall` has a cost equivalent to the sum of all the query costs.

### `ContractDeploy`

A `ContractDeploy` consists of a contract's initial state.

**Validation**: A contract deploy is always valid.

**Effects**: The deployed contract's address is the hash of the
`ContractDeploy`. If this contract does not exist, it is created, with its state
set to the initial state defined by the `ContractDeploy`.

### `HomomorphicZeroCommitment`

A `HomomorphicZeroCommitment` is a `HomomorphicCommitment` with a Fiat-Shamir
proof-of-knowledge of exponent. That is, it consists of $c = g^r$, and a proof
of knowledge of $r$, ensuring that it is single-base, and effectively a value of
zero for every type is embedded.

The challenge in the Fiat-Shamir transform is taken to be not just $c$, but also
the hash of the rest of the `CriticalSection` this is a part of, ensuring that
the Fiat-Shamir proof is binding to the whole transaction part.

**Validation**: The Fiat-Shamir proof validates when given $c$, and the hash of
the rest of the containing `CriticalSection`.

### `BindingRandomness`

The binding randomness is an element of the embedded curve's scalar field.

### `HomomorphicCommitment`

The homomorphic commitments are points on the SNARK's embedded elliptic curve.
They have a representation $c = g^r \prod_{\mathsf{ty}}
H(\mathsf{ty})^{v_{\mathsf{ty}}}$, where $r$ is `BindingRandomness`, and
`v_{\mathsf{ty}}` is the value of type `\mathsf{ty}` recorded in `deltas`.

## Assembling Transactions

`ZSwapOffer`s and `CriticalSections` may be assembled independently. The wallet
should be able to generate `ZSwapInput`s its own coins, and the Lares backend to
do so from contract-owned coins. Likewise, the wallet should be able to generate
`ZSwapOutput`s from public keys, as should the Lares backend (although this
should also be able to do so from smart contract addressses). The backend should
be able to convert a `ZSwapOutput` to a `ZSwapIO` when the output is
contract-owned.

All of these parts will produce `BindingRandomness` in addition to these parts.
They may be combined into a single `ZSwapOffer`, with the corresponding
`BindingRandomness`es (when multiplied together) making this `Transaction` bind.

`CriticalSection`s are constructed by starting with an empty `CriticalSection`,
only with a binding commitment, and populating it while executing a transition
function. A dApp will initiate a call to a transition function with a contract
address `addr` and entry point `entry_point`, with an input `w`. The Lares
backend will lookup the corresponding transition function code locally (note
that this is *not* represented on-chain), and run it with the input `w`. During
this run, it will make a number of public oracle queries against the contract
state at `addr`.  These are recorded, along with their responses, in the public
transcript. During the execution, the Lares backend will also gather the
corresponding private transcript, as well as the result of the transition
function, `y`. Kernel calls have additional behaviour which will be detailed later.

A ZK-proof is created using the captured public transcript, a Pederson
commitment (with randomness `r`) to `(w, y)` and the `CriticalSection`s
`HomomorphicCommitment` as the public input vector, and `w` and the private
transcript as private inputs used to compute intermediate wire values.

For Kernel calls in this process, the transaction assembly as a whole may be affected.
1. For `claim_zswap_{input, output}` calls, these should be preceeded by either
   explicit or implicit constructions of the corresponding zswap inputs/outputs.
2. For `claim_contract_call` calls:
  * The transition function will first make a private query `const y = initiate_contract_call(addr, entry_point, w)`, which
    manifests as if the dApp had directly made this call as well.
  * It then computes the communications commitment in-circuit with a randomness supplied
    from a private `subcall_nonce()` query, which matches the `r` used in the
    just created `ContractCall`s communications commitment.
  * Finally, it runs `claim_contract_call(addr, entry_point, comm)` as a normal query, which is taken to succeed.

It's important to note that randomness is shares between caller and callee, and
that the binding commitment must be embedded in *all* of the proofs.

# Desired Result
This proposal is to describe what should take place of the mocked shapes of
transactions in multiple places, and should be taken as a tool to understanding
how to interact with the [ledger
prototype](/../../../../midnight-ledger-prototype) component.
