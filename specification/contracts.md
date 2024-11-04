# Contracts states and interactions

This specification's goal is to be fairly detached from the functioning of
smart contracts, however it does have to model them to some level of
abstraction. This is because the sequencing of transcripts, and the *effects*
of transcripts affects what are valid transactions, as contracts can directly
interact with other parts of the ledger.

At it's core, a contract has an *internal state type*, which we refer to as
`StateValue`. This type is left unspecified in this spec, however in practice
it is an [onchain runtime state
value](../apis-and-common-types/onchain-runtime/README.md#values).

```rust
type StateValue;
```

A contract's state consists of:
- It's current `StateValue`
- Maintenance information, in the for of a contract maintenance authority
- A mapping from entry point names to verifier keys
- A token balance mapping for this contract

```rust
struct ContractState {
    data: StateValue,
    operations: Map<Bytes, Zk<fn(...) -> bool>>,
    maintenance_authority: ContractMaintenanceAuthority,
    balance: Map<TokenType, u128>,
}
```

We will not detail contract maintenance authorities, or maintenance
transactions here at this point, but will assume they exist.

```rust
type ContractMaintenanceAuthority;
type MaintenanceUpdate;

impl LedgerContractState {
    fn apply_maintenance_update(self, upd: MaintenanceUpdate) -> Result<Self>;
}
```

## Deploying a contract

A contract is deployed simply by providing its initial state and a nonce. For
the deployment to be valid, this initial state must have zero balance.

```rust
struct ContractDeploy {
    initial_state: ContractState,
    nonce: [u8; 32],
}

type ContractAddress = Hash<ContractDeploy>;

impl ContractDeploy {
    fn well_formed(self) -> Result<()> {
        assert!(self.initial_state.balance.is_empty());
    }
}

struct LedgerContractState {
    contract: Map<ContractAddress, ContractState>,
}

impl LedgerContractState {
    fn apply_deploy(mut self, deploy: ContractDeploy) -> Result<Self> {
        assert!(!self.contract.contains(hash(deploy)));
        self.contract = self.contract.insert(hash(deploy), deploy);
        Ok(self)
    }
}
```

## Calling a contract

The most important interaction with a contract is the *call*, which executes
arbitrary code against the contract with a proof of correctness. It's core form
consists of:

- The address and entry point of the contract being called, used to retrieve
  the relevant circuit
- A guaranteed and fallible transcript (to be described later, for now, these
  can be thought of as a `fn(StateValue) -> Option<StateValue>`)
- A communication commitment, which commits to the inputs and outputs of the
  circuit being called
- A ZK proof

```rust
struct ContractCall<P> {
    address: ContractAddress,
    entry_point: Bytes,
    guaranteed_transcript: Option<Transcript>,
    fallible_transcript: Option<Transcript>,
    communication_commitment: Fr,
    proof: P::Proof,
}
```

Conceptually, first the guaranteed transcript is applied, then the fallible
transcript, with any failure during the fallible transcript application
reverting to the state after the guaranteed transcript was applied.

In practice, the `Transcript` is *not* just a partial function over
`StateValue`, but crucially also contains an `Effects` object, which describes
how this contract call interacts with the rest of the system. It also contains
a `gas` bound on the execution costs of the transcript program, but the details
for this are not covered in this spec.

Similarly, the input to the partial function is not just a `StateValue`, but it
also includes a `CallContext`, which can provide additional information to the
transaction about the conditions it is executed in.

```rust
struct Transcript {
    gas: u64,
    effects: Effects,
    // Model type, not actual
    program: fn(StateValue, CallContext) -> Option<StateValue>,
}
```

Note that the real program is a program as described in the [onchain runtime
specification](../apis-and-common-types/onchain-runtime/README.md).

### Effects

The effects of a contract include:
- Which Zswap coins the contract authorized to spend, by their nullifier
- Which Zswap coins the contract expected to receive, by their commitment
- Which Zswap coins the contract requires to be uniquely present as an output,
  by their commitment
- Which contract calls the contract requires to be uniquely present, by their:
  - Sequence number, for ordering
  - Contract address
  - Hash of the entry point used
  - Communication commitment expected
- Which Zswap coins the contract minted
- Which unshielded coins the contract minted
- Which unshielded coins are expected to have been received
- Which unshielded coins the contract authorized to spend
- Which unshielded outputs the contract requires to be uniquely present as a
  UTXO, or input to another contract
  - Note that the type allows encoding outputting Zswap/Dust tokens to a UTXO
    verifying key. Effects containing this are not considered well formed.

```rust
struct Effects {
    claimed_nullifiers: Set<CoinNullifier>,
    claimed_shielded_receives: Set<CoinCommitment>,
    claimed_shielded_spends: Set<CoinCommitment>,
    claimed_contract_calls: Set<(u64, ContractAddress, Hash<Bytes>, Fr)>,
    shielded_mints: Map<[u8; 32], u64>,
    unshielded_mints: Map<[u8; 32], u64>,
    unshielded_inputs: Map<TokenType, u128>,
    unshielded_outputs: Map<TokenType, u128>,
    unshielded_spends: Map<(TokenType, Either<Hash<VerifyingKey>, ContractAddress>), u128>,
}
```

### Context

The call context currently consists of time information, the block hash of
the parent block, and an optional caller, as a contract address or verifying
key hash.

```rust
struct CallContext {
    seconds_since_epoch: Timestamp,
    seconds_since_epoch_err: Duration,
    block_hash: Hash<Block>,
    caller: Option<Either<Hash<VerifyingKey>, ContractAddress>>,
}
```

The call context is in part derived from a block context, given at application
time, and in part from the containing `Intent`:

```rust
struct BlockContext {
    seconds_since_epoch: Timestamp,
    seconds_since_epoch_err: Duration,
    block_hash: Hash<Block>,
}
```

TODO: document how to derive `CallContext`

### Call well-formedness

A contract call is considered 'well-formed` with respect to a reference state
if the proof verifies against the key recorded at the location in the reference
state. The binding input for the proof is the parent intent hash.

```rust
impl ContractCall {
    fn well_formed(self, ref_state: LedgerContractState, parent_hash: IntentHash) -> Result<()> {
        let circuit = ref_state.contract.get(self.address)?.operations.get(self.entry_point)?;
        zk_verify(
            circuit,
            (
                self.guaranteed_transcript.map(|t| t.program),
                self.fallible_transcript.map(|t| t.program),
            ),
            parent_hash.into(),
            self.proof,
        )?;
    }
}
```
