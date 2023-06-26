$version: "2.0"

namespace midnight.ledger.tx

use midnight.ledger.data#sorted
use midnight.ledger.data#canonicalMap
use midnight.ledger.data#g1Element
use midnight.ledger.data#field
use midnight.ledger.data#embeddedField
use midnight.ledger.data#i128
use midnight.ledger.data#PedersenRandomness
use midnight.ledger.data#PedersenCommitment
use midnight.ledger.data#ContractAddress
use midnight.ledger.data#TokenType
use midnight.ledger.data#Proof
use midnight.ledger.data#CoinCiphertext
use midnight.ledger.data#CoinCommitment
use midnight.ledger.data#Nullifier
use midnight.ledger.data#MerkleTreeDigest
use midnight.ledger.data#HashOutput
use midnight.ledger.data#OperationName
use midnight.ledger.data#QueryType

use midnight.ledger.state#ContractState
use midnight.ledger.state#FabValue

/// A basic transaction in Midnight
structure Transaction {
  /// The guaranteed section of coins. Must cover fees for the entire
  /// transaction.
  @required
  gauranteed_coins: ZswapOffer
  /// The fallible section of coins. May be omitted.
  fallible_coins: ZswapOffer
  /// The contract calls in this transaction.
  contract_calls: ContractCalls
  /// The binding randomness cryptographically sealing this transaction
  /// together.
  @required
  binding_randomness: PedersenRandomness
}

/// A Zswap offer is a UTXO-like input/output sub-transaction
structure ZswapOffer {
  /// The shielded inputs in this offer.
  @required
  inputs: ZswapInputs
  /// The shielded outputs in this offer.
  @required
  outputs: ZswapOutputs
  /// Shielded outputs in this transaction which are also immediately used as
  /// inputs.
  @required
  transient: ZswapTransients
  /// The sum of the inputs minus outputs per `TokenType`.
  @required
  deltas: ZswapDeltas
}

/// A set of inputs.
@uniqueItems
@sorted
list ZswapInputs {
  member: ZswapInput
}

/// A single shielded transaction input.
structure ZswapInput {
  /// The nullifier marking this input as spent.
  @required
  nullifier: Nullifier
  /// The homomorphic commitment to the type/value of this input.
  @required
  value_commitment: PedersenCommitment
  /// The contract address of this input, if contract-owned.
  contract_address: ContractAddress
  /// The root of the Merkle tree this input spends from.
  @required
  merkle_tree_root: MerkleTreeDigest
  /// The zero-knowledge proof demonstrating correctness, and eligibility to
  /// spend.
  @required
  proof: Proof
}

/// A set of outputs.
@uniqueItems
@sorted
list ZswapOutputs {
  member: ZswapOutput
}

/// A single shielded transaction output.
structure ZswapOutput {
  /// The coin commitment created in this output.
  @required
  coin_com: CoinCommitment
  /// The homomorphic commitment to the type/value of this output.
  @required
  value_commitment: PedersenCommitment
  /// The contract address of this output, if contract-owned.
  contract_address: ContractAddress
  /// The ciphertext attached to this output, if sending to another user.
  ciphertext: CoinCiphertext
  /// The zero-knowledge proof demonstrating correctness.
  @required
  proof: Proof
}

/// A set of transient outputs.
@uniqueItems
@sorted
list ZswapTransients {
  member: ZswapTransient
}

/// An output that is immediately spent within the same transaction.
structure ZswapTransient {
  /// The nullifier marking this coin as spent.
  @required
  nullifier: Nullifier
  /// The coin commitment created while outputting this transient.
  @required
  coin_com: CoinCommitment
  /// The homomorphic commitment to the type/value of the input form of this
  /// transient.
  @required
  value_commitment_input: PedersenCommitment
  /// The homomorphic commitment to the type/value of the output form of this
  /// transient.
  @required
  value_commitment_output: PedersenCommitment
  /// The contract address of this transient, if contract-owned.
  contract_address: ContractAddress
  /// The ciphertext attached to the output form of this transient.
  ciphertext: CoinCiphertext
  /// The proof of correctness and eligibility to spend of the input form of
  /// this transient.
  @required
  proof_input: Proof
  /// The proof of correctness of the output form of this transient.
  @required
  proof_output: Proof
}

/// A map from `TokenType`s to the surplus of inputs (or deficit if negative)
/// in a given offer of this type.
@canonicalMap
list ZswapDeltas {
  member: ZswapDeltasEntry
}

/// Marks an integer as not being zero.
@trait(selector: "*")
structure nonZero {}

/// An entry in a `ZswapDeltas` map.
structure ZswapDeltasEntry {
  @required
  key: TokenType
  @required
  @nonZero
  value: i128
}

/// A sequence of contract calls within a transaction.
structure ContractCalls {
  /// The list of calls.
  @required
  calls: ContractCallList
  /// The binding commitment sealing this list cryptographically.
  @required
  binding_commitment: FiatShamirPedersen
}

/// A Fiat-Shamir challenge in the proof of knowledge of exponent.
@g1Element
blob FiatShamirTarget

/// A Fiat-Shamir response in the proof of knowledge of exponent.
@embeddedField
blob FiatShamirResponse

/// A Fiat-Shamir transformed Pedersen commitment, ensuring that only the
/// generator is used in the commitment.
structure FiatShamirPedersen {
  /// The underlying commitment.
  @required
  commitment: PedersenCommitment
  /// The Fiat-Shamir challenge.
  @required
  target: FiatShamirTarget
  /// The Fiat-Shamir response.
  @required
  response: FiatShamirResponse
}

/// A list of basic contract calls.
list ContractCallList {
  member: CallOrDeploy
}

/// A contract call or deployment.
union CallOrDeploy {
  /// A basic contract call.
  call: ContractCall
  /// A contract deployment.
  deploy: ContractDeploy
}

/// This action deploys a new contract on-chain.
structure ContractDeploy {
  /// The initial state of the contract to deploy.
  @required
  initial_state: ContractState
  /// A arbitrary nonce, allowing the same contract to be deployed multiple
  /// times.
  @required
  nonce: HashOutput
}

/// A call to a specific operation on a specific contract.
structure ContractCall {
  /// The address of the contract being called.
  @required
  address: ContractAddress
  /// The operation on the contract being called.
  @required
  entry_point: OperationName
  /// The guaranteed section of the public transcript.
  @required
  guaranteed_transcript: Transcript
  /// The fallible section of the public transcript.
  @required
  fallible_transcript: Transcript
  /// The communication commitment, for use in linking parent and child calls.
  @required
  communication_commitment: CommunicationCommitment
  /// The zero-knowledge proof demonstrating correctness of the above.
  @required
  proof: Proof
}

/// A commitment to the secret inputs and outputs of a given call.
@field
blob CommunicationCommitment

/// A public transcript is a sequence of public operations.
@sparse
list Transcript {
  member: TranscriptEntry
}

/// A transcript entry is an on-chain execution operation.
structure TranscriptEntry {
  /// The specific type of this query.
  @required
  type: QueryType
  /// The arguments to this query.
  @required
  args: FabValue
  /// The recorded result of the query.
  @required
  result: FabValue
}
