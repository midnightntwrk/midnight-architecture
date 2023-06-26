$version: "2.0"

namespace midnight.ledger.state

use midnight.ledger.data#customSerialize
use midnight.ledger.data#sorted
use midnight.ledger.data#canonicalMap
use midnight.ledger.data#u64
use midnight.ledger.data#i128
use midnight.ledger.data#HashOutput
use midnight.ledger.data#MerkleTreeDigest
use midnight.ledger.data#Nullifier
use midnight.ledger.data#VerifierKey
use midnight.ledger.data#ContractAddress
use midnight.ledger.data#FieldName
use midnight.ledger.data#OperationName
use midnight.ledger.data#QueryType

/// The state of the Midnight ledger at any specific point
structure LedgerState {
  /// The zswap part of the ledger state
  @required
  zswap: ZswapChainState
  /// The state of contracts in the ledger
  @required
  contract: ContractStateMap
}

/// A map from contract addresses to a contract's state
@canonicalMap
list ContractStateMap {
  member: ContractStateMapEntry
}

/// An entry in a `ContractStateMap`.
structure ContractStateMapEntry {
  @required
  key: ContractAddress
  @required
  value: ContractState
}

/// A contract's state, and the permitted operations on it.
structure ContractState {
  /// The individual fields of the contract's current state.
  @required
  fields: ContractFieldMap
  /// The operations that can be performed against this contract, sometimes
  /// also referred to as entry points.
  @required
  operations: ContractOperationMap
}

/// A map from field names to ADT states
@canonicalMap
list ContractFieldMap {
  member: ContractFieldMapEntry
}

/// An entry in a `ContractFieldMap`.
structure ContractFieldMapEntry {
  @required
  key: FieldName
  @required
  value: AdtState
}

/// A map from operation names to the constraints of this operation.
@canonicalMap
list ContractOperationMap {
  member: ContractOperationMapEntry
}

// An entry in a `ContractOperationMap`.
structure ContractOperationMapEntry {
  @required
  key: OperationName
  @required
  value: ContractOperation
}

/// The state of an ADT in a contract's state.
union AdtState {
  /// An instance of Abcird's `Counter` ADT
  counter: i128
  /// An instance of Abcird's `Cell[T]` ADT
  cell: FabValue
  /// An instance of Abcird's `Set[T]` ADT
  set: FabSet
  /// An instance of Abcird's `Map[K, V]` ADT
  map: FabMap
  /// An instance of Abcird's `List[T]` ADT
  list: FabList
  /// An instance of Abcird's `MerkleTree[n, T]` ADT
  merkle_tree: MerkleTreeAdt
  /// An instance of Abcird's `HistoricMerkleTree[n, T]` ADT
  historic_merkle_tree: HistoricMerkleTreeAdt
}

/// A raw field-aligned binary data value.
@customSerialize
list FabValue {
  member: Blob
}

/// A set of `FabValue`s
@uniqueItems
@sorted
list FabSet {
  member: FabValue
}

/// A map from `FabValue`s to `FabValue`s.
@canonicalMap
list FabMap {
  member: FabMapEntry
}

/// An entry in a `FabMap`.
structure FabMapEntry {
  @required
  key: FabValue
  @required
  value: FabValue
}

/// A list of `FabValue`s, represented as an index to value map.
structure FabList {
  /// The length of the list
  @required
  len: u64
  /// The map of indicies to values
  @required
  values: IndexValueMap
}

/// A map from list indicies to `FabValue`s.
@canonicalMap
list IndexValueMap {
  member: IndexValueMapEntry
}

/// An entry in an `IndexValueMap`.
structure IndexValueMapEntry {
  @required
  key: u64
  @required
  value: FabValue
}

/// A Merkle tree with a pointer to the first free index.
structure MerkleTreeAdt {
  /// The underlying `MerkleTree`.
  @required
  tree: MerkleTree
  /// The first index of `tree` that is free (if in bounds).
  @required
  first_free: u64
}

/// A Merkle tree with a pointer to the first free index, and a set of past
/// Merkle roots.
structure HistoricMerkleTreeAdt {
  /// The underlying `MerkleTree`.
  @required
  tree: MerkleTree
  /// The first index of `tree` that is free (if in bounds).
  @required
  first_free: u64
  /// A set of past (and the current) Merkle roots of `tree`.
  @required
  past_roots: MerkleRootSet
}

/// A set of Merkle roots.
@uniqueItems
@sorted
list MerkleRootSet {
  member: MerkleTreeDigest
}

/// A Merkle tree, represented by its entries and the tree height.
@customSerialize
structure MerkleTree {
  /// The height of this tree.
  @required
  height: u64
  /// A map from indicies to (non-default) hashes.
  @required
  entries: MerkleTreeEntries
}

/// A Merkle tree's individual entries
@canonicalMap
list MerkleTreeEntries {
  member: MerkleTreeEntry
}

/// An entry in a `MerkleTree`.
structure MerkleTreeEntry {
  @required
  key: u64
  @required
  value: HashOutput
}

/// An operation that can be performed on a contract.
structure ContractOperation {
  /// The verifier key used to verify calls to this operation.
  vk: VerifierKey
  /// The shape that guaranteed transcripts of this operation must conform to.
  @required
  guaranteed_transcript_shape: TranscriptShape
  /// The shape that fallible transcripts of this operation must conform to.
  @required
  fallible_transcript_shape: TranscriptShape
}

/// The shape of a transcript.
list TranscriptShape {
  member: QueryType
}

/// The state of the Zswap ledger
structure ZswapChainState {
  /// The Merkle tree of coin commitments.
  @required
  coin_coms: MerkleTree
  /// The index of the first free slot in `coin_coms`.
  @required
  first_free: u64
  /// The nullifier set.
  @required
  nullifiers: NullifierSet
  /// The set of valid past roots of `coin_coms`.
  @required
  past_roots: MerkleRootSet
}

/// A set of `Nullifier`s.
@uniqueItems
@sorted
list NullifierSet {
  member: Nullifier
}
