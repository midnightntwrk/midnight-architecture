$version: "2.0"

namespace midnight.ledger.data

/// A fixed-length binary blob, with the length given in bytes
@trait(selector: "blob")
structure fixedlen {
  @required
  bytes: Integer
}

/// A field element in the outer curve's scalar field
@trait(selector: "blob")
structure field {}

/// A field element in the embedded curve's scalar field
@trait(selector: "blob")
structure embeddedField {}

/// A group element in the outer curve
@trait(selector: "blob")
structure g1Element {}

/// Requires the given list to be sorted by canonical serialization.
@trait(selector: "list")
structure sorted {}

/// Requires the given list to consist of key-value pairs, be key-unique, and
/// sorted by canonical serialization.
@trait(selector: "list")
structure canonicalMap {}

/// Notes that an element will not follow standard serialization rules.
@trait(selector: "*")
structure customSerialize {}

/// For standard integer types, inteprets them as unsigned integers instead.
@trait(selector: ":is(number, [trait|midnight.ledger.data#fixedlen])")
structure unsigned {}

@unsigned
long u64
@fixedlen(bytes: 16)
blob i128
@fixedlen(bytes: 32)
blob HashOutput
@field
blob MerkleTreeDigest

@fixedlen(bytes: 32)
blob Nullifier
@fixedlen(bytes: 32)
blob CoinCommitment
@fixedlen(bytes: 32)
blob TokenType
@fixedlen(bytes: 32)
blob ContractAddress

@customSerialize
blob VerifierKey

/// The name of a state field in a contract
blob FieldName
/// The name of an operation on a contract
blob OperationName

/// The type of an individual query in a contract.
@customSerialize
blob QueryType

/// The randomness used to open a Pedersen commitment.
@field
blob PedersenRandomness
/// A Pedersen commitment
@g1Element
blob PedersenCommitment

/// A zero-knowledge proof
@customSerialize
blob Proof

/// An encrypted coin
@customSerialize
blob CoinCiphertext
