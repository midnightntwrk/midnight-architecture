# Preliminaries

This section includes definitions and assumptions that other sections draw
upon. It is intended less as prerequisite reading, and more as a reference to
resolve ambiguities.

---

To start with, we define some basic types. Note that Midnight uses SHA-256 as
its primary hash function. To simplify in this spec, we will assume that all
data is hashable. We make the hash's output type `Hash<T>` parametric over the
input type `T`, to capture structurally which data is used to produce which
outputs. `...` signals that a part goes beyond the scope of this spec.

While this document will not go into contracts in detail, a few things are
necessary to understand:
- Contract have an address, denoted by the type `ContractAddress`, which is a
  hash of data that is beyond the scope of this document.
- Contracts may be able to issue tokens. For this, tokens have an associated
  `TokenType`. Tokens of different token types are not fungible, and token
  types are derived in one of two ways:
  - Built-in tokens, such as Night, are assigned a fixed `TokenType`.
  - User-defined tokens have a `TokenType` determined by the hash of the
    issuing contract, and a domain separator. This allows each contract to
    issue as many types of tokens as it wishes, but due to the collision
    resistance of hashes, prevents tokens from being issued by any other
    contract, or built-in tokens from being issued.

We define:

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
// Where `M` is the data being signed
type Signature<M> = secp256k1::schnorr::Signature;
```

---

Midnight makes heavy use of zero-knowledge proofs, and in some cases this means
making use of native data structures and operations that are efficient to use
in these proofs. In particular, for data types, these are:

```rust
// The type of the arithmetic circuit's modular field
type Fr;

mod embedded {
    // The type of the embedded curve's points
    type CurvePoint;
    // The type of the embedded curve's scalar field
    type Scalar;
}
```

Beyond the standard arithmetic operations on these types, we assume some
proof-system friendly hash functions, one hashing to `Fr`, and one hashing to
`embedded::CurvePoint`.

```rust
mod field {
    type Hash<T> = Fr;
    // In practice, this is Poseidon
    fn hash<T>(value: T) -> Hash<T>;
}
mod embedded {
    type Hash<T> = CurvePoint;
    fn hash<T>(value: T) -> Hash<T>;
}
```

---

We assume a notion of time, provided by consensus at a block-level. For this,
we assume a timestamp type, which corresponds to milliseconds elapsed since the
1st of January 1970, at Midnight UTC (the UNIX epoch).

```rust
type Timestamp = u64;
type Duration = u64;
```

We will occasionally refer to `now: Timestamp` as a pseudo-constant, in
practice this is the reported timestamp of the most recent block, that is
constrained by consensus to a small validity window.

We will also refer to `Timestamp::MAX` with the assumption that this time is
clearly unreachable, and assume the existence of a ledger parameter
`global_ttl: Duration` defining a global validity window for time-to-live
values, counting between `now` and `now + global_ttl`. This can be taken to be
on the order of weeks.
