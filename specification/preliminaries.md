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
