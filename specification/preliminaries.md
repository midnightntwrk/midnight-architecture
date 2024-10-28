# Preliminaries

This section includes definitions and assumptions that other sections draw
upon. It is intended less as prerequisite reading, and more as a reference to
resolve ambiguities.

## Hashing

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

## Signatures

We also need to assume public key cryptography. We use Schnorr over Secp256k1,
as specified in [BIP 340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki).

```rust
type SigningKey = secp256k1::Scalar;
type VerifyingKey = secp256k1::Point;
// Where `M` is the data being signed
type Signature<M> = secp256k1::schnorr::Signature;
```

## zk-Friendly Primitives

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

## Fiat-Shamir'd and Multi-Base Pedersen

Midnight makes heavy use of Pedersen commitments, in the embedded elliptic
curve `embedded::CurvePoint`. These are used both to ensure balancing, as
Pedersen commitments are additively homomorphic, and to ensure binding between
different transaction parts.

At its simplest, the Pedersen commitment requires to group generators `g, h:
embedded::CurvePoint`, and commits to a value `v: embedded::Scalar` with
randomness `r: embedded::Scalar`. The commitment is `c = g * r + h * v`, and is
opened by revealing `v` and `r`. Two commitments `c1` and `c2` can be added,
and opened to the sums `v1 + v2` and `r1 + r2`.

A multi-base Pedersen commitment uses a different value for `h` in different
situations. In Midnight we pick `h = hash_to_curve(coin.type, segment)`, and `v
= coin.value`, for [Zswap](./zswap.md) coins. This ensures that commitments in
different coin types and segments do not interfere with each other, as it is
cryptographically hard to find two `coin` and `segment` values that produce the
same (or a complimentary) commitment.

In Midnight, the randomness values from each Pedersen commitment are summed
across the transaction to provide binding: As only the creator of the
transaction knows the individual randomness components, it's cryptographically
hard to separate out any of the individual Pedersen commitments, ensuring that
the transaction must appear together. This binding is also used for
[`Intent`s](./intents-transactions.md), which do not carry a (Zswap) value.
Instead, we only include the randomizing portion of `g^r` for Intents.
As Intents do not carry intrinsic zero-knowledge proofs, where the shape of the
Pedersen commitment can be proven, we instead use a simple Fiat-Shamir proof to
ensure that the commitment *only* commits to a randomness value, and *not* to a
value that can be used for balancing.

We do this with a knowledge-of-exponent proof, consisting of:
- The commitment itself, `g * rc`
- A 'target' point, `g * s` for a random `s: embedded::Scalar`
- (implied) the challenge scalar `c: embedded::Scalar`, defined as the hash of:
    - The containing `Intent<(), ()>` hash
    - The commitment
    - The target point
- The 'reply' scalar `r = s - c * rc`

The Fiat-Shamir Pedersen is considered valid if `g * s == g * r + (g * rc) *
c`. Note that technically this is not a Pedersen commitment, but it is used as
a re-randomization of Pedersen commitments, so we're lumping them together.

## Time

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
