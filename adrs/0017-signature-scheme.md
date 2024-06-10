# 17. Signature scheme

## Status

proposed

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2024-06-05                                                                                                                       |
| deciders  | Thomas Kerber, Iñigo Azurmendi |
| consulted | |
| informed  | Andrzej Kopec |
---

## Context and Problem Statement

Midnight requires a signature scheme for use in two contexts:
- For tracking the owner set of smart contracts, allowing owners to patch a
  contract, both for routine bugfixes, and for the contract to remain
  executable after a major proof system update.
- For the unshielded tokens due to be added.

These should use the same signature scheme.

## Decision Drivers

* Compatibility with other ecosystems
    * To what extent other ecosystems are capable of validating and interacting
      with the chosen scheme
* Hardware wallet support
    * This is weighted as an important consideration
* In-circuit efficiency
    * This is weighted as a less important consideration, as there are no
      immediate plans to verify in circuit, although it will affect the ZK
      bridge and rollup stories.
* Support for aggregation
    * In particular contract updates benefit from multi-ownership over a single
      public key.
* Maturity of implementation

## Considered Options

* Schnorr Signatures over Secp256k1
* Schnorr Signatures over Eris
* BLS Signatures over BLS12-381
* BLS Signatures over Pluto

### Signing Algorithms

#### Schnorr Signatures

Schnorr signatures are widely used in the industry, including in Bitcoin
(post-Taproot) and Ethereum, and are natively supported in Plutus over
SECP256k1 (and its Edwards variant, ed25519). We have implementations for these
signatures both in-circuit and for the native SNARK curve, as well as
SECP256k1. Schnorr signatures are well-studied, with extensive security
analysis available in academic literature.

##### Aggregation and Threshold Signatures

Aggregation techniques for Schnorr signatures exist, enabling multi-signatures
or threshold signatures. However, non-trivial constructions often require
interactive key generation (e.g., FROST) and interactive signing phases (e.g.,
MuSig/MuSig2). However, some more efficient multi-sig and threshold schemes
exist that require a different verifier than the original algorithm (e.g.,
Compact Certificates), and batch verification can significantly reduce verifier
computation through large MSMs.

##### Hardware-Wallet Support

Schnorr signatures, particularly over SECP256k1, are likely to have broad
support among hardware wallets due to their adoption in major cryptocurrencies
like Bitcoin and Ethereum. This widespread support ensures ease of integration
and a high level of security for users.

#### BLS Signatures

BLS signatures are known for their excellent aggregation properties. Given n
signatures and n public keys, verification can be simplified to checking a
single aggregated signature against an aggregated public key. This property is
beneficial for large-scale applications.

##### Complexity

BLS signatures require pairing-friendly curves (e.g., BLS12-381), making them
complex to verify in-circuit, which increases both circuit size and developer
complexity. Threshold signatures with BLS also necessitate an interactive phase
for threshold key generation.

##### Hardware-Wallet Support

BLS signatures are less commonly supported by hardware wallets compared to
Schnorr signatures, primarily due to their complexity and less widespread
adoption. This could pose challenges for user accessibility and security.

#### ECDSA vs. Schnorr

ECDSA (Elliptic Curve Digital Signature Algorithm) has been a standard in
digital signatures, used extensively in Bitcoin, Ethereum, and other blockchain
systems. However, Schnorr signatures offer several advantages over ECDSA.

* Security: Schnorr signatures are provably secure under the discrete logarithm
  assumption and do not have the same malleability issues as ECDSA.
* Efficiency: Schnorr signatures are generally more efficient than ECDSA in
  terms of both signature size and verification speed.
* Aggregation: Schnorr signatures support straightforward signature
  aggregation, which ECDSA does not natively support.

Given these advantages, Schnorr signatures are a preferred choice over ECDSA
for modern cryptographic applications, particularly in blockchain contexts
where aggregation and efficiency are critical.

#### EdDSA vs Schnorr
Ed25519 and Schnorr signatures both offer robust cryptographic solutions, with Ed25519 being a variant of the Schnorr signature scheme over the Edwards curve edwards25519. This variant is notably used in the Cardano blockchain. One significant advantage of Ed25519 is that Edwards curves support complete addition formulas, which enhances implementation efficiency and reduces the likelihood of errors. However, a notable drawback is that the curve's group order is not prime, having a cofactor that complicates protocol translation. Careful study is needed to adapt protocols, traditionally designed for prime order groups, to work with this cofactor. While Ed25519 has its advantages, the thoroughly audited and optimized implementation of secp256k1 minimizes the advantages offered by Edwards curves, particularly in contexts where the highest levels of scrutiny and optimization have already been achieved.

### Elliptic Curves and Hashing for Schnorr

#### SECP256k1 + SHA256

SECP256k1 and SHA256 are supported across multiple ecosystems (Cardano,
Bitcoin, Ethereum). These standards have been extensively vetted, ensuring high
security guarantees.

* Performance: Although SECP256k1 and SHA256 are implemented in Midnight circuits, their use in-circuit remains expensive.
* Hardware-Wallet Support: SECP256k1 is widely supported by hardware wallets
  due to its extensive use in Bitcoin and other major cryptocurrencies. This
  ensures that users will have access to secure hardware solutions for managing
  their keys and signatures, enhancing the overall security of the system.

#### Eris + Poseidon

Eris and Poseidon are used in Midnight and are efficient to implement
in-circuit, providing significant performance benefits. This efficiency makes
instantiating threshold signatures with SNARKs feasible for medium-sized
groups.

The downside is the lack of native support in other ecosystems and the
potential for future changes to the curve or hashing function, which could
necessitate transitions for existing wallets.

* Hardware-Wallet Support: Eris and Poseidon are not widely supported by
  existing hardware wallets, which may limit their adoption and ease of use.
  This could require additional development efforts to ensure hardware wallet
  compatibility, adding to the complexity and cost of implementation.

### Curves for BLS

#### BLS12-381

The BLS12-381 curve is utilized in several ecosystems (e.g., ZCash, Ethereum)
and is, or soon will be, natively supported in Plutus.

* Performance: Verifying a pairing in-circuit is highly complex, making a
  trustless bridge with these signatures challenging.
* Hardware-Wallet Support: BLS12-381 has limited support in current hardware
  wallets, primarily due to its complexity. As adoption grows, support may
  improve, but currently, this poses a challenge for secure hardware
  integration.

#### Pluto

Pluto is the native curve for SNARKs in Eris, allowing more efficient proofs.
However, in-circuit pairing remains costly, and the benefits of using this
solution are limited.

* Hardware-Wallet Support: Pluto, being less common, is unlikely to be
  supported by most hardware wallets. This lack of support could complicate
  secure key management and signature verification, making it a less attractive
  option.

## Decision Outcome

Chosen option: Schnorr Signatures over Secp256k1, following the
[BIP340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)
standard, due to strong support and standardisation.

The [`k256`](https://docs.rs/k256/latest/k256/schnorr/index.html) rust
implementation is off-the-shelf and pre-audited.

-----

While BLS signatures offer better aggregation properties, for small-sized
groups, verifying multiple Schnorr signatures is more efficient than evaluating
a pairing. With SNARKs, we can make threshold signatures more concise if
needed.

For the curve and hashing algorithm, the applied cryptography team initially
recommended Eris + Poseidon due to their superior in-circuit performance, and
out of concern for the complexity of the trustless bridge.

In discussion the support of hardware wallets were rated over these concerns.

## Validation

By review of specifications using, and PRs adding this signature scheme, and
by using existing wallet tooling for these signatures.
