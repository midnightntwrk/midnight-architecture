# Proposal 0013: Midnight HD Wallet

## Problem Statement

It is important to specify how Midnight keys and addresses can be derived in an HD (Hierarchical Deterministic) wallet setting - that is where multiple keys are deterministically derived from a single seed. This not only streamlines work of Wallet Builders in the ecosystem, but also provides reference point to allow migrations between wallet software, as well as hints, how Midnight support can be added to multi-chain wallets. While implicitly assumed, it needs to be stated explicitly, that as much as possible of existing standards like BIP-32, BIP-44, SLIP-0010, etc. should be utilized, so that amount of custom work needed by Wallet Builders is minimized.  

## Proposed Changes

At the moment of writing, there are some unknowns about tokenomics and its impact on exact key/address structure needed to follow. For that reason, there are 2 variants being proposed:
1. to follow BIP-44, with to-be specified coin type and private keys being seed to a unified key derivation for Night, Dust and other credentials
2. to follow BIP-32 key derivation, with paths similar to CIP-1852, each credential having its separate role assigned

In both cases, an ECDSA private key on secp256k1 would be used as an input to further key derivation. Generally treating keys as uniform bitstrings should not be done, though in this particular case, where secp256k1 base field is so close in size to 2^256, it is found that impact on security is negligible, which makes this approach acceptable. 

### Variant 1 - BIP-44 + all account keys derived from a single seed

This variant is expected to be adopted, if there is a cryptographic relationship needed between Night and Dust keys/addresses.

It assumes following BIP-44 to derive a private key from path of form `m / 44' / midnight_coin_type' / account' / 0 / address_index`.
Then such private key is taken as a seed to derive Midnight keys and addresses according to wallet specification.

This variant would also mean that in case of any changes, the key derivation structure needs to be adjusted to follow.

### Variant 2 - BIP-32 with CIP-1852 structure

This variant is expected to be adopted, if no direct cryptographic relationship is needed between Night and Dust keys/addresses.

It assumes following BIP-32 algorithm and CIP-1852-like derivation path, that is: `m / purpose' / midnight_coin_type' / account' / role / index`,
with possible roles being:
- `0` - Night token and unshielded native tokens, with generated private key being a private key for a Schnorr signature over secp256k1 (as specified in [ADR-0017](../adrs/0017-signature-scheme.md))
- `1` - Dust token, with generated private key being an input for Dust key derivation according to wallet specification
- `2` - zswap shielded tokens, with generated private key being an input for Dust key derivation according to wallet specification (assuming zswap and Dust can have the same key derivation scheme, only purpose being different)
- `3` - tentatively - token metadata signing, with generated private key being a private key for a Schnorr signature over secp256k1 (as specified in [ADR-0017](../adrs/0017-signature-scheme.md))

Similarly to Cardano, this variant still allows to build compound addresses, if multiple public keys are needed, though a special care should be put into assessing malleability of such addresses and possible impacts. Additionally, it is important to keep in mind that in principle keys derived for a specific role should only be used in that particular context (which is the reason for separating Dust and zswap keys into own roles, despite likely the key format and algorithms being the same, as well as having separate roles for tokens and metadata).

## More to read

- [CIP-1852](https://cips.cardano.org/cip/CIP-1852)
- [BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki)
- [BIP-44](https://github.com/bitcoin/bips/blob/master/bip-0044.mediawiki)
- [BIP-340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)

## Desired Result

One of the variants adopted and documented as part of the wallet specification, including test vectors, to let wallet builders implement Midnight support as part of HD wallet structure in confidence.
