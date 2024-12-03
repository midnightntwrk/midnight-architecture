# 19. User-facing keys and addresses formatting

## Status

Accepted

---
| -         | -                                                |
|-----------|--------------------------------------------------|
| date      | June 25th, 2024                                  |
| deciders  | Andrzej Kopeć, Thomas Kerber                     |
| consulted | Agron Murtezi, Enrique Rodriguez, Partner Chains |
| informed  | Lace team                                        |
---

## Context and Problem Statement

At the moment of writing, formatting addresses and user-visible keys for Midnight is not precisely defined in a form of a spec, and is prone to undetectable errors. 

## Decision Drivers

* Possibility to detect errors in user-entered credentials so typosquatting is much limited, and omission errors (common case when doing copy&paste) do not lead to loss of funds  
* Human-readable indicator of a kind of credential being used
* Ability to encode target network information in a key/address
* Ability to encode versioning information in a key/address
* Ability to support the format across Midnight stack (Midnight.js, WalletEngine, Indexer, Node) consistently

## Considered Options

* Base58Check
* Bech32m in a way similar to Zcash (dropping length requirement)
* Bech32 in a way similar to Zcash (dropping length requirement)
* Ethereum's EIP-55 encoding
* Polkadot's SS58

Full list of options learned and considered is documented at [Other chain reference](../components/WalletEngine/Other%20chain%20reference.md).

## Decision Outcome

Chosen option: "Bech32m", because Bech32 is format used by Cardano, so Cardano users are familiar with it. On top of this - Bech32m meets all requirements and many Bech32 implementations support Bech32m and customization of human-readable part.

### Positive Consequences

* An extensible and consistent formatting
* There are solid implementations available for JS (like package `@scure/base`), there seem to be good implementations available for Rust (https://crates.io/crates/bech32)
* Addresses and keys formatted this way are clearly distinguishable

### Negative Consequences

* Full support (that is for contract addresses, token types, etc.) will likely require Midnight.js or Compact runtime to support the format too   
* Full support (that is for contract addresses, token types, etc.) will likely require Midnight node to support the format too for a consistent experience

## Validation

The format is implemented and consistently present in Wallet APIs as well as relevant UIs.
As key structure evolves, accommodating for different keys and addresses does not incur much of engineering work from encoding/decoding perspective.

## Pros and Cons of the Options

Covered in [Other chain reference](../components/WalletEngine/Other%20chain%20reference.md)


## More Information

[Test vectors](../components/WalletEngine/test-vectors) contain generated addresses for various kinds of credentials and networks

 


