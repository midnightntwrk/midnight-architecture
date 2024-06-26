# 19. User-facing keys and addresses formatting

## Status

Proposed

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                |
|-----------|--------------------------------------------------|
| date      | June 25th, 2024                                  |
| deciders  | Andrzej Kopeć, Thomas Kerber                     |
| consulted | Agron Murtezi, Enrique Rodriguez, Partner Chains |
| informed  | Lace team                                        |
---

## Context and Problem Statement

At the moment of writing, formatting addresses and user-visible keys for Midnight is not precisely defined in a form of a spec, and is prone to undetectable errors. 

<!-- This is an optional element. Feel free to remove. -->
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

Full list of options learned and considered is documented at [Other chain addresses and wallets](../components/WalletEngine/Other%20chain%20addresses%20and%20wallets.odt).

## Decision Outcome

Chosen option: "Bech32m", because Bech32 is format used by Cardano, so Cardano users are familiar with it. On top of this - Bech32m meets all requirements. 

### Positive Consequences

* An extensible and consistent formatting
* There are solid implementations available for JS, there seem to be some implementations available for Rust
* Addresses and keys formatted this way are clearly distinguishable

### Negative Consequences

* Full support will likely require Midnight.js or Compact runtime to support the format too   
* Full support will likely require Midnight node to support the format too for a consistent experience

## Validation

The format is implemented and consistently present in Wallet APIs as well as relevant UIs.
As key structure evolves, accommodating for different keys and addresses does not incur much of engineering work from encoding/decoding perspective.

<!-- This is an optional element. Feel free to remove. -->
## Pros and Cons of the Options

Covered in [Other chain addresses and wallets](../components/WalletEngine/Other%20chain%20addresses%20and%20wallets.odt)


## More Information

_This section is meant to be ported to Wallet Specification and verified against Halo2 primitives_

### Human-readable part

It should consist of 3 parts, separated by underscore:
- constant `mn`
- type of credential encoded, like `addr` for payment address
- type of network (following structure already present in Ledger serialization): `undeployed`, `dev` or `test`. It is omitted for mainnet   

### Payment address

It is a concatenation of coin public key (32 bytes) and encryption public key (variable length, usually 32 bytes + versioning header).
Its credential type is `addr`

_NOTE: propose changing the encoding, so that all types of keys/addresses have defined ledger serialization which always takes only the first couple of bytes for versioning?_

Example human-readable parts:
- for mainnet: `mn_addr`
- for testnet: `mn_addr_test`
- for devnet: `mn_addr_dev`
- for local, undeployed, address: `mn_addr_undeployed`

NOTE: in current form and usage this address structure is prone to malleability, where attacker replaces coin or encryption public key in the address. It seems that Zcash was prone to this kind of malleability too in Sprout, and it was acceptable there because of assumption of addresses being securely transmitted. Implementation of diversified addresses seems to have addressed this malleability by design.

### Coin public key

Just 32 bytes of the public key.
Credential type is `cpk`.

### Encryption secret key

Ledger serialization header + contents of the secret key (which may be 32 bytes, but also may be less)
Credential type is `esk`
