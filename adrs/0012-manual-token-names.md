# 12. Manual token names in wallet

## Status

accepted

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                          |
|-----------|----------------------------|
| date      | Jan 12, 2024               |
| deciders  | Thomas Kerber, Andrzej Kopeć 
| consulted | Kent Dybvig                |
| informed  | Agron Murtezi     |
---

## Context and Problem Statement

Wallet and DApp users need to know exactly their balances of tokens and types of tokens being used in a transaction before it is submitted, so that they can make conscious decisions about using a DApp or allowing a DApp to create a transaction. 

## Decision Drivers

* Amount of work needed to design and implement a solution
* Needed API changes
* Possibility of end-users making wrong choice because of issues related to DApp honesty (like typosquatting or just lying in presented metadata)

## Considered Options

* On-chain metadata format
* DApp proposing token metadata upon wallet interaction
* Off-chain metadata server
* Manual setting token name in wallet

## Decision Outcome

Chosen option: "Manual setting token name in wallet", because it requires the least amount of work to implement, is not likely to cause issues relate to DApp honesty and still keeps open path to implementing one of the other options later.

### Positive Consequences

* Support for native tokens can be delivered and released quickly
* There exists a path towards a more robust option to be delivered
* There is a possibility to receive community feedback before implementing a more robust option 

### Negative Consequences

* DApp and Wallet interaction may be hindered by user's lack of clarity 
* Name is the only metadata considered at this point, DApp developers may feel limited

## More Information

 - Ethereum token standards - https://ethereum.org/en/developers/docs/standards/tokens
 - Cardano proposal - https://developers.cardano.org/docs/native-tokens/cardano-token-registry/
