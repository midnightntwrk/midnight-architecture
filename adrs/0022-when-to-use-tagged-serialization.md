# When to use tagged serialization

## Status

accepted

---
| -         | -                                                               |
|-----------|-----------------------------------------------------------------|
| date      | Oct, 2025                                                       |
| deciders  | Andrzej Kopeć, Thomas Kerber                                    |
| consulted | Agron Murtezi, Ian Gregson, Jegor Sidorenko, Heiko Seeberger, Sean Kwak, Oscar Bailey, Justin Frevert, Joe Tsang |
| informed  | - |
---

## Context and Problem Statement

Early versions of Midnight Ledger used to serialize data with a 3-byte prefix: 
1 for encoding network id, 1 for major version and 1 for minor version. This led 
to issues around storage and being able to deserialize data while preserving 
its structure for hashing purposes. Eventually Ledger implemented a serialization 
approach, which adds a unique tag to each serialized piece of data, so that it 
is possible to maintain `deserialize ○ serialize === id` property regardless 
of data evolving to support new capabilities.

While this so-called "tagged" serialization should be reached for as a default, 
there are present inconsistencies and notable exceptions that needs to be agreed 
upon and documented. The particular areas, where confusion arised is mostly 
related to JSON-based APIs and keys/address types.

<!-- This is an optional element. Feel free to remove. -->
## Decision Drivers

* Compatibility with JS bindings
* Compatibility with Compact
* Works well for Bech32m addresses and keys
* Does not prevent versioning of Bech32m addresses and keys
* Uniformity of representation in different contexts
* Overall consistency

## Considered Options

* Adopt tagged serialization uniformly across the stack
* Adopt tagged serialization in most cases, but use untagged one for wallet keys 
  and addresses
* Adopt tagged serialization in most cases, but use untagged one for wallet keys 
  and addresses, as well as couple other types, which behave like keys or addresses

## Decision Outcome

Chosen option: "Adopt tagged serialization in most cases, but use untagged one 
for wallet keys and addresses, as well as couple other types, which behave like 
keys or addresses", because it seems to be the only one meeting all the criteria 
and provides a quite clear cut of when to use tagged and when untagged format.

### Positive Consequences

* A reference for when to use the tagged or untagged serialization exists

### Negative Consequences

* It's not as clear as would be preferred. Some inconsistencies may be spotted 
  in the implementation

## Validation

After implementation, Dust and cost model are integrated across the stack without 
inconsistencies arising from the wrong serialization API usage.


## Pros, Cons and more descriptions of the Options

### Adopt tagged serialization uniformly across the stack

* Good, because it is the simplest one to remember and implement
* Bad, because it adds to much redundant information to the Bech32m keys and addresses
* Bad, because it makes ledger implementation detail part of the wallet specification

### Adopt tagged serialization in most cases, but use untagged one for wallet keys and addresses

This was the original option proposed until an inconsistency wrt. contract addresses was found.

* Good, because it is simple enough to follow
* Good, because it meets the Bech32m compatibility requirements
* Bad, because it leaves contract addresses and token types unspecified

### Adopt tagged serialization in most cases, but use untagged one for wallet keys and addresses, as well as couple other types, which behave like keys or addresses

In this option:
- for Bech32m keys and addresses use untagged serialization only
- for contract addresses and token types (which are planned to be formatted with
  Bech32m in the future too) - use untagged serialization
- for datatypes being form of hashes or identifiers (Merkle tree roots, 
  transaction identifiers) - rather use untagged serialization
- for everything else - use tagged serialization

This approach, while not being as clear cut as the other 2, seems to be the most 
consistent with Compact runtime and Ledger JS bindings. It retains the good 
compatibility with Bech32m format.  It also brings consistency around the data, 
which is likely to be displayed (iether in UI or for debugging purposes), and 
then copy-pasted to be used in some API (Node's JSON RPC, Indexer's GraphQL or in a DApp).

The reasons for such approach are:
- the Bech32 format already has equivalent to tag in the human-readable-part
- the serialization format for wallet keys and addresses is well-defined now, 
  not an implementation detail of the ledger, so any possible changes need 
  to be done in a different manner
- prepended tags add relatively lot of bulk to the addresses
- enabling versioning of addresses remains possible and relatively simple without 
  tag - shielded and unshielded addresses are constant length today, while the 
  compact Scale encoding prepends data with its length, in all cases making it 
  easy to prepend a byte for versioning purposes.
- dropping tags entirely for id-like datatypes appears to be the only really 
  consistent option; any approach where some addresses use tagged, and some 
  untagged serialization is very inconsistent and exposes part of the ledger 
  meant to be implementation detail as something that needs to be well-specified 
  (especially in case of wallet addresses)
- contract addresses and token types are used in untagged version across the 
  stack (Compact, JS bindings, etc.)
- contract addresses and token types are meant to be Bech32m encoded in the future
