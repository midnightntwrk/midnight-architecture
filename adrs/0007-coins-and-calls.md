# 7. Coins and calls: Allowing contracts to interact

## Status

proposed

| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2022-09-22                                                                                                                   |
| deciders  | Thomas Kerber                                                                                                                |
| consulted | Mikhail Volkhov, Amira Bouguera, Markulf Kohlweiss                                                                           |
| informed  | Joseph Denman, Kent Dybvig, Jakub Zalewski, Jon Rossie                                                                       |
---

## Context and Problem Statement

For most of its lifetime, [Lares](../components/lares/) has had the same scope
of the Kachina paper: How to define rules for a singular private smart
contract. 

Contracts are more useful when not acting in isolation however, namely when
they can be actors as well as the object of transactions. A notable special
case is contracts interacting with currency, as this is not implemented as a
contract in Midnight.

## Decision Drivers

* Contracts should be able to define their own rules.
* Contracts should be able to play according to another contract's rules.
* Contracts should be able to hold, receive, and send funds.
* Contract-held funds should be able to hide their value.
* Contracts should be partially firewalled from each other, and from funds:
  * If a contract has a bug, it should be able to cause damage an independent
    contract, or lead to the loss of more funds than were placed in it.
  * If the contract system has a bug, it should not lead to the loss of funds
    not in the contract system, or the creation of non-contract funds.

## Considered Options

There are multiple parts to this ADR with independent options.

### Native currency

* Zcash-clone (likely of Sprout or Orchard)
* ZSwap (in-house multi-currency variant of ZCash with additional benefits)

### Ledger structure

* Hashtable of contracts with (mostly) independent currency ledger
* Hashtable of contract/value pairs, with independent currency ledger for non-contract funds only
* eUTXO-based structure a la Zexe

### Interaction model

What does a contract `A` calling `B` look like?

* Circuit embedding (`A` contains `B`)
* Plaintext message passing (transaction contains `A` part which says: calls
  `B` with input `x` and output `y`, and `B` part which says: called with input
  `x`, ..., return `y`)
* Committed message passing (transaction contains `A` part which says: calls
  `B` with io `comm`, and `B` part which says: called with io `comm`; where
  `comm` is a commitment to the input `x` and result `y` computed in-circuit)

### Interaction restrictions

* Pre-defined DAG of contract calls with limited path length.
* Free-form graph
* Free-form graph, without re-entrancy

### Contract coin model

What does a contract receiving or sending funds look like?

* Implicit value attached to any call (for a fixed set of types?)
* Explicit coin objects transferred and validated

### User-defined tokens and NFTs

* Contracts able to issue coins in a color deriving from their address.

## Decision Outcome

Chosen options:

* Currency: **ZSwap**, as it was designed to suit our desire for native tokens.
* Ledger structure: **hashtable of contracts with independent currency**, as
  this best fits the combination of Kachina with ZSwap.
* Interaction model: **committed message passing**, as circuit embedding
  constrains the interactions (it forces the choice of a pre-defined DAG of
  contract calls), and does not align with our SNARK upgrade strategy.
* Interaction restrictions: **free-form graph without re-entrancy**, as
  re-entrancy is a common source of security flaws, and greatly complicates
  transaction processing from processing independent contract parts.
* Contract coin model: **explicit coin objects**, as it requires the least
  changes to Abcird, and emphasises the ACE approach.
* User defined tokens: **by contract address hash**, as this is the only clear
  option.

### Positive Consequences

* Midnight becomes an actually useful system

### Negative Consequences

* It complicates many components in subtle ways
* Decisions made here are likely to be extremely sticky

## Validation

* The ledger component will be reviewed to comply with this ADR, especially the
  [Transaction Structure
  proposal](../proposals/0005-transaction-structure-v1.md).
* The high-level language of Abcird will be reviewed to comply with this ADR.
* Integration tests of intra-contract calls and fund transfers will be
  produced.

## More Information

Please see the following accompanying proposals for how these should be implemented in more detail:
* [Transaction Structure](../proposals/0005-transaction-structure-v1.md)
* [Coins in Abcird](../proposals/0006-abcird-coins.md)
* [Contract Interfaces in Abcird](../proposals/0007-abcird-contract-interfaces.md)
* [Signatures of Knowledge in Abcird](../proposals/0008-abcird-sok.md)
