# 4. Public oracle language direction

## Status

proposed

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2022-09-14                                                                                                                   |
| deciders  | Thomas Kerber, Jakub Zalewski, Jon Rossie                                                                                    |
| consulted | Joseph Denmanm, Kent Dybvig, Piotr Paradzinski, Andrzej Kopeć                                                                |
| informed  | {list everyone who is kept up-to-date on progress; and with whom there is a one-way communication}                           |
---

## Context and Problem Statement

We need a resource-bounded language for on-chain computation. This is a very
wide design space, but delivery of a MVP requires picking a direction and point
in this space. Part of this problem is problem discovery, which lead to the
recording of [five desired
properties](../proposals/0003-public-oracle-language.md#desired-properties-of-transactions) (see below).

## Decision Drivers

* The following high-level desirable properties were identified:
  1. Users should not pay for failed transactions.
  2. Transactions which cannot pay should be rejected with a low resource cost.
  3. Transactions allow expressing strong pre- and post-conditions for their effect.
  4. Transaction compression mechanisms (that is, rollups) fit well with the design.
  5. Transactions are unlikely to conflict.
* We have a constraint to get a small workable language quickly for use
  in a workshop later this year.

## Considered Options

* ["Ethereum-style" freely programamble](../proposals/0003-public-oracle-language.md#ethereum-style-freely-programmable)
* [eUTXO-style](../proposals/0003-public-oracle-language.md#eutxo-style)
* [Read-then-write ADTs](../proposals/0003-public-oracle-language.md#read-then-write-adts)
* [Maximally programmable phase-1 validation](../proposals/0003-public-oracle-language.md#maximally-programmable-v)
* [Read set](../proposals/0003-public-oracle-language.md#read-set)

## Decision Outcome

Chosen option: ADTs.

Overall, this option scored well on all criteria, while other options had
drawbacks in at least one. A few minor changes should be noted:

* While the option first discussed focuses on read operations followed by write
  operations, the focus since has been more on distinguishing *fast* and *slow*
  operations.
  * This leaves us open the option of *only* supporting *fast* operations for
    various benefits.
  * This requires shifting some responsibility to contract authors to ensure
    that slow operations succeed if their preceeding fast operations do (this
    was guaranteed in a read/write setting).
* The option discussed originally permitted arbitrary nesting of ADTs. While
  this is still a desirable goal, for version 1 we will limit ourselves to
  contracts consisting or records of ADTs.

## Validation

This ADR shall be followed up with an ADR for a concrete initial public oracle
language, which should adhere to the decision recorded here.

## Pros and Cons of the Options

See [the associated proposal](../proposals/0003-public-oracle-language.md#proposed-changes).
