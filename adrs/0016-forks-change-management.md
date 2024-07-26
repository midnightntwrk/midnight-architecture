# 16. Forks and change management

## Status

accepted

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                            |
|-----------|------------------------------------------------------------------------------|
| date      | Apr 26th 2024                                                                |
| deciders  | Andrzej Kopec, Thomas Kerber                                                 |
| consulted | Giles Cope, Justin Frevert, Sebastian Bach, Jonathan Sobel, Mauricio Magaldi |
| informed  |                                                                              |
---

## Context and Problem Statement

Midnight's design and capabilities, similarly to other chains, are not set in
stone. There are many known and unknown changes in the future, which will require a clear protocol, mechanism and policy for upgrades.

See [Proposal 0012 - Forks and change management](../proposals/0012-forks.md) for more details, which also describes considered options.


## Decision Drivers

* Security of the mechanics to execute upgrades
* Easiness of implementation
* Possibility to switch to a governance-based policy in the future
* Possibility to execute Snark upgrades

## Considered Options

There were a range of options considered in a different areas of Midnight. They all are mentioned in [Proposal 0012 - Forks and change management](../proposals/0012-forks.md).

The options, which took the most time to discuss were related to the mechanics of performing Midnight Ledger upgrades in Substrate node, namely:

1. To not use Substrate's runtime upgrades capability at all
2. To separate Midnight Ledger from runtime through native runtime interface (current state)
3. To make Midnight Ledger part of the runtime under upgrades

## Decision Outcome

Chosen options:

* to trigger upgrades based on seen adoption of new client versions in blocks within an epoch (similar to Bitcoin model)
* to separate Midnight Ledger from runtime through native runtime interface for the time being
* to store contract states dependent on runtime in a generalized map per runtime
* to implement facades following common mechanics for components like Indexer, Wallet or Midnight.js
because these are options, which seem to meet requirements with the least amount of new code and still offer flexibility needed.

### Positive Consequences

* There are still possibilities to explore alternative options in the future (most notably - desired integration of Midnight Ledger into the runtime or changing policy to trigger updates under vote-based governance model)
* Usage of a well-tested and well-understood mechanic, which seems to have received a range of supportive tooling in the ecosystem
* Relatively little amount of preparational work in components participating in consensus
* Clear signs on the blockchain of upcoming and in-progress updates

### Negative Consequences

* Little support from type system in ensuring and enforcing possibility of performing upgrade
* Reliance on client releases and upgrades to perform protocol upgrades
* Need to orchestrate client upgrades across block producers to perform upgrade

## Validation

Successful execution of protocol upgrades:

* without liveness issues
* with client components receiving needed updates before upgrade was performed
* without users losing tokens

## Pros and Cons of the Options

See [Proposal 0012 - Forks and change management](../proposals/0012-forks.md).
