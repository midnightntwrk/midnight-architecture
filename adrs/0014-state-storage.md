# 14. State Storage

## Status

accepted

| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2024-02-13                                                                                                                       |
| deciders  | Thomas Kerber, Jon Rossie |
| consulted | Alex Dalton, Giles Cope, Andrzej Kopeć, Jonathan Sobel |
---

## Context and Problem Statement

Blockchain states can be very large. This is especially true for smart-contract
based blockchains, where smart contracts can themselves occupy parts of the
state, and effectively purchase network storage space. We therefore need to
plan for states that do not fit into the RAM of our nodes.

To additionally complicate matters, we would like to preserve our use of
*persistent data structures* in the ledger and smart contracts. These data
structures allow us to perform functional updates, keeping both the current and
prior state in memory, with $O(1)$ cloning and $O(\log n)$ lookup and
modification costs. This is useful as it simplifies the ledger design into a
functional program, helping future conformance tests, and reducing the
complexity of a key part of the system.

## Decision Drivers

* Both reading from, and writing to storage should be reasonably fast, although
  throughput is not the current concern, it should be possible to improve in
  the future.
* All ledger state should use the same storage mechanism, including contract
  states, commitment trees, and nullifier sets.
* Storage should be largely transparent to the ledger.
* We want $O(1)$ cloning, and $O(\log n)$ modification costs.
* We want to be able to accurately measure the following for contract call
  costs:
  - Relative change to amount of stored state within a sub-part of the state (additions - deletions)
  - "Churn" of state within a sub-part of the state (additions + deletions)
* It should be possible in $O(\log n)$ to prove inclusion in the state.

## Considered Options

### Memory model

* Software transactional memory
* Persistent data structures
  * Off-the-shelf
  * Persistent Merkle-Patricia tries

### Disk backing

Only serious consideration has been key-value stores, with the following facets:

* Key type
  * UUID keys
  * Counter keys
  * Hash keys (content-addressed)
* Content type
  * Statically described data + references
  * Self describing data + references
  * Self describing data + references with reference count

## Decision Outcome

This ADR recommends the use of *Persistent Merkle-Patricia tries*, in a
*content-addressed data store* storing *self describing data, and references to
further data*, with a *reference counts* to track and remove unused data.

Concrete suggestions of how this can be implemented may be found under
[Hoarfrost](../apis-and-common-types/hoarfrost).

## Positive Consequences

* Existing code needs little to no modifications to work with new storage
* We retain functional handling of data, and can expose this to contract authors.

## Negative Consequences

* We cannot use an off-the-shelf solution
* We do not know the concrete performance ahead of implementation
* We use more data than necessary (256-bit hashes) for references, increasing
  storage

## Pros and Cons of the Options

### Software transactional memory

* Good, because it likely has existing implementations that can be directly
  picked up
* Bad, because it assumes memory mutation, and does not have $O(1)$ clones

### Off-the-shelf persistent data structures

* Good, because they require minimal effort to support
* Good, because they allow $O(1)$ clones, and functional style
* Bad, because there is often little view into internals to serialize these
  while remaining deduplicated
* Bad, because there is little control of internals to overlay a hash tree for
  inclusion proofs

### Persistent Merkle-Patricia tries

* Good, because they allow $O(1)$ clones, and functional style
* Good, because they allow deduplicated writing to disk
* Good, because they allow efficient inclusion proofs
* Bad, because there are no off-the-shelf implementations available

### Key types

#### UUID-keys

* Good, because they enable parallel insertions
* Bad, because insertions are non-deterministic
* Bad, because of large key size

#### Counter-keys

* Good, because of small key size
* Bad, because they prevent parallel insertions
* Bad, because an insertion run by two nodes will not have the same key
  associated, potentially introducing inconsistencies down the line.

#### Hash-keys

* Good, because they allow parallel insertions
* Good, because keys are deterministic
* Bad, because of large key size
* Neutral/good: Prevents reference loops

### Content types

#### Statically described data + references

Using type information to determine the format of the content when it is used.

* Good, because type information is available
* Good, as it saves overhead of self-described data
* Bad, as attempting to use the wrong type of data will fail with little diagnostics
* Bad, as storage layer cannot manage the structure of data by itself

#### Self described data + references

Where the content takes the form of binary data, and a list of references to
further entries. References could also be full entries, inlined, instead of a
hash, which may be cheaper in some situations.

* Good, because structure of data is visible to the data store
* Good, because accessing incorrectly structured data can give better diagnostics
* Good, because size of entries can be optimised, e.g. to fully utilise a
  random 4k read
* Bad, because of overhead of describing the entries

#### Self described data + references with reference count

As before, but with an additional reference count field which is *not* included
in the hash calculations.

* Good, for all reasons listed above
* Bad, because of overhead of describing the entries
* Good, for automatically cleaning up unused references
