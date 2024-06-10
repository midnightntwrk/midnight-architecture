# 18. Contract Maintenance Authorities

## Status

proposed

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2024-06-10 |
| deciders  | Thomas Kerber, Andrezj Kopeć |
| consulted | Iñigo Azurmendi, Jon Rossie |
| informed  |                            |
---

## Context and Problem Statement

The most challenging part of a hard fork changing the proof system is how this
change affects contracts. In particular, breakage of user-deployed contracts is
inevitable, as verifier keys for a prior proof system will, in some cases, need
to be disabled.

There are other types of breakage possible, described in [an accompanying
proposal](../proposals/0014-snark-upgrade.md), however the ability to maintain
verifier keys is the primary *change* being actively proposed, and is the focus
of this document.

## Considered Options

Other options were historically considered, specifically for co, including:

* Fully relying on a Snark VM for contract upgrades, and having contract
  verifier keys be programmable by contracts themselves
* Recomputing verifier keys node-side from IR stored on-chain
* Updates to verifier keys needing to prove that new verifier keys were
  correctly computed
* A signature based update mechanism

The latter of which is the focus here.

For the Contract Maintenance Authorities, [various options were discussed in
the accompanying
proposal](../proposals/0014-snark-upgrade.md#contract-maintenance-authorities),
depending on the granularity of the authorized set:

- A simple public key signature (CMA being a public key)
- A multisignature (n/n threshold signature)
- A k/n threshold multisignature
- A stake-based threshold multisignature (allowing e.g. DAOs to be maintained
  by their participants)

## Decision Outcome

This ADR makes the decision to *implement contract maintenance authorities*,
and specifically rely on *straightforward k/n multisignatures* using the
accepted [signature scheme](./0017-signature-scheme.md). By this, it is meant
that:

- Contracts have a *maintenance authority* associated with them, which consists
  of `n` public keys, and a threshold `k <= n`.
- Instead of contract operations being a map from names to verifier keys, they
  are a map from names and major verifier key versions to verifier keys of the
  associated version.
- Contract maintenance authorities can perform two new types of transactions,
  each of which must be signed with `k` or the nominated public keys to be
  considered valid:
  - Ownership change operations, which are modifications to the set of
    maintenance public keys, or the threshold `k`, either as a full overwrite
    or as a state delta.
  - Verifier key change operations, which are modifications to the set of
    verifier keys, either as full overwrites of as a state deltas. This includes:
    - Adding new copies of verifier keys for a new major version, that may or
      may not be fully deployed at this point (for instance, the version may be
      supported, but not yet enabled for use in transactions).
    - Adding new, or modifying existing keys for an existing version.
    - Removing existing verifier keys

## Validation

Ideally, the implementation of this ADR would be validated through a full proof
system upgrade. However, given our current timelines, this seems unrealistic
prior to the intended testnet release. One of the challenges is that a good
part of the work for an update happens during the update, and not in
preparation to this, and that the preparation can be done successfully without
having carried out an update in practice.

More pragmatically therefore, we will validate with end-to-end tests that
contract maintenance authorities can perform operations as expected outside of
adding new verifier keys for new version, and leave for review and manual
inspection to convince ourselves that a new version can be added in a reliable
way in the future.
