# 13. Proof System Choice

## Status

accepted

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2023-12-14[^1]                                                                                                                       |
| deciders  | Thomas Kerber, Jon Rossie, Vanishree Rao                                                                                     |
| consulted | Carlos Pérez Baró, Inigo Querejeta Azurmendi |
---

## Context and Problem Statement

We need a proof system we are willing to stick with in the medium-term, to
reduce the amount of code churn, and give stability to our applied crypto
development. This proof system should be well-supported, reasonably
future-proof, performant, and provide the features we need to use it in Zswap
and Compact.

<!-- This is an optional element. Feel free to remove. -->
## Decision Drivers

* Proof verification time should be low
* Not having a trusted setup is preferred
* Not requiring proof batching for verification is preferred
* Constant-size proofs is preferred
* The proof system must have a path to recursive verification in the medium-term

## Considered Options

* ZK-Garage Plonk over BLS12-381
* Halo 2 over Pallas/Vesta with IPA
* Halo 2 over Pluto/Eris with IPA
* Halo 2 over Pluto/Eris with KZG

## Decision Outcome

Chosen option: Halo 2 over Pluto/Eris with KZG

This option was chosen because:
- KZG is more performant than IPA
- Halo 2 provides a more direct path to a recursion-ready proof system than
  our prior Plonk implementation
- Pluto/Eris, being equipped with a pairing and a cycle, benefits from both
  Halo 2's recursion strategy, and the performance uplift of KZG.
- While KZG requires a trusted setup, we believe the benefits outweigh this
  drawback.

[^1] Note that this ADR includes relatively old decisions at the point of writing.
