# 1. Public oracle language v1.0

## Status

accepted

---
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2022-09-16                                                                                                                   |
| deciders  | Thomas Kerber, Jakub Zalewski, Andrzej Kopeć, Jon Rossie                                                                     |
| consulted | Joseph Denman, Kent Dybvig, Piotr Paradzinski                                                                                |
---

## Context and Problem Statement

Following from [ADR-0005](./0005-public-oracle-language-direction.md), a
concrete language is needed that moves us from theory to practice. This
language needs to be rapidly developed for a 2022 workshop, sufficient to
express our sample dApps, and leave room for extension.

## Considered Options

Only one option has been considered, recorded in the proposal [Micro ADT
Language](../proposals/0004-micro-adt-language.md). This proposal was derived
through peer review and iteration with Andy, Jakub, Joe, and Piotr,.

## Decision Outcome

We decided to adopt the proposed micro ADT language as our initial public
oracle language.

### Positive Consequences

* We can begin implementing public oracles, and specifying their impact on various components.
* Our dApps can be written in a plausible on-chain language.

### Negative Consequences

* This proposal is being rushed through decision, and lacks viable competing options.

## Validation

The ADTs will primarily be owned by the ledger component, which shall be held
accountable for ensuring these are properly implemented through code review,
and review of the provided API by consuming components.
