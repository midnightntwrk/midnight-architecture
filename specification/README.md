# Midnight ledger specification

This space is intended to specify formats and behaviours of Midnight, starting
with the Midnight ledger. The specification should eventually be in literate
agda, but is starting its life as rust sketches, providing both a prose
description of intention and reasoning, and a precise definition.

The specification will initially focus on specific parts of the ledger, but is
expected to expand in scope over time.

The parts of this specification are:
- [Preliminaries](./preliminaries.md), describing various preliminaries and
  primitives used in other sections.
- [Zswap](./zswap.md), describing shielded tokens on Midnight
- [Night](./night.md), describing Night and other unshielded tokens on Midnight
- [Dust](./dust.md), describing Dust payments and generation. This part of the
  spec is still in progress, although the key format may be treated as fixed.
- [Contracts](./contracts.md), abstractly describing contract states and
  interactions in transactions, without specifying the details of the structure
  of proofs and the onchain VM.
- [Intents & Transactions](./intents-transactions.md), describing Midnight's
  composite transaction format, and intents on Midnight.
- [Properties](./properties.md), describing the security and correctness
  properties of Midnight's transactions.
