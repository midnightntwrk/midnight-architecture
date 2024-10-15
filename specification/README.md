# Midnight formal specification

This space is intended to formally specify formats and behaviours of Midnight.
The specification will be in literate agda, but is starting its life as rust
sketches, providing both a prose description of intention and reasoning, and a
precise and executable definition.

The specification will initially focus on specific parts of the ledger, but is
expected to expand in scope over time.

The parts of this specification are:
- [Preliminaries](./preliminaries.md), describing various preliminaries and
  primitives used in other sections.
- [Zswap](./zswap.md), describing shielded tokens on Midnight
- [Night](./night.md), describing Night and other unshielded tokens on Midnight
- [Dust](./dust.md), describing Dust payments and generation
- [Intents & Transactions](./intents-transactions.md), describing Midnight's
  composite transaction format, and intents on Midnight.

## Scratch
Should we tie UTXOs to Intent Outputs? Probably `IntentHash` and output #? -- Probably yes! But then, that will _require_ an intent to have at least one guaranteed input or dust payment? Hmm.

How about: TTL to prevent replays / ensure output uniqueness?
 > TTL isn't signed by anything for Intents with just Zswap components?
 > Could just ban empty intents? -- I think this is it. That limits danger of replays to Zswap, where they are already mitigated.

Contracts owning funds should clearly be part of transcript effects.

Identified issue: It's *technically* fine to just sign the binding commitment... However, this is bad for wallet UX, as it means you're signing opaque data. Better would be to sign the parts of a tx you care about... but this break privacy for atomic swaps.
 > Well, let's just keep it signing the commitment for zswap, but the rest of an Intent as well.
