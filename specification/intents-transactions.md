# Transaction and Intents

A transaction consists of a set of intents, a guaranteed Zswap offer, a
fallible Zswap offer, and binding randomness.

Intents and fallible offers carry a `segment_id: u16`. This must not be 0
(which is reserved for the guaranteed section), and groups parts that apply
atomically together.

```rust
struct Transaction<S, P> {
    intents: Map<u16, Intent<S, P>>,
    guaranteed_offer: Option<ZswapOffer<P>>,
    fallible_offer: Map<u16, ZswapOffer<P>>,
    binding_randomness: Fr,
}
```

An intent consists of guaranteed and fallible *unshielded* offers, a sequence
of calls, a set of dust payments, a TTL timestampt, and a binding commitment
with a proof of knowledge of exponent of `g`, to prevent interfering with the
Zswap value commitments.

A canonical ordering is imposed on the set of dust payments, with only this
order being considered valid. One offer, call, or dust payment must be present
for the intent to be valid.

The transaction is only valid if the TTL is a) not in the past, and b) to too
far in the future (by the ledger parameter `global_ttl`).

```rust
struct Intent<S, P> {
    guaranteed_unshielded_offer: Option<UnshieldedOffer<S>>,
    fallible_unshielded_offer: Option<UnshieldedOffer<S>>,
    calls: Vec<ContractAction<P>>,
    dust_payments: Vec<DustSpend<P>>,
    ttl: Timestamp,
    binding_commitment: FiatShamirPedersen<P>,
}
```

## Sequencing

To execute a transaction, an ordering for the component `Intent`s must first be
established. The guaranteed section always executes first, and the rest of the
transaction executes by segment ID. This has the added benefit that it prevents
malicious 'frontrunning', as a user can simply use segment ID 1 to avoid being
frontrun. This does make co-incidental merges less likely as many transactions
are likely to use the same segment IDs.

There is the additional question of how to sequence calls to the same contract
from different segments. If two segments, with IDs `a < b` are executed, and
each call the same contract `c`, how are the transcripts sequenced?

This is an issue because the contract call *may* contain both guaranteed and
fallible transcripts, but the guaranteed part of `b` must run *before* the
fallible part of `a`. This would violate an assumption that the fallible part
of `a` applies *immediately after* the guaranteed part.

To resolve this, a constraint is placed on merged transactions: If two segments
`a < b` call the same contract, then one of the following must be true:
- `a` does not have a fallible transcript for this call
- `b` does not have a guaranteed transcript for this call

For a longer sequence, this means there must be at most one segment with both a
guaranteed and fallible transcript, and any segment prior to this must have
only guaranteed transcript, and any segment after must have only fallible
transcripts.

## Replay Protection

- Use TTL for replay protection
- Zswap has it's own replay protection
- Intents are protected by keeping all intent hashes in time window of valid
  TTLs stored in state, and rejecting intents that are already present.
