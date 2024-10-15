# Transaction and Intents

A transaction consists of a set of intents, a guaranteed Zswap offer, a
fallible Zswap offer, and binding randomness.

A canonical ordering is imposed on the set of intents, with only this order
being considered valid.

```rust
struct Transaction {
    intents: Map<u16, Intent>,
    guaranteed_offer: Option<ZswapOffer>,
    fallible_offer: Map<u16, ZswapOffer>,
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
far in the future (by a ledger parameter `max_ttl`).

```rust
struct Intent<S, P> {
    guaranteed_unshielded_offer: Option<UnshieldedOffer<S>>,
    fallible_unshielded_offer: Option<UnshieldedOffer<S>>,
    calls: Vec<ContractAction<P>>,
    dust_payments: Vec<DustSpend>,
    ttl: Timestamp,
    binding_commitment: FiatShamirPedersen<P>,
}
```

An unshielded offer consists of a set of inputs and a set of outputs, where
outputs may be plain UTXOs, or UTXOs with Dust generation information.
In the latter case, the UTXO *must* have `type_` be equal to `NIGHT`.
It also contains a sequence of spend authorizing signatures.

## Replay Protection

- Use TTL for replay protection
- Zswap has it's own replay protection
- Intents are protected by keeping all intent hashes in time window of valid
  TTLs stored in state, and rejecting intents that are already present.
