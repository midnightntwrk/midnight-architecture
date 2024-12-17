# Transaction and Intents

A transaction consists of a set of intents, a guaranteed Zswap offer, a
fallible Zswap offer, and binding randomness.

Intents and fallible offers carry a `segment_id: u16`. This must not be 0
(which is reserved for the guaranteed section), and groups parts that apply
atomically together. These are important for [sequencing](#sequencing) the
order in which parts of the transaction are applied.

```rust
struct Transaction<S, P> {
    intents: Map<u16, Intent<S, P>>,
    guaranteed_offer: Option<ZswapOffer<P>>,
    fallible_offer: Map<u16, ZswapOffer<P>>,
    binding_randomness: Fr,
}
```

An intent consists of guaranteed and fallible *unshielded* offers, a sequence
of contract actions, a set of dust payments, a TTL timestampt, and a binding commitment
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
    actions: Vec<ContractAction<P>>,
    // Dust payments will be enabled once dust tokenomics is fully settled.
    // dust_payments: Vec<DustSpend<P>>,
    ttl: Timestamp,
    binding_commitment: FiatShamirPedersen<P>,
}

type IntentHash = Hash<(u16, Intent<(), ()>)>;
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
We will refer to this relation as `a` *causally precedes* `b`.

For a longer sequence, this means there must be at most one segment with both a
guaranteed and fallible transcript, and any segment prior to this must have
only guaranteed transcript, and any segment after must have only fallible
transcripts.

Causal precedence is also extended to contract-to-contract calls within a
single intent: If `a` calls `b`, then `a` must causally precede `b`. Finally,
causal precedence is extended to be transitive: If `a` causally precedes `b`,
and `b` causally precedes `c`, then `a` must causally precede `c`. Note that
this *isn't* direct, and must be enforced.

## Replay Protection

To prevent the replay of transactions, all of the intent hashes are kept
in a history of seen intents. If an intent hash is encountered again, it is
rejected.

```rust
struct ReplayProtectionState {
    intent_history: Map<Timestamp, IntentHash>,
}

impl ReplayProtectionState {
    fn apply_intent<S, P>(mut self, intent: Intent<S, P>, tblock: Timestamp) -> Result<Self> {
        let hash = hash(intent.erase_proofs());
        assert!(!self.intent_history.contains_value(hash));
        assert!(intent.ttl >= tblock && intent.ttl <= tblock + global_ttl);
        self.intent_history = self.intent_history.insert(intent.ttl, hash);
        Ok(self)
    }

    fn apply_tx<S, P>(mut self, tx: Transaction<S, P>, tblock: Timestamp) -> Result<Self> {
        tx.intents.values().fold(|st, intent| (st?).apply_intent(intent, tblock), Ok(self))
    }

    fn post_block_update(mut self, tblock: Timestamp) -> Self {
        self.intent_history = self.intent_history.filter(|(t, _)| t > tblock + global_ttl);
        self
    }
}
```

Note that no additional replay protection is added for Zswap, as Zswap provides
its own replay protection. This comes at the cost of linear growth, which is a
known bound of the Zswap solution.

## Well-Formedness (and Balancing)

Partly, a transactions well-formedness is just the sum of its parts, however
there are additional checks to perform to ensure a holistic correctness. Those
are:

- Check that the different offers' inputs (and for Zswap, outputs) are disjoint
- Check the [sequencing restrictions](#sequencing) laid out earlier.
- TODO: Cross-check token-contract constraints, and contract call constraints
  \[all `Effects` constaints\]
  - For each contract claim in `Effects`, there is one matching call in the
    same segment, and the mapping is bidirectional
  - For each claimed nullifier in `Effects`, there is one matching nullifier in
    the same segment, and the mapping is bidirectional
  - For each claimed shielded spend in `Effects`, there is one matching coin
    commitment in the same segment, and the mapping is bidirectional
  - For each claimed shielded receive in `Effects`, there is one matching
    commitment in the same segment, and the mapping is bidirectional (but may
    overlap with the spend mapping)
  - For each unshielded spend in `Effects`, there is one matching unshielded
    UTXO output or contract input (in `Effects::unshielded_inputs`) in the same
    segment, and the mapping is bidirectional.
- Ensure that the transaction is balanced

Balancing is done on a per-segment-id basis, where segment ID `0` encompasses
the guaranteed section. Balancing also includes fee payments, which are
denominated in `DUST`. The fee payment required is subtracted from the Dust
balance of segment 0.

It's also during this time that contract interactions, both with tokens and
with other contracts are enforced. These are enforced as static 1-to-1
existence constraints, where specific interactions also mandate the existence
of another part in a contract.

```rust
impl<S, P> Intent<S, P> {
    fn well_formed(
        self,
        segment_id: u16,
        ref_state: LedgerContractState,
    ) -> Result<()> {
        let erased = self.erase_proofs();
        self.guaranteed_offer.map(|offer| offer.well_formed(erased)).transpose()?;
        self.fallible_offer.map(|offer| offer.well_formed(erased)).transpose()?;
        self.actions.iter().all(|action| action.well_formed(ref_state, hash((segment_id, erased)))).collect()?;
    }
}

const SEGMENT_GUARANTEED: u16 = 0;

impl<S, P> Transaction<S, P> {
    fn well_formed(self, tblock: Timestamp, ref_state: LedgerContractState) -> Result<()> {
        self.guaranteed_offer.map(|offer| offer.well_formed(0)).transpose()?;
        for (segment, offer) in self.fallible_offer {
            assert!(segment != SEGMENT_GUARANTEED);
            offer.well_formed(segment)?;
        }
        for (segment, intent) in self.intents {
            assert!(segment != SEGMENT_GUARANTEED);
            intent.well_formed(segment, ref_state)?;
        }
        self.disjoint_check()?;
        self.sequencing_check()?;
        self.balancing_check()?;
        self.pedersen_check()?;
        self.effects_check()?;
        self.ttl_check_weak(tblock)?;
    }
}
```

The weak TTL check simply checks if the transaction is in the expected time window:

```rust
impl<S, P> Transaction<S, P> {
    fn ttl_check_weak(self, tblock: Timestamp) -> Result<()> {
        for (_, intent) in self.intents {
            assert!(intent.ttl >= tblock && intent.ttl <= tblock + global_ttl);
        }
    }
}
```

The disjoint check ensures that no inputs or outputs in the different parts
overlap:

```rust
impl<S, P> Transaction<S, P> {
    fn disjoint_check(self) -> Result<()> {
        let mut shielded_inputs = Set::new();
        let mut shielded_outputs = Set::new();
        let mut unshielded_inputs = Set::new();
        let shielded_offers = self.guaranteed_offer.iter().chain(self.fallible_offer.values());
        for offer in shielded_offers {
            let inputs = offer.inputs.iter()
                .chain(offer.transients.iter().map(ZswapTransient::as_input))
                .collect();
            let outputs = offer.outputs.iter()
                .chain(offer.transients.iter().map(ZswapTransient::as_output))
                .collect();
            assert!(shielded_inputs.disjoint(inputs));
            assert!(shielded_outputs.disjoint(outputs));
            shielded_inputs += inputs;
            shielded_outputs += outputs;
        }
        let unshielded_offers = self.intents.values()
            .flat_map(|intent| [
                intent.guaranteed_unshielded_offer,
                intent.fallible_unshielded_offer,
            ].into_iter());
        for offer in unshielded_offers {
            assert!(unshielded_inputs.disjoint(inputs));
            unshielded_inputs += inputs;
        }
    }
}
```

The sequencing check enforces the 'causal precedence' partial order above:

```rust
impl<S, P> Transaction<S, P> {
    fn sequencing_check(self) -> Result<()> {
        // NOTE: this is implemented highly inefficiently, and should be
        // optimised for the actual implementation to run sub-quadratically.
        let mut causal_precs = Set::new();
        // Assuming in-order iteration
        for ((sid1, intent1), (sid2, intent2)) in self.intents.iter().product(self.intents.iter()) {
            if sid1 > sid2 {
                continue;
            }
            // If a calls b, a causally precedes b.
            // Also, if a contract is in two intents, the prior precedes the latter
            for ((cid1, call1), (cid2, call2)) in intent1.actions.iter()
                .filter_map(ContractAction::as_call)
                .product(intent2.actions.iter().filter_map(ContractAction::as_call))
            {
                if sid1 == sid2 && cid1 == cid2 {
                    continue;
                }
                if (sid1 == sid2 && call1.calls(call2)) || (sid1 != sid2 && call1.address == call2.address) {
                    causal_precs = causal_precs.insert(((sid1, cid1, call1), (sid2, cid2, call2)));
                }
            }
        }
        // If a calls b and c, and the sequence ID of b precedes
        // that of c, then b must precede c in the intent.
        for (_, intent) in self.intents.iter() {
            for ((cid1, call1), (cid2, call2), (cid3, call3)) in intent.actions.iter()
                .filter_map(ContractAction::as_call)
                .product(intent.actions.iter().filter_map(ContractAction::as_call))
                .product(intent.actions.iter().filter_map(ContractAction::as_call))
            {
                if let (Some((_, s1)), Some((_, s2))) = (call1.calls_with_seq(call2), call1.calls_with_seq(call3)) {
                    assert!(cid1 < cid2);
                    assert!(cid1 < cid3);
                    assert!(s1 < s2 == cid2 < cid3);
                }
            }
        }
        // If a calls `b`, `b` must be contained within the 'lifetime' of the
        // call instruction in `a`.
        // Concretely, this means that:
        // - If the call to `b` in in `a`'s guaranteed section, it *must*
        //   contain only a guaranteed section.
        // - If the call to `b` in in `a`'s fallible section, it *must*
        //   contain only a fallible section.
        for (_, intent) in self.intents.iter() {
            for ((cid1, call1), (cid2, call2)) in intent.actions.iter()
                .filter_map(ContractAction::as_call)
                .product(intent.actions.iter().filter_map(ContractAction::as_call))
            {
                if let Some((segment, _)) = call1.calls_with_seq(call2) {
                    if segment {
                        assert!(call2.fallible_transcript.is_none());
                    } else {
                        assert!(call2.guaranteed_transcript.is_none());
                    }
                }
            }
        }
        // Build transitive closure
        let mut prev = Vec::new();
        while causal_precs != prev {
            prev = causal_precs;
            for ((a, b), (c, d)) in prev.iter().zip(prev.iter()) {
                if b == c && !prev.contains((a, d)) {
                    causal_precs = causal_precs.insert((a, d));
                }
            }
        }
        // Enforce causality requirements
        for ((_, _, a), (_, _, b)) in causal_precs.iter() {
            assert!(a.fallible_transcript.is_none() || b.guaranteed_transcript.is_none());
        }
    }
}
```

The balance check depends on fee calculations (out of scope), and the overall
balance of the transaction, which is per token type, per segment ID:

```rust
impl<S, P> Transaction<S, P> {
    fn fees(self) -> Result<u128> {
        // Out of scope of this spec
    }

    fn balance(self) -> Result<Map<(TokenType, u16), i128>> {
        let mut res = Map::new();
        for (segment, intent) in self.intents {
            for (segment, offer) in [
                (0, intent.guaranteed_unshielded_offer),
                (segment, intent. fallible_unshielded_offer),
            ] {
                for inp in offer.inputs {
                    let bal = res.get_mut_or_default((TokenType::Unshielded(inp.type_), segment));
                    *bal = (*bal).checked_add(inp.value)?;
                }
                for out in offer.outputs {
                    let bal = res.get_mut_or_default((TokenType::Unshielded(out.type_), segment));
                    *bal = (*bal).checked_sub(out.value)?;
                }
            }

            for call in self.actions.iter().filter_map(|action| match action {
                ContractAction::Call(call) => Some(call),
                _ => None,
            }) {
                let effects = call.guaranteed_transcript.iter()
                    .map(|t| (0, t))
                    .chain(call.fallible_transcript.iter()
                        .map(|t| (segment, t)));
                for (segment, transcript) in transcripts {
                    for (pre_token, val) in transcript.effects.shielded_mints {
                        let tt = TokenType::Shielded(hash((transcript.address, pre_token)));
                        let bal = res.get_mut_or_default((tt, segment));
                        *bal = (*bal).checked_add(val)?;
                    }
                    for (pre_token, val) in transcript.effects.unshielded_mints {
                        let tt = TokenType::Unshielded(hash((transcript.address, pre_token)));
                        let bal = res.get_mut_or_default((tt, segment));
                        *bal = (*bal).checked_add(val)?;
                    }
                    for (tt, val) in transcript.effects.unshielded_inputs {
                        // NOTE: This is an input *to* the contract, so an
                        // output of the transaction.
                        let bal = res.get_mut_or_default((tt, segment));
                        *bal = (*bal).checked_sub(val)?;
                    }
                    for (tt, val) in transcript.effects.unshielded_outputs {
                        // NOTE: This is an output *from* the contract, so an
                        // input to the transaction.
                        let bal = res.get_mut_or_default((tt, segment));
                        *bal = (*bal).checked_add(val)?;
                    }
                }
            }
        }
        for (segment, offer) in self.fallible_offer.iter()
            .chain(self.guaranteed_offer.iter().map(|o| (0, o)))
        {
            for (tt, val) in offer.deltas {
                res.set((TokenType::Shielded(tt), segment), val);
            }
        }
        Ok(res)
    }

    fn balancing_check(self) -> Result<()> {
        for bal in self.balance()?.map(|(_, bal)| bal) {
            assert!(bal >= 0);
        }
    }
}
```

The Pedersen check ensures that the Pedersen commitments are openable to the
declared balances:

```rust
impl<S, P> Transaction<S, P> {
    fn pedersen_check(self) -> Result<()> {
        let comm_parts =
            self.intents.values()
                .map(|intent| intent.binding_commitment.commitment)
                .chain(
                    self.guaranteed_offer.iter()
                        .chain(self.fallible_offer.values())
                        .flat_map(|offer|
                            offer.inputs.iter()
                                .map(|inp| inp.value_commitment)
                                .chain(offer.outputs.iter()
                                    .map(|out| -out.value_commitment))
                                .chain(offer.transients.iter()
                                    .map(|trans| trans.value_commitment_input))
                                .chain(offer.transients.iter()
                                    .map(|trans| -trans.value_commitment_output))));
        let comm = comm_parts.fold(|a, b| a + b, embedded::CurvePoint::identity);
        let expected = self.balance()?.filter_map(|((tt, segment), value)| match tt {
            TokenType::Shielded(tt) => Some(hash_to_curve(tt, segment) * value),
            _ => None,
        }).fold(
            |a, b| a + b,
            embedded::CurvePoint::GENERATOR * self.binding_randomness,
        );
        assert!(comm == expected);
        Ok(())
    }
}
```

The effects check ensures that the requirements of each `ContractCall`s
`Effects` section are fulfilled.

```rust
impl<S, P> Transaction<S, P> {
    fn effects_check(self) -> Result<()> {
        // We have multisets for the following:
        // - Claimed nullifiers (per segment ID)
        // - Claimed contract calls (per segment ID)
        // - Claimed shielded spends (per segment ID)
        // - Claimed shielded receives (per segment ID)
        // - Claimed unshielded spends (per segment ID)

        // transcripts associate with both the their intent segment, and their
        // logical segment (0 for guarnateed transcripts), as the matching uses
        // the former for calls, and the latter for zswap.
        let calls = self.intents.iter()
            .flat_map(|(segment, intent)|
                intent.actions.iter().filter_map(|action| match action {
                    ContractAction::Call(call) => Some((segment, call)),
                    _ => None,
                }))
            .collect();
        let transcripts = calls.iter()
            .flat_map(|(segment, call)|
                call.guaranteed_transcript.iter()
                    .map(|t| (segment, 0, t))
                    .chain(call.fallible_transcript.iter()
                        .map(|t| (segment, segment, t, call.address)))))
            .collect();
        let offers = self.guaranteed_offer.iter()
            .map(|o| (0, o))
            .chain(self.fallible_offer.iter())
            .collect();
        let commitments: MultiSet<(u16, CoinCommitment, ContractAddress)> =
            offers.iter().flat_map(|(segment, offer)|
                offer.outputs.iter()
                    .filter_map(|o| o.contract.map(|addr| (o.commitment, addr)))
                    .chain(offer.transients.iter()
                        .filter_map(|t| t.contract.map(|addr| (t.commitment, addr))))
                    .map(|(com, addr)| (segment, com, addr)))
                .collect();
        let nullifiers: MultiSet<(u16, CoinNullifier, ContractAddress)> =
            offers.iter().flat_map(|(segment, offer)|
                offer.inputs.iter()
                    .flat_map(|i| i.contract.map(|addr| (i.nullifier, addr)))
                    .chain(offer.transients.iter()
                        .flat_map(|t| t.contract.map(|addr| (t.nullifier, addr))))
                    .map(|n| (segment, n)))
                .collect();
        let claimed_nullifiers: MultiSet<(u16, CoinNullifier, ContractAddress)> =
            transcripts.iter()
                .flat_map(|(_, segment, t, addr)|
                    t.effects.claimed_nullifiers.iter()
                        .map(|n| (segment, n, addr)))
                .collect();
        // All contract-associated nullifiers must be claimed by exactly one
        // instance of the same contract in the same segment.
        assert!(nullifiers == claimed_nullifiers);
        let claimed_shielded_receives: MultiSet<(u16, CoinCommitment, ContractAddress)> =
            transcripts.iter()
                .flat_map(|(_, segment, t, addr)|
                    t.effects.claimed_shielded_receives.iter()
                        .map(|c| (segment, c, addr)))
                .collect();
        // All contract-associated commitments must be claimed by exactly one
        // instance of the same contract in the same segment.
        assert!(commitments == claimed_shielded_receives);
        let claimed_shielded_spends: MultiSet<(u16, CoinCommitment)> =
            transcripts.iter()
                .flat_map(|(_, segment, t)|
                    t.effects.claimed_shielded_spends.iter()
                        .map(|c| (segment, c)))
                .collect();
        assert!(claimed_shielded_spends.iter_count().all(|(_, count)| count <= 1));
        let all_commitments: MultiSet<(u16, CoinCommitment)> =
            offers.iter().flat_map(|(segment, offer)|
                offer.outputs.iter().map(|o| o.commitment)
                    .chain(offer.transients.iter().map(|t| t.commitment))
                    .map(|c| (segment, c)))
                .collect();
        // Any claimed shielded outputs must exist, and may not be claimed by
        // another contract.
        assert!(all_commitments.has_subset(claimed_shielded_spends));
        let claimed_calls: MultiSet<(u16, (ContractAddress, Hash<Bytes>, Fr))> =
            transcripts.iter()
                .flat_map(|(segment, _, t)|
                    t.effects.claimed_contract_calls.iter()
                        .map(|c| (segment, c)))
                .collect();
        assert!(claimed_contract_calls.iter_count().all(|(_, count)| count <= 1));
        let real_calls: MultiSet<(u16, (ContractAddress, Hash<Bytes>, Fr))> =
            calls.iter().map(|(segment, call)| (
                segment,
                (
                    call.address,
                    hash(call.entry_point),
                    call.communication_commitment,
                )
            )).collect();
        // Any claimed call must also exist within the same segment
        assert!(real_calls.has_subset(claimed_contract_calls));
        let claimed_unshielded_spends: MultiSet<(
            (u16, bool),
            ((TokenType, Either<Hash<VerifyingKey>, ContractAddress>), u128)
        )> = transcripts.iter()
                .flat_map(|(intent_seg, logical_seg, t, _)|
                    t.effects.claimed_unshielded_spends.iter()
                        .map(|spend| ((intent_seg, logical_seg == 0), spend))
                .collect();
        let real_unshielded_spends: MultiSet<(
            (u16, bool),
            ((TokenType, Either<Hash<VerifyingKey>, ContractAddress>), u128)
        )> = transcripts.iter()
                .flat_map(|(intent_seg, logical_seg, t, addr)|
                    t.effects.unshielded_inputs.map(|(tt, val)|
                        (
                            (intent_seg, logical_seg == 0),
                            ((tt, Right(addr)), val),
                        )))
                .chain(self.intents.iter()
                    .flat_map(|(segment, intent)|
                        intent.guaranteed_unshielded_offer.outputs.iter()
                            .map(|o| (true, o))
                            .chain(intent.fallible_unshielded_offer.outputs.iter()
                                .map(|o| (false, o)))
                            .map(|(guaranteed, output)| (
                                (segment, guarnateed),
                                ((TokenType::Unshielded(output.type_), Left(output.owner)), output.value),
                            ))))
                .collect();
        assert!(real_unshielded_spend.has_subset(claimed_unshielded_spends));
    }
}
```

## Transaction application

Transaction application roughly follows the following procedure:
1. Apply the guaranteed section of all intents, and the guaranteed offer.
2. Check if each fallible Zswap offer is applicable in isolation. That is:
(that is: are the Merkle trees valid and the nullifiers unspent?).
3. In order of sequence IDs, apply the fallible sections of contracts, and the
   fallible offers (both Zswap and unshielded).

If any one sequence in 3. fails, this sequence, and this sequence only, is
rolled back. If any part of 1. or 2. fails, the transaction fails in its
entirety. To represent this, the transaction returns a success state which is
one of:
- `SucceedEntirely` (all passed with no failures)
- `FailEntirely` (failure in 1. or 2.)
- `SucceedPartially`, annotated with which segment IDs succeeded, and which
  failed.

```rust
enum TransactionResult {
    SucceedEntirely,
    FailEntirely,
    SucceedPartially {
        // Must include (0, true).
        segment_success: Map<u16, bool>,
    }
}

impl<S, P> Transaction<S, P> {
    fn segments(self) -> Vec<u16> {
        let mut segments = vec![0];
        let mut intent_segments = self.intents.iter().map(|(s, _)| s).peekable();
        let mut offer_segments = self.fallible_offer.iter().map(|(s, _)| s).peekable();
        loop {
            let next_intent = intents.peek();
            let next_offer = offers.peek();
            let choice = match (intents.peek(), offers.peek()) {
                (Some(i), Some(o)) => Some(i.cmp(o)),
                (Some(_), None) => Some(Ordering::Less),
                (None, Some(_)) => Some(Ordering::Greater),
                (None, None) => None,
            };
            match choice {
                Some(Ordering::Less) => segments.push_first(intents.next().unwrap()),
                Some(Ordering::Equal) => segments.push_first(intents.next().unwrap()),
                Some(Ordering::Greater) => segments.push_first(offers.next().unwrap()),
                None => break,
            }
        }
        segments
    }
}

struct LedgerState {
    utxo: UtxoState,
    zswap: ZswapState,
    contract: LedgerContractState,
    replay_protection: ReplayProtectionState,
}

impl LedgerState {
    fn apply<S, P>(
        mut self,
        tx: Transaction<S, P>,
        block_context: BlockContext,
    ) -> (Self, TransactionResult) {
        let segments = tx.segments();
        let mut segment_success = Map::new();
        let mut total_success = true;
        for segment in segments.iter() {
            match self.apply_segment(tx, segment, block_context) {
                Ok(state) => {
                    self = state;
                    segment_success = segment_success.insert(segment, true);
                }
                Err(e) => if segment == 0 {
                    return (self, TransactionResult::FailEntirely);
                } else {
                    segment_success = segment_success.insert(segment, false);
                    total_success = false;
                },
            }
        }
        (self, if total_success {
            TransactionResult::SucceedEntirely
        } else {
            TransactionResult::SucceedPartially {
                segment_success,
            }
        })
    }

    fn apply_segment<S, P>(
        mut self,
        tx: Transaction<S, P>,
        segment: u16,
        block_context: BlockContext,
    ) -> Result<Self> {
        if segment == 0 {
            // Apply replay protection
            self.replay_protection = self.replay_protection.apply_tx(
                tx,
                block_context.seconds_since_epoch,
            )?;
            if let Some(offer) = tx.guaranteed_offer {
                self.zswap = self.zswap.apply(offer)?;
            }
            // Make sure all fallible offers *can* be applied
            assert!(tx.fallible_offer.values()
                .fold(Ok(self.zswap), |st, offer| st?.apply(offer))
                .is_ok());
            // Apply all guaranteed intent parts
            for intent in tx.intents.values() {
                let erased = intent.erase_proofs();
                if let Some(offer) = intent.guaranteed_unshielded_offer {
                    self.utxo = self.utxo.apply_offer(offer, erased)?;
                }
                for action in intent.actions.iter() {
                    self.contract = self.contract.apply_action(
                        action,
                        true,
                        block_context,
                        erased,
                    )?;
                }
            }
        } else {
            if let Some(intent) = tx.intents.get(segment) {
                let erased = intent.erase_proofs();
                if let Some(offer) = intent.fallible_unshielded_offer {
                    self.utxo = self.utxo.apply_offer(offer, erased)?;
                }
                for action in intent.actions.iter() {
                    self.contract = self.contract.apply_action(
                        action,
                        false,
                        block_context,
                        erased,
                    )?;
                }
            }
            if let Some(offer) = tx.fallible_offer.get(segment) {
                self.zswap = self.zswap.apply(offer)?;
            }
        }
        Ok(self)
    }
}
```
