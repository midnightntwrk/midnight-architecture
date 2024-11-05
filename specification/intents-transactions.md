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
- Ensure that the transaction is--custom 2560 1440 balanced

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
    fn well_formed(self, segment_id: u16, ref_state: LedgerContractState) -> Result<()> {
        let erased = self.erase_proofs();
        self.guaranteed_offer.map(|offer| offer.well_formed(erased)).transpose()?;
        self.fallible_offer.map(|offer| offer.well_formed(erased)).transpose()?;
        self.calls.iter().all(|action| action.well_formed(ref_state, hash(erased))).collect()?;
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
        // TODO
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

    fn balance(self) -> Map<(TokenType, u16), i128> {
        let mut res = Map::new();
        for (segment, intent) in self.intents {
            for (segment, offer) in [
                (0, intent.guaranteed_unshielded_offer),
                (segment, intent. fallible_unshielded_offer),
            ] {
                for inp in offer.inputs {
                    // Checked addition, fail on overflow
                    res.get_mut_or_default((TokenType::Unshielded(inp.type_), segment)) += inp.value;
                }
                for out in offer.outputs {
                    // Checked subtraction, fail on overflow
                    res.get_mut_or_default((TokenType::Unshielded(out.type_), segment)) -= out.value;
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
        res
    }

    fn balancing_check(self) -> Result<()> {
        for bal in self.balance().map(|(_, bal)| bal) {
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
        let expected = self.balance().filter_map(|((tt, segment), value)| match tt {
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
    ) -> (Self, TransactionResult) {
        if segment == 0 {
            todo!()
        } else {
            todo!()
        }
    }
}
```
