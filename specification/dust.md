# Dust and fee payments

> [!WARNING]
> This section is under construction.

### EDITS TO MAKE

- Dust should no longer be allowed to go negative, cooldown should not exist.
- Instead, it should be possible to back-date dust generation if none existed
  for that Night UTXO previously, and pay for the back-dating transaction with
  the Dust resulting.
- We want a linkage map between Night addresses and Dust addresses, which sets
  the dust output for any subsequent night sent. Note that the dust back-dating
  is by necessity a different mechanism.
- We should be explicit about cNIGHT interaction. Talk about/link to how we're
  genenerating dust from them, extend the night document with locking/unlocking
  discussions.
- Explicitly commit to linear curve right now, and comment on potential for
  other curves in future.

### Up-to-date code spec

```rust
type DustSecretKey = Fr;
type DustPublicKey = field::Hash<DustSecretKey>;

type InitialNonce = Hash<(IntentHash, u32)>;

struct DustOutput {
    value: u128,
    owner: DustPublicKey,
    nonce: field::Hash<(InitialNonce, u32, Fr)>,
    seq: u32,
    ctime: Timestamp,
}

struct DustGenerationInfo {
    value: u128,
    owner: DustPublicKey,
    nonce: InitialNonce,
    dtime: Timestamp,
}

struct DustGenerationUniquenessInfo {
    value: u128,
    owner: DustPublicKey,
    nonce: InitialNonce,
}

struct DustGenerationState {
    address_delegation: Map<NightAddress, DustPublicKey>,
    generating_tree: MerkleTree<DustGenerationInfo>,
    generating_tree_first_free: usize,
    generating_set: Set<DustGenerationUniquenessInfo>,
    night_indices: Map<Utxo, u64>,
    root_history: TimeFilterMap<MerkleTreeRoot>,
}

struct DustPreProjection<T> {
    value: u128,
    owner: T,
    nonce: field::Hash<(InitialNonce, u32, Fr)>,
    ctime: Timestamp,
}

type DustCommitment = field::Hash<DustPreProjection<DustPublicKey>>;
type DustNullifier = field::Hash<DustPreProjection<DustSecretKey>>;

struct DustParameters {
    /// The ratio between atomic NIGHT units (STARs), and atomic DUST units (SPECKs)
    /// at their cap
    /// Note that 1 NIGHT = 10^6 STARs, 1 DUST = 10^15 SPECKs
    night_dust_ratio: u64,
    /// The number amount of MOTES per SPEC per second to generate or decay.
    generation_decay_rate: u32,
    /// The amount of time that may pass before a DUST spend is forced to time out.
    dust_grace_period: Duration,
}

const INITIAL_DUST_PARAMETERS: DustParameters = {
    night_dust_ratio = 5_000_000_000; // 5 DUST per NIGHT
    generation_rate = 8_267; // Works out to a generation time of approximately 1 week.
    dust_grace_period = Duration::from_hours(3),
};

fn updated_value(inp: DustOutput, gen: DustGenerationInfo, now: Timestamp, params: DustParameters) -> u128 {
    // There are up to four linear segments:
    // 1. Generating (from inp.ctime to tfull, the time dust fills to the cap)
    // 2. Constant full (from tfull to gen.dtime)
    // 3. Decaying (from gen.dtime to tempty, the time dust reaches zero)
    // 4. Constant empty (from tempty onwards)
    // 
    // If gen.dtime <= tfull, phase 3. doesn't occur, and if gen.dtime <=
    // inp.ctime Phase 1 doesn't occur.
    //
    // We assume that the full value is gen.value * night_dust_ratio, and that
    // the time to fill is dust_ttl
    let vfull = gen.value * params.night_dust_ratio;
    // Note that `night_dust_ratio / time_to_gen` can be an input, not
    // requiring division in-circuit.
    let rate = gen.value * generation_decay_rate;
    // Note that we aren't constraining the end to be after the start, instead
    // we're clamping the output to the reasonable region of outputs.
    let tstart_phase_1 = inp.ctime;
    let tend_phase_1 = min(gen.dtime, now);
    let value_phase_1_unchecked = (tend_phase_1 - tstart_phase_1).as_seconds() * rate + inp.value;
    let value_phase_1 = clamp(value_phase_1_unchecked, inp.value, vfull);
    // Again, we aren't constraining the end to be after the start, instead
    // we're clamping the output to the reasonable region of outputs.
    let tstart_phase_3 = gen.dtime;
    let tend_phase_3 = now;
    let value_phase_3_unchecked = value_phase_1 - (tend_phase_3 - tstart_phase_3).as_seconds() * rate;
    let value_phase_3 = clamp(value_phase_3_unchecked, 0, value_phase_1);
    value_phase_3
}

struct DustUtxoState {
    commitments: MerkleTree<DustCommitment>,
    commitments_first_free: usize,
    nullifiers: Set<DustNullifier>,
    root_history: TimeFilterMap<MerkleTreeRoot>,
}

struct DustState {
    utxo: DustUtxoState,
    generation: DustGenerationState,
    params: DustParameters,
}

struct DustSpend<P> {
    v_fee: u128,
    nullifier: DustNullifier,
    commitment: DustCommitment,
    proof: P::Proof,
}

fn dust_spend_valid(
    dust_spend: Public<DustSpend<()>>,
    tnow: Public<Timestamp>,
    params: Public<DustParameters>,
    commitment_root: Public<MerkleTreeRoot>,
    generation_root: Public<MerkleTreeRoot>,
    dust: Private<DustOutput>,
    sk: Private<DustSecretKey>,
    gen: Private<DustGenerationInfo>,
    commitment_merkle_tree: Private<MerkleTree<DustCommitment>>,
    generation_merkle_tree: Private<MerkleTree<DustGenerationInfo>>,
    // Note these are for the new coin, and there is no need to validate these,
    // as the secret key ensures these are provided by the same user as consumes
    // them.
    initial_nonce: Private<InitialNonce>,
    seq_no: Private<u32>,
) -> bool {
    assert!(dust.owner == field::hash(sk));
    let pre_commitment = field::hash(DustPreProjection {
        value: dust.value,
        owner: dust.owner,
        nonce: dust.nonce,
        ctime: dust.ctime,
    });
    assert!(commitment_merkle_tree.contains(pre_commitment));
    assert!(commitment_root = commitment_merkle_tree.root());
    assert!(generation_merkle_tree.contains(gen));
    assert!(genration_root = generation_merkle_tree.root());
    let nullifier = field::hash(DustPreProjection {
        value: dust.value,
        owner: sk,
        nonce: dust.nonce,
        ctime: dust.ctime,
    });
    assert!(dust_spend.nullifier == nullifier);
    let v_pre = updated_value(inp, gen, tnow, params);
    assert!(dust_spend.v_fee >= v_pre);
    let v = v_pre - dust_spend.v_fee;
    let nonce = field::hash((initial_nonce, seq_no, sk));
    let post_commitment = field::hash(DustPreProjection {
        value: v,
        owner: dust.owner,
        nonce,
        ctime: tnow,
    });
    assert!(dust_spend.commitment == post_commitment);
}

impl<P> DustSpend<P> {
    fn well_formed(self, ref_state: DustState, segment: u16, binding: Pedersen, tparent: Timestamp) -> Result<()> {
        assert!(zk_verify(
            dust_spend_valid,
            (
                self,
                tparent,
                ref_state.parameters,
                ref_state.utxo.root_history.get(tparent),
                ref_state.generation.root_history.get(tparent),
            ),
            Some((segment, binding)),
            self.proof,
        ));
    }
}

struct DustRegistration<S> {
    night_key: VerifyingKey,
    dust_address: Option<DustPublicKey>,
    /// The amount of fees from owed DUST that this registration will cede to
    /// fee payments. This *must* be an underestimate of the fees available.
    allow_fee_payment: u128,
    Signature,
}

struct DustActions<S, P> {
    spends: Vec<DustSpend<P>>,
    /// Note that registrations *may* count towards the transaction dust
    /// balance, iff the registered night address has both inputs and outputs
    /// in this transaction, and the inputs were not already generating dust.
    ///
    /// Then:
    /// - The total DUST owed to all non-generating inputs of this address is
    ///   computed as `dust_in`
    /// - The fee still owed in the transaction `fee_remaining` is mutably
    ///   processed by:
    ///   - Seetting the amount paid `fee_paid := min(fee_remaining, allow_fee_payment, dust_in)`
    ///   - Setting `fee_remaining := fee_remaining - fee_paid`
    /// - The remaining `dust_out := dust_in - fee_paid` DUST is distributed to
    ///   the output UTXOs for the same owner in proportion to their balance
    ///   (rounded down).
    ///
    /// Note that this overrides the typical output processing, to avoid the
    /// outputs here having two corresponding DUST UTXOs.
    ///
    /// Further note that it *only* happens to the guaranteed unshielded offer,
    /// and the fallible offer is processed normally.
    registrations: Vec<DustRegistration>,
    ctime: Tiemstamp,
}

impl<S, P> DustActions<S, P> {
    fn well_formed(self, ref_state: DustState, segment: u16, parent: ErasedIntent, tnow: Timestamp) -> Result<()> {
        let binding = parent.binding_commitment;
        assert!(!self.spends.is_empty() || !self.registrations.is_empty())
        for spend in self.spends {
            spend.well_formed(ref_state, segment, binding, self.ctime)?;
        }
        assert!(self.ctime <= tnow && self.ctime + params.dust_grace_period >= tnow);
        // FIXME: Need to make sure that the declared possible dust
        // registrations are actually possible
    }
}

impl DustState {
    fn apply<S, P>(
        mut self,
        actions: DustActions<S, P>,
        remaining_fees: u128,
        segment: u16,
        parent_intent: ErasedIntent,
        utxo_state: UtxoState,
        params: DustParameters,
    ) -> Result<(Self, u128)> {
        for spend in self.spends {
            self = self.apply_spend(spend)?;
        }
        for reg in self.registrations {
            (self, remaining_fees) = self.apply_registration(
                utxo_state,
                remaining_fees,
                segment,
                parent_intent,
                reg,
                params,
            )?;
        }
        Ok((self, remaining_fees))
    }

    fn apply_offer<S, P>(
        mut self,
        offer: UnshieldedOffer<S>,
        segment: u16,
        guaranteed: bool,
        parent: ErasedIntent,
        tnow: Timestamp,
    ) -> Result<Self> {
        for input in offer.inputs.filter(|i| i.type_ == NIGHT_RAW) {
            let Some(idx) = self.generation.night_indices.get(Utxo::from(input)) else { continue; };
            let mut gen_info = self.generation.generating_tree
                .get(idx)
                .expect("Invalid index should not be in night indices");
            gen_info.dtime = tnow;
            self.generation.generating_tree = self.generation.generating_tree.insert(idx, gen_info);
        }
        for (output_no, output) in offer.outputs
            .iter()
            .enumerate()
            .filter(|(_, o)| o.type_ == NIGHT_RAW)
        {
            let Some(dust_addr) = self.generation.address_delegation.get(output.owner) else { continue; };
            let handled_by_registration = guaranteed && parent.dust_actions
                .iter()
                .flat_map(|actions| actions.registrations.iter())
                .any(|reg| hash(reg.night_key) == output.owner);
            if handled_by_registration {
                continue;
            }
            let initial_nonce = hash(hash(segment, parent), output_no as u32);
            let seq = 0;
            let dust_pre_projection = DustPreProjection {
                value: 0,
                owner: dust_addr,
                nonce: field::hash((initial_nonce, seq, dust_addr)),
                ctime: tnow,
            };
            let dust_commitment = field::hash(dust_pre_projection);
            self.utxo.commitments = self.utxo.commitments.insert(
                self.utxo.commitments_first_free,
                dust_commitment,
            );
            self.utxo.commitments_first_free += 1;
            let gen_info = DustGenerationInfo {
                value: output.value,
                owner: dust_addr,
                nonce: initial_nonce,
                dtime: Timestamp::MAX,
            };
            let utxo = Utxo {
                value: output.value,
                owner: output.owner,
                type_: output.type_,
                intent_hash: hash(segment, parent),
                output_no,
            };
            assert!(!self.generation.generating_set.contains(gen_info.into()));
            self.generation.generating_set = self.generation.generating_set.insert(gen_info.into());
            self.generation.generating_tree = self.generation.generating_tree.insert(self.generation.generating_tree_first_free, gen_info);
            self.generation.night_indices.insert(utxo, self.generation.generating_tree_first_free);
            self.generation.generating_tree_first_free += 1;
        }
        self
    }

    fn apply_spend<P>(mut self, spend: DustSpend<P>) -> Result<Self> {
        assert!(!self.utxos.nullifiers.contains(spend.nullifier));
        self.utxo.nullifiers = self.utxo.nullifiers.insert(spend.nullifier);
        self.utxo.commitments = self.utxo.commitments.insert(self.utxo.commitments_first_free, spend.commitment);
        self.utxo.commitments_first_free += 1;
        Ok(self)
    }

    // Returns the updated self, and the updated `remaining_fees`.
    fn apply_registration<S>(
        mut self,
        utxo_state: UtxoState,
        mut remaining_fees: u128,
        segment: u16,
        parent_intent: ErasedIntent,
        reg: DustRegistration<S>,
        params: DustParameters,
    ) -> Result<(Self, u128)> {
        let night_address = hash(self.night_key);
        match reg.dust_address {
            None => {
                let entry = self.generation.address_delegation.remove(night_address);
                assert!(entry.is_some());
            },
            Some(dust_addr) => self.generation.address_delegation.insert(night_address, dust_addr),
        }
        let generationless_inputs = parent_intent.guaranteed_unshielded_offer
            .iter()
            .flat_map(|o| o.inputs.iter())
            .filter(|i| i.owner == self.night_key && i.type_ == NIGHT_RAW)
            .filter(|i| !self.generation.night_indices.contains(Utxo::from(i)))
            .collect();
        let owned_outputs = parent_intent.guaranteed_unshielded_offer
            .iter()
            .flat_map(|o| o.outputs.iter().enumerate())
            .filter(|(_, o)| o.owner == night_address && o.type_ == NIGHT_RAW)
            .collect();
        let dust_in = generationless_inputs.iter().map(|i| {
            // In parallel with `updated_value`, but only phase 1
            let vfull = i.value * params.night_dust_ratio;
            let rate = i.value * generation_decay_rate;
            let tstart = utxo_state.get(Utxo::from(i))?.ctime;
            let tend = parent_intent.dust_actions
                .expect("Dust actions must exist to process a registration")
                .ctime;
            let value_unchecked = (tend_phase_1 - tstart_phase_1).as_seconds() * rate;
            clamp(value_unchecked, 0, vfull)
        }).sum();
        let fee_paid = u128::min(remaining_fees, u128::min(reg.allow_fee_payment, dust_in));
        remaining_fees -= fee_paid;
        let dust_out = dust_in - fee_paid;
        if let Some(dust_addr) = reg.dust_address {
            let output_sum = owned_outputs.iter().map(|o| o.value).sum();
            for (output_no, output) in owned_outputs {
                // NOTE: The ratio calculation could overflow even u128. As a
                // result, we quantize it.
                const DISTRIBUTION_RESOLUTION: u128 = 10_000;
                let ratio = ((output.value * DISTRIBUTION_RESOLUTION) / output_sum);
                let initial_value = (ratio * dust_out) / DISTRIBUTION_RESOLUTION;
                // NOTE: This is identical to `apply_offer`. Factor out?
                let initial_nonce = hash(hash(segment, parent), output_no as u32);
                let seq = 0;
                let dust_pre_projection = DustPreProjection {
                    value: initial_value,
                    owner: dust_addr,
                    nonce: field::hash((initial_nonce, seq, dust_addr)),
                    ctime: tnow,
                };
                let dust_commitment = field::hash(dust_pre_projection);
                self.utxo.commitments = self.utxo.commitments.insert(
                    self.utxo.commitments_first_free,
                    dust_commitment,
                );
                self.utxo.commitments_first_free += 1;
                let gen_info = DustGenerationInfo {
                    value: output.value,
                    owner: dust_addr,
                    nonce: initial_nonce,
                    dtime: Timestamp::MAX,
                };
                let utxo = Utxo {
                    value: output.value,
                    owner: output.owner,
                    type_: output.type_,
                    intent_hash: hash(segment, parent),
                    output_no,
                };
                assert!(!self.generation.generating_set.contains(gen_info.into()));
                self.generation.generating_set = self.generation.generating_set.insert(gen_info.into());
                self.generation.generating_tree = self.generation.generating_tree.insert(self.generation.generating_tree_first_free, gen_info);
                self.generation.night_indices.insert(utxo, self.generation.generating_tree_first_free);
                self.generation.generating_tree_first_free += 1;
            }
        }
        Ok((self, remaining_fees))
    }

    // Need to process night inputs and outputs. Where to put the linking operation?
    // The link needs to be signed by the relevant night addr, but doesn't
    // make sense as an input. A separate field, or extending ContractAction?
    // The latter would question why this isn't used more for unshielded tokens
    // though.

    // Let's just have it be a separate signed action, part of the dust
    // payments segment.

    fn post_block_update(mut self, tblock: Timestamp) -> Self {
        self.utxo.root_history = self.utxo.root_history.insert(
            tblock,
            self.utxo.commitments.root(),
        ).filter(tblock - global_ttl);
        self.generation.root_history = self.generation.root_history.insert(
            tblock,
            self.generation.generating_tree.root(),
        ).filter(tblock - global_ttl);
        self
    }
}
```

### Old prose to rewrite or recycle

# Dust and fee payments

> Midnight's fees are payed with the *Dust* token. This token is generated over
> time by Night, but also decays over time to compensate. Dust is unique in the
> Midnight system, and is not transferable.
> 
> Dust is designed to be *resettable*. That is, the entire Dust subsystem state
> can be deleted without significant impact on users. Note that some impact is
> likely unavoidable, but this is considered an acceptable cost.
> 
> Due to this, Dust makes heavy use of SNARK friendly cryptography;
> Dust public keys are a (snark-friendly) hash of dust secret keys:


> A dust output consists of its value, owner, nonce, and creation time. Note
> that, unusually, negative values *are permitted* here. This is used to allow
> redirection of dust generation for free, by effectively incurring a debt. In
> all other cases, created outputs must have a positive value.

> The nonce is defined as `nonce = field::hash((initial_nonce, n, key))`, `initial_nonce = hash(night_utxo.intent_hash, night_utxo.output_no)` where `night_utxo` is the corresponding Night
> UTXO that created this Dust output, and `n` is the sequence number `seq` in
> this Dust evolution (0 at the initial creation), and `key` is the owner's
> public key if `n = 0`, and the owner's *secret* key otherwise. This ensures
> that the `DustOutput` is publicly computable if and only if it is the initially
> created one, and is only computable by the owner otherwise.

### Dust generation

> In addition to dust outputs, dust generation information is needed to compute
> the balance of the dust output at the time it is spent. This consists of a
> Merkle tree with leaves containing the (Dust) owner of a UTXO, the *initial*
> (Night) nonce, the value of corresponding Night UTXO, and the time the Night
> UTXO was spent. The final value is set to `Timestamp::MAX` if it *has not yet
> been spent*.

> Additionally, a set of `(value, owner, nonce)` tuples is maintained, to prevent
> creation of multiple outputs with the same nonce, which could constitute a
> faerie-gold-like attack.

```rust
```

> `historic_roots` tracks past versions of `generating_tree` that are still permitted
> to prove against. This is regularly filtered, so only the most recent roots are
> valid, within a validity window `dust_validity`. `night_indices` tracks the
> position of each Night utxo in the `generating_tree`, allowing these to be
> updated with the correct `dtime` when the corresponding Night utxo is spent.

### Spending Dust

> Dust will follow Zerocash commitment/nullifier structure. Each `DustOutput` has
> two projections, a `DustNullifier` and a `DustCommitment`, both produced using
> the `field::hash`. The nullifier set is a set of the former, and the commitment set
> a Merkle tree of the latter. As the dust *generation* set has faerie-gold
> attack mitigation, no mitigation is needed for Dust itself.

> A Dust transaction will always be a 1-to-1 transfer, consuming one `DustOutput`
> and producing another. The transaction must be associated with a time `t`, and
> output a public fee payment `v_fee`. The input `inp: DustOutput`'s value must
> be recomputed for time `t`, and the associated `gen: DustGenerationInfo`. The
> function to compute this will be discussed separately, and is assumed here,
> it's result is `v_in: i128`.
> 
> The output `out: DustOutput` is defined as (where the output `value` *must* be
> non-negative):

> ```rust
> out = DustOutput {
>     value: updated_value(inp, gen) - v_fee,
>     owner: inp.owner,
>     nonce: transient_hash(gen.nonce, inp.seq + 1, dust_sk),
>     seq: inp.seq + 1,
>     ctime: t,
> }
> ```

> The public state of Dust is simply a commitment Merkle tree, a nullifier set,
> and the historic roots & first f(Note that this needs to be tracked
> separately, as in our implementation the tree itself has no policy on order of
> insertions for flexibility. In practice we insert in order). To simplify the
> fee payment transaction
> fragment, the timestamps used in the Dust historic roots, and the generation
> historic roots should be the same.

> A Dust payment then consists of:
> - Some data to sign over
> - A timestamp `t`
> - A value `v_fee`
> - A Dust nullifier (for the spent Dust)
> - A Dust commitment (for the new Dust output)
> - A ZK proof (more on that below)

> When applying this, the proof is checked against `transient_hash(sign_over)`,
> `t`, `dust_root = <dust state>.historic_roots[t]`, `gen_root = <gen
> state>.historic_roots[t]`, `v_fee`, `nullifier`, and `commitment`. *Private*
> inputs to the proof are:
> 
> - The secret key `sk`
> - The input `inp: DustOutput` and its Merkle path `inp_path`
> - The relevant `gen: DustGenerationInfo`, and its Merkle path `gen_path`
> 
> Then the proof asserts that:
> - `gen` is under `gen_root` at `gen_path`
> - `inp` is under `inp_root` at `inp_path`
> - `inp`'s nullifier is `nullifier`
> - `out` is computed as above
> - `out`'s commitment is `commitment`
> 
> When applying, the nullifier is inserted into `<dust state>.nullifiers`, with a
> transaction failure if it already exists.

> ### Spending Night
> 
> The spending of Night should affect the `DustGenerationState`. This requires a
> change to the semantics of UTXO outputs, and a change to the transaction, as
> this must nominate an output `DustPublicKey`. Night transfers should still be
> able to operate solely on Night addresses, which implies that even regular Dust
> transfers need to de-register any generation from spent UTXOs.

>> FIXME: This is not longer correct.

> ```rust
> struct GeneratingUtxoOutput {
>     regular: UtxoOutput,
>     generation_owner: DustPublicKey,
> }
> ```
> 
> This can be used over `UtxoOutput` to also update `DustGenerationState`, by
> inserting a new generation information corresponding to the new UTXO output.
> Finally, any spend where `type_ == NIGHT` should try to update the
> `DustGenerationState` to set the `dtime` of any corresponding generation
> information (if this does not exist, this is a no-op).
> 
> In order to permit Night to be transferable *without* having Dust, a basic
> {1,2}-to-{1,2} UTXO transfer will be permitted to *not* have Dust funding it.
> The output Night will be placed in 'cooldown', where any attempt to spend it
> will be considered invalid for as much time as it would take to generate the
> fees. The output Dust (if any) will be given a negative balance to account for
> these fees. The cooldown period must be less than a given threshold to prevent
> spending of small UTXOs that will not cover their own fees in any reasonable
> amount of time (suggestion: 1 month).
> 
> This consists of a new `CooldownState`, tracking Night UTXOs and when they
> become spendable:
> 
> ```rust
> struct CooldownState {
>     time_spendable: Map<Utxo, Timestamp>,
> }
> ```
> 
> This is updated if an unfunded transaction is deemed eligible for cooldown by
> adding its outputs to the cooldown set, with the same timestamp computed to
> when they jointly can cover the unfunded transaction's fees.
> 
> It is checked and updated on a Night spend, by ensuring that if the spent UTXO
> is a key in the map, that it's timestamp is in the past. If so, the entry is
> removed. If the timestamp is in the future, the transaction is invalid.
> 
> #### Updating the Dust states
> 
> When a Night UTXO `utxo` is spent, the generation state `gen:
> DustGenerationState` is updated by setting
> `gen.generating_tree[gen.night_indices[utxo]].dtime` (if it exists) to the current block's
> time.
> 
> When a new *generating* Night UTXO `utxo` is created, the generation state `gen:
> DustGenerationState` is updated by:
> 
> - Inserting `DustGenerationInfo { value: utxo.regular.value, owner: utxo.generation_owner, nonce: utxo.regular.nonce, dtime: Timestamp::MAX }` into `gen.generating_tree[gen.generating_tree_first_free]`
> - Inserting `DustGenerationuniquenessInfo { value: utxo.regular.value, owner: utxo.generation_owner, nonce: utxo.regular.nonce }` into `gen.generating_set`, failing if it is already present
> - Setting `gen.night_indices[utxo.regular] = gen.generating_tree_first_free`
> - Incrementing `gen.generating_tree_first_free`
> 
> (`historic_roots` should be updated at a block level, not a transaction level, so is left out here)
> 
> A new Dust output is also created, and its commitment inserted into the `DustState`. This output is defined as:
> 
> ```rust
> utxo = DustOutput {
>     value: value,
>     owner: utxo.generation_owner,
>     nonce: transient_hash(utxo.regular.nonce, 0, utxo.generation_owner),
>     seq: 0,
>     ctime: t,
> }
> ```
> 
> where `t` is the block time, and `value` is `0`, unless the output is a
> cooldown output, in which case it is `-fee`, where `fee` is the (part of) the
> transaction fee this Dust output covers.
