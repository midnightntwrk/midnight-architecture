ZKIR Version 2
==============

# Gates:

## add

**JSON:** { "op": "add", "a": Index, "b": Index }

Adds `a` and `b` in the prime field.

**Outputs:** One output `a + b`.

**Binary:** 0x11 ??? ???

**Rehearsal semantics:** the field values at indexes *a* and *b* are read from
the memory; the memory is extended with the result of adding them in the prime
field.

    I::Add { a, b } => memory.push(idx(&memory, *a)? + idx(&memory, *b)?),

**Circuit semantics:** the gates at indexes *a* and *b* are read from the
memory; the memory is extended with an `add` gate using the inputs *a* and *b*.

    I::Add { a, b } => mem_push(
        std.add(layouter, idx(&memory, *a)?, idx(&memory, *b)?)?,
        &mut memory,
    )?,


## assert

**JSON:** { "op": "assert", "cond": Index }

Asserts that `index` has value `1`. Undefined behavior if `index` is not `0` or
`1`.

**Outputs:** None.

**Binary:**

**Rehearsal semantics:** the field value at *cond* is read from the memory.  The
operation fails if the value is not 0 or 1, and it fails if the value is 0.

    I::Assert { cond } => {
        if !idx_bool(&memory, *cond)? {
            bail!("Failed direct assertion");
        }
    }

**Circuit semantics:** The gate at *cond* is read from the memory.  THEN WHAT?

    I::Assert { cond } => std.assert_non_zero(layouter, idx(&memory, *cond)?)?,


## cond_select

**JSON:** { "op: "cond_select", "bit": Index, "a": Index, "b": Index }

Conditionally selects a value. Undefined behavior if `bit` is not `0` or `1`.

**Outputs:** One element, `a` or `b`.

**Binary:**

**Rehearsal semantics:**

    I::CondSelect { bit, a, b } => {
        let (bit, a, b) = (
            idx_bool(&memory, *bit)?,
            idx(&memory, *a)?,
            idx(&memory, *b)?,
        );
        memory.push(if bit { a } else { b })
    }

**Circuit semantics:**

    I::CondSelect { bit, a, b } => {
        let bit = std.is_zero(layouter, idx(&memory, *bit)?)?;
        // Note that b comes first here, because the is_zero negates the bit.
        // The negation is to ensure the bit bound. This may be
        // excessive, but user input could violate it otherwise.
        let result =
            std.select(layouter, &bit, idx(&memory, *b)?, idx(&memory, *a)?)?;
        mem_push(result, &mut memory)?;
    }


## constrain_bits

**JSON:** { "op": "constrain_bits", "var": Index, "bits" u32 }

Constrains a value to a set number of bits.

**Outputs:** No outputs.

**Binary:**

**Rehearsal semantics:**

    I::ConstrainBits { var, bits } => drop(idx_bits(&memory, *var, Some(*bits))?),

**Circuit semantics:**

    I::ConstrainBits { var, bits } => drop(std.assigned_to_le_bits(
        layouter,
        idx(&memory, *var)?,
        Some(*bits as usize),
        *bits as usize >= FR_BITS,
    )?),


## constrain_eq

**JSON:** { "op": "constrain_eq", "a": Index, "b": Index }

Constrains two values `a` and `b` to be equal.

**Outputs:** No outputs.

**Binary:**

**Rehearsal semantics:**

    I::ConstrainEq { a, b } => {
        if idx(&memory, *a)? != idx(&memory, *b)? {
            bail!(
                "Failed equality constraint: {:?} != {:?}",
                idx(&memory, *a)?,
                idx(&memory, *b)?
            );
        }
    }

**Circuit semantics:**

    I::ConstrainEq { a, b } => {
        std.assert_equal(layouter, idx(&memory, *a)?, idx(&memory, *b)?)?
    }


## constrain\_to\_boolean

**JSON:** { "op": "constrain\_to\_boolean", "var": Index }

Constrains a value `var` to be boolean (`0` or `1`).

**Outputs:** No outputs.

**Binary:**

**Rehearsal semantics:**

    I::ConstrainToBoolean { var } => drop(idx_bool(&memory, *var)?),

**Circuit semantics:**

    I::ConstrainToBoolean { var } => {
        // Yes, this does insert a constraint.
        let _: AssignedBit<_> = std.convert(layouter, idx(&memory, *var)?)?;
    }


## copy

**JSON:** { "op": "copy", "var": Index }

Creates a copy of a value `var`. Superfluous, but potentially useful in some
settings, and does not extend the actual circuit.

**Outputs:** One element, `var`.

**Binary:**

**Rehearsal semantics:**

    I::Copy { var } => memory.push(idx(&memory, *var)?),

**Circuit semantics:**

    I::Copy { var } => mem_push(idx(&memory, *var)?.clone(), &mut memory)?,


## declare\_pub\_input

**JSON:** { "op": "declare\_pub\_input", "var": Index }

Declares a variable as the next public input.

**Outputs:** No outputs.

**Binary:**

**Rehearsal semantics:**

    I::DeclarePubInput { var } => {
        pis.push(idx(&memory, *var)?);
        public_transcript_inputs_idx += 1;
    }

**Circuit semantics:**

    I::DeclarePubInput { var } => {
        pi_push(idx(&memory, *var)?.clone(), &mut public_inputs)?
    }


## div\_mod\_power\_of\_two

**JSON:** { "op": "div\_mod\_power\_of\_two", "var": Index, "bits": u32 }

Divides with remainder by a power of two (number of bits).

**Outputs:** Two outputs, `var >> bits`, and `var & ((1 << bits) - 1)`.

**Binary:**

**Rehearsal semantics:**

    I::DivModPowerOfTwo { var, bits } => {
        if *bits as usize > FR_BYTES_STORED * 8 {
            bail!("Excessive bit count");
        }
        let var_bits = idx_bits(&memory, *var, None)?;
        memory.push(from_bits(var_bits[*bits as usize..].iter().copied()));
        memory.push(from_bits(var_bits[..*bits as usize].iter().copied()));
    }

**Circuit semantics:**

    I::DivModPowerOfTwo { var, bits } => {
        let var = idx(&memory, *var)?.clone();
        let (divisor, modulus) = match &workbench {
            ProofWorkbench::Dry => (Value::unknown(), Value::unknown()),
            ProofWorkbench::Mock => (
                Value::known(Default::default()),
                Value::known(Default::default()),
            ),
            ProofWorkbench::Live(preproc) => {
                let idx = memory.len();
                if preproc.memory.len() < idx + 2 {
                    return Err(ProofError::Synthesis);
                }
                (
                    Value::known(preproc.memory[idx]),
                    Value::known(preproc.memory[idx + 1]),
                )
            }
        };
        let divisor = std.assign(layouter, divisor)?;
        let modulus = std.assign(layouter, modulus)?;
        let divisor_bits = std.assigned_to_le_bits(
            layouter,
            &divisor,
            Some(FR_BITS - *bits as usize),
            *bits == 0,
        )?;
        let modulus_bits = std.assigned_to_le_bits(
            layouter,
            &modulus,
            Some(*bits as usize),
            *bits as usize >= FR_BITS,
        )?;

        let var_bits = std.assigned_to_le_bits(layouter, &var, None, true)?;
        for (a, b) in modulus_bits
            .iter()
            .chain(divisor_bits.iter())
            .zip(var_bits.iter())
        {
            let a: AssignedCell<outer::Scalar, outer::Scalar> =
                std.convert(layouter, a)?;
            let b: AssignedCell<outer::Scalar, outer::Scalar> =
                std.convert(layouter, b)?;
            std.assert_equal(layouter, &a, &b)?;
        }
        mem_push(divisor, &mut memory)?;
        mem_push(modulus, &mut memory)?;
    }


## ec_add

**JSON:** { "op": "ec\_add", "a\_x": Index, "a\_y": Index, "b\_x": Index, "b\_y": Index }

Adds two elliptic curve points. UB if either is not a valid curve point.

**Outputs:** Two elements, `c_x` and `c_y`.

**Binary:**

**Rehearsal semantics:**

    I::EcAdd { a_x, a_y, b_x, b_y } => memory.extend(from_point(
        idx_point(&memory, *a_x, *a_y)? + idx_point(&memory, *b_x, *b_y)?,
    )),

**Circuit semantics:**

    I::EcAdd { a_x, a_y, b_x, b_y } => {
        let a = ecc_from_parts(
            std,
            layouter,
            workbench,
            idx(&memory, *a_x)?,
            idx(&memory, *a_y)?,
        )?;
        let b = ecc_from_parts(
            std,
            layouter,
            workbench,
            idx(&memory, *b_x)?,
            idx(&memory, *b_y)?,
        )?;
        let c = std.ecc_chip().add(layouter, &a, &b)?;
        mem_push(c.x(), &mut memory)?;
        mem_push(c.y(), &mut memory)?;
    }


## ec_mul

**JSON:** { "op": "ec\_mul", "a\_x": Index, "a\_y": Index, "scalar": Index }

Multiplies an elliptic curve point by a scalar. UB if it is not a valid curve
point.

**Outputs:** Two elements, `c_x` and `c_y`.

**Binary:**

**Rehearsal semantics:**

    I::EcMul { a_x, a_y, scalar } => memory.extend(from_point(
        idx_point(&memory, *a_x, *a_y)? * idx(&memory, *scalar)?,
    )),

**Circuit semantics:**

    I::EcMul { a_x, a_y, scalar } => {
        let a = ecc_from_parts(
            std,
            layouter,
            workbench,
            idx(&memory, *a_x)?,
            idx(&memory, *a_y)?,
        )?;
        let scalar = std.ecc_chip().convert(layouter, idx(&memory, *scalar)?)?;
        let b = std.ecc_chip().msm(layouter, &[scalar], &[a])?;
        mem_push(b.x(), &mut memory)?;
        mem_push(b.y(), &mut memory)?;
    }


## ec\_mul\_generator

**JSON:** { "op": "ec\_mul\_generator", "scalar": Index }

Multiplies the group generator by a scalar.

**Outputs:** Two elements, `c_x` and `c_y`.

**Binary:**

**Rehearsal semantics:**

    I::EcMulGenerator { scalar } => memory.extend(from_point(
        EmbeddedGroupAffine::generator() * idx(&memory, *scalar)?,
    )),

**Circuit semantics:**

    I::EcMulGenerator { scalar } => {
        let g: EccPoint<embedded::Affine> = std
            .ecc_chip()
            .assign_fixed(layouter, embedded::Affine::generator())?;
        let scalar = std.ecc_chip().convert(layouter, idx(&memory, *scalar)?)?;
        let b = std.ecc_chip().msm(layouter, &[scalar], &[g])?;
        mem_push(b.x(), &mut memory)?;
        mem_push(b.y(), &mut memory)?;
    }


## hash\_to\_curve

**JSON:** { "op": "hash\_to\_curve", "inputs", Index[] }

Hashes a sequence of field elements to an embedded curve point.

**Outputs:** Two elements, `c_x` and `c_y`.

**Binary:**

**Rehearsal semantics:**

    I::HashToCurve { inputs } => {
        let inputs = inputs
            .iter()
            .map(|var| idx(&memory, *var))
            .collect::<Result<Vec<_>, _>>()?;
        memory.extend(from_point(hash_to_curve(&inputs)))
    }

**Circuit semantics:**

    I::HashToCurve { inputs } => {
        let inputs = inputs
            .iter()
            .map(|input| idx(&memory, *input).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let (x, y) = std.hash_to_curve(layouter, &inputs)?;
        mem_push(x, &mut memory)?;
        mem_push(y, &mut memory)?;
    }


## less_than

**JSON:** { "op": "less_than", "a": Index, "b": Index, "bits": u32 }

Checks if `a` < `b`, intepreting both as `bits`-bit unsigned integers.  UB if
`a` or `b` exceed `bits`.

**Outputs:** One boolean output `a < b`.

**Binary:**

**Rehearsal semantics:**

    I::LessThan { a, b, bits } => memory.push(
        (from_bits(idx_bits(&memory, *a, Some(*bits))?.into_iter())
            < from_bits(idx_bits(&memory, *b, Some(*bits))?.into_iter()))
        .into(),
    ),

**Circuit semantics:**

    I::LessThan { a, b, bits } => {
        // Adding mod 2 to meet library constraint that this is even
        // Hidden req that this is >= 4
        let bit = std.lower_than(
            layouter,
            idx(&memory, *a)?,
            idx(&memory, *b)?,
            u32::max(*bits + *bits % 2, 4),
        )?;
        mem_push(std.convert(layouter, &bit)?, &mut memory)?;
    }


## load_imm

**JSON:** { "op": "load_imm", "imm": Fr??? }

Loads a constant into the circuit.

**Outputs:** One output, `imm`.

**Binary:**

**Rehearsal semantics:**

    I::LoadImm { imm } => memory.push(*imm),

**Circuit semantics:**

    I::LoadImm { imm } => mem_push(std.assign_fixed(layouter, imm.0)?, &mut memory)?,


## mul

**JSON:** { "op": "mul", "a": Index, "b": Index }

Multiplies `a` and `b` in the prime field.

**Outputs:** One output `a * b`.

**Binary:**

**Rehearsal semantics:**

    I::Mul { a, b } => memory.push(idx(&memory, *a)? * idx(&memory, *b)?),

**Circuit semantics:**

    I::Mul { a, b } => mem_push(
        std.mul(layouter, idx(&memory, *a)?, idx(&memory, *b)?, None)?,
        &mut memory,
    )?,


## neg

**JSON:** { "op": "neg", "a": Index }

Negates `a` in the prime field.

**Outputs:** One output `-a`.

**Binary:**

**Rehearsal semantics:**

    I::Neg { a } => memory.push(-idx(&memory, *a)?),

**Circuit semantics:**

    I::Neg { a } => mem_push(std.neg(layouter, idx(&memory, *a)?)?, &mut memory)?,


## not

**JSON:** { "op": "not", "a": Index }

Boolean not gate.  NOTE: This gate is never emitted by the compiler.

**Outputs:** One output `!a`.

**Binary:**

**Rehearsal semantics:**

    I::Not { a } => memory.push((!idx_bool(&memory, *a)?).into()),

**Circuit semantics:**

    I::Not { a } => mem_push(lnot(std, layouter, idx(&memory, *a)?)?, &mut memory)?,


## output

**JSON:** { "op": "output", "var": Index }

Outputs a `var` from the circuit, including it in the communications commitment

**Outputs:** No outputs (at the level of the IR VM), despite the name.

**Binary:**

**Rehearsal semantics:**

    I::Output { var } => outputs.push(idx(&memory, *var)?),

**Circuit semantics:**

    I::Output { var } => outputs.push(idx(&memory, *var)?.clone()),


## persistent_hash

**JSON:** { "op": "persistent_hash", "alignment": Alignment, "inputs": Index[] }

Calls a long-term hash function on a sequence of items with a given alignment

**Outputs:** One output, `H(inputs)`, in the binary format.

**Binary:**

**Rehearsal semantics:**

    I::PersistentHash { alignment, inputs } => {
        let inputs = inputs
            .iter()
            .map(|i| idx(&memory, *i))
            .collect::<Result<Vec<_>, _>>()?;
        let value = alignment.parse_field_repr(&inputs).ok_or_else(|| {
            error!("Inputs did not match alignment (inputs: {inputs:?}, alignment: {alignment:?})");
            anyhow!("Inputs did not match alignment (inputs: {inputs:?}, alignment: {alignment:?})")
        })?;
        let mut repr = Vec::new();
        ValueReprAlignedValue(value).binary_repr(&mut repr);
        trace!(bytes = ?repr, "bytes decoded out-of-circuit");
        let hash = persistent_hash(&repr);
        memory.push(hash.field_vec()[0]);
    }

**Circuit semantics:**

    I::PersistentHash { alignment, inputs } => {
        let inputs = inputs
            .iter()
            .map(|i| idx(&memory, *i).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let bytes = fab_decode_to_bytes(std, layouter, alignment, &inputs)?;
        let res_bytes = std.sha256(layouter, &bytes)?;
        mem_push(assemble_bytes(std, layouter, &res_bytes)?, &mut memory)?;
    }


## pi_skip

**JSON:** { "op": "pi_skip", "guard": Maybe<Index>, "count": u32 }

A marker informing the proof assembler that a set of public inputs belong
together (typically as an instruction), and whether they are active or not.

Every `declare_pub_input` should be *followed* by a `pi_skip` covering it.

**Outputs:** No outputs, but adds activity information to `IrSource::prove` and
`IrSource::check`.

**Binary:**

**Rehearsal semantics:**

    I::PiSkip { guard, count } => match guard {
        Some(guard) if !idx_bool(&memory, *guard)? => {
            pi_skips.push(Some(*count as usize));
            public_transcript_inputs_idx -= *count as usize;
        }
        _ => {
            pi_skips.push(None);
            for i in 0..(*count as usize) {
                let idx = public_transcript_inputs_idx - *count as usize + i;
                let expected = preimage.public_transcript_inputs.get(idx).copied();
                let computed = Some(pis[pis.len() - *count as usize + i]);
                if expected != computed {
                    error!(
                        ?idx,
                        ?expected,
                        ?computed,
                        ?memory,
                        ?pis,
                        "Public transcript input mismatch"
                    );
                    bail!(
                        "Public transcript input mismatch for input {idx}; expected: {expected:?}, computed: {computed:?}"
                    );
                }
            }
        }
    },

**Circuit semantics:**

    I::PiSkip { .. } => {}


## private_input

**JSON:** { "op": "private_input", "guard": Maybe<Index> }

Retrieves a public input from the public transcript outputs.

**Outputs:** Outputs one element, the next private transcript output, or `0` if
the guard fails

**Binary:**

**Rehearsal semantics:**

    I::PrivateInput { guard } => match guard {
        Some(guard) if !idx_bool(&memory, *guard)? => memory.push(0.into()),
        _ => {
            memory.push(
                preimage
                    .private_transcript
                    .get(private_transcript_outputs_idx)
                    .copied()
                    .ok_or(anyhow!("Ran out of private transcript outputs"))?,
            );
            private_transcript_outputs_idx += 1;
        }
    },

**Circuit semantics:**

    I::PublicInput { guard } | I::PrivateInput { guard } => {
        let guard = guard.map(|guard| idx(&memory, guard)).transpose()?;
        let value = match &workbench {
            ProofWorkbench::Live(preproc) => {
                let idx = memory.len();
                if idx > preproc.memory.len() {
                    error!("Ran out of preprocessed memory. This is a bug.");
                    return Err(ProofError::Synthesis);
                }
                Value::known(preproc.memory[idx])
            }
            ProofWorkbench::Dry => Value::unknown(),
            ProofWorkbench::Mock => Value::known(Default::default()),
        };
        let value_cell = std.assign(layouter, value)?;
        // If `guard` is Some, then we want to ensure that
        // `value` is 0 if `guard` is 0
        // That is: guard == 0 -> value == 0
        // => value == 0 || guard
        if let Some(guard) = guard {
            let value_is_zero = std.is_zero(layouter, &value_cell)?;
            let guard_bit = std.convert(layouter, guard)?;
            let is_ok = std.or(layouter, &[value_is_zero, guard_bit])?;
            let is_ok_field = std.convert(layouter, &is_ok)?;
            std.assert_non_zero(layouter, &is_ok_field)?;
        }
        mem_push(value_cell, &mut memory)?;
    }


## public_input

**JSON:** { "op": "public_input", "guard": Maybe<Index> }

Retrieves a public input from the public transcript outputs.

**Outputs:** Outputs one element, the next public transcript output, or `0` if
the guard fails.

**Binary:**

**Rehearsal semantics:**

    I::PublicInput { guard } => {
        let val = match guard {
            Some(guard) if !idx_bool(&memory, *guard)? => 0.into(),
            _ => {
                public_transcript_outputs_idx += 1;
                preimage
                    .public_transcript_outputs
                    .get(public_transcript_outputs_idx - 1)
                    .copied()
                    .ok_or(anyhow!("Ran out of public transcript outputs"))?
            }
        };
        memory.push(val);
    }

**Circuit semantics:**

ZK semantics is the same as `private_input`.


## reconstitute_field

**JSON:** { "op": "reconstitute_field", "divisor": Index, "modulus": Index, "bits": u32 }

Takes two inputs, `divisor` and `modulus`, and outputs `divisor << bits |
modulus`, guaranteeing that the result does not overflow the field size, and
that `modulus < (1 << bits)`. Inverse of `DivModPowerOfTwo`.

**Outputs:** One.

**Binary:**

**Rehearsal semantics:**

    I::ReconstituteField {
        divisor,
        modulus,
        bits,
    } => {
        if *bits as usize > FR_BYTES_STORED * 8 {
            bail!("Excessive bit count");
        }
        let fr_max = Fr::from(-1);
        let max_bits = idx_bits(&[fr_max], 0, None)?;
        let modulus_bits = idx_bits(&memory, *modulus, Some(*bits))?;
        let divisor_bits = idx_bits(&memory, *divisor, Some(FR_BITS as u32 - *bits))?;
        let cmp = modulus_bits
            .iter()
            .chain(divisor_bits.iter())
            .rev()
            .zip(max_bits[..FR_BITS].iter().rev())
            .map(|(ab, max)| ab.cmp(max))
            .fold(
                Ordering::Equal,
                |prefix, local| if prefix.is_eq() { local } else { prefix },
            );
        if cmp.is_gt() {
            bail!("Reconstituted element overflows field");
        }
        let power = (0..*bits).fold(Fr::from(1), |acc, _| Fr::from(2) * acc);
        memory.push(power * idx(&memory, *divisor)? + idx(&memory, *modulus)?);
    }

**Circuit semantics:**

    I::ReconstituteField {
        divisor,
        modulus,
        bits,
    } => {
        let divisor = idx(&memory, *divisor)?.clone();
        let modulus = idx(&memory, *modulus)?.clone();
        let reconstituted_value = match &workbench {
            ProofWorkbench::Dry => Value::unknown(),
            ProofWorkbench::Mock => Value::known(Default::default()),
            ProofWorkbench::Live(preproc) => {
                let idx = memory.len();
                if preproc.memory.len() < idx + 1 {
                    return Err(ProofError::Synthesis);
                }
                Value::known(preproc.memory[idx])
            }
        };
        let reconstituted = std.assign(layouter, reconstituted_value)?;
        let divisor_bits = std.assigned_to_le_bits(
            layouter,
            &divisor,
            Some(FR_BITS - *bits as usize),
            *bits == 0,
        )?;
        let modulus_bits = std.assigned_to_le_bits(
            layouter,
            &modulus,
            Some(*bits as usize),
            *bits as usize >= FR_BITS,
        )?;
        let reconstituted_bits =
            std.assigned_to_le_bits(layouter, &reconstituted, None, true)?;
        for (a, b) in modulus_bits
            .iter()
            .chain(divisor_bits.iter())
            .zip(reconstituted_bits.iter())
        {
            let a: AssignedCell<outer::Scalar, outer::Scalar> =
                std.convert(layouter, a)?;
            let b: AssignedCell<outer::Scalar, outer::Scalar> =
                std.convert(layouter, b)?;
            std.assert_equal(layouter, &a, &b)?;
        }
        mem_push(reconstituted, &mut memory)?;
    }


## test_eq

**JSON:** { "op": "test_eq": "a": Index, "b": Index }

Tests if `a` and `b` are equal.

**Outputs:** One boolean output, `a == b`.

**Binary:**

**Rehearsal semantics:**

    I::TestEq { a, b } => memory.push((idx(&memory, *a)? == idx(&memory, *b)?).into()),

**Circuit semantics:**

    I::TestEq { a, b } => {
        let bit = std.is_equal(layouter, idx(&memory, *a)?, idx(&memory, *b)?)?;
        mem_push(std.convert(layouter, &bit)?, &mut memory)?;
    }


## transient_hash

**JSON:** { "op": "transient_hash", "inputs": Index[] }

Calls a circuit-friendly hash function on a sequence of items.

**Outputs:** One output, `H(inputs)`.

**Binary:**

**Rehearsal semantics:**

    I::TransientHash { inputs } => memory.push(transient_hash(
        &inputs
            .iter()
            .map(|i| idx(&memory, *i))
            .collect::<Result<Vec<_>, _>>()?,
    )),

**Circuit semantics:**

    I::TransientHash { inputs } => mem_push(
        std.poseidon(
            layouter,
            &inputs
                .iter()
                .map(|inp| idx(&memory, *inp).cloned())
                .collect::<Result<Vec<_>, _>>()?,
        )?,
        &mut memory,
    )?,
