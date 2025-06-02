ZKIR Version 2
==============

# Overview

ZKIR (**Z**ero **K**nowledge **I**ntermediate **R**epresentation) is used as the interface between smart contracts and the Midnight proof system.
The Compact compiler generates ZKIR files for a contract as one of the compiler outputs.
These files are used as input to a separate binary (`zkir`) to generate prover and verifier keys.
The verifier keys are stored on-chain when a contract is deployed.
The prover keys are used to construct zkSNARKs ("proofs") that are included as part of a transaction.
Before a transaction is made to the network, ZKIR files are sent to the proof server along with the transaction's private inputs, in order to construct zkSNARKs to be verified on-chain.

There are two different encodings of ZKIR.
There is a [JSON](https://www.json.org/json-en.html) encoding which is produced by the Compact compiler and used as input to the `zkir` binary to generate prover and verifier keys.
There is an equivalent binary encoding which is produced as an output by the `zkir` binary and used as input to the proof server to generate zkSNARKs.
There is a separate pair of ZKIR files for each exported circuit in a contract.

Both encodings of ZKIR are considered an [application binary interface (ABI)](https://en.wikipedia.org/wiki/Application_binary_interface).
They are versioned together using [semantic versioning](https://semver.org/), the current major version is version 2.
(Version 1 was not publicly released.)

# The Memory

A ZKIR circuit consists of a linear sequence of *instructions* which describe a program for constructing a *memory*.
The memory is a growable array of *locations* indexed by 32-bit unsigned integers.
The memory has a *length*, the initial length is 0 (the memory is initially empty).
The memory is extended by incrementing the length by one and by storing into the index equal to the length before incrementing.
Each instruction has a variable number of *inputs* and *outputs*.
Inputs are explicitly given in an instruction's encoding, and they can be of various kinds as described below.
Outputs are implicitly determined by an instruction's position in the instruction sequence.

An instruction causes the next available locations in the memory to be filled with the instruction's outputs in order.
One kind of input is a memory index, which represents a use of the output of some previous instruction in the sequence.

The values that can be in a memory location are described below.

# File Header

[TODO]

# Instructions

An instruction in the JSON format is given by a JSON object with a member named `"op"` whose value is an operation name string.
In the binary format, instructions have a variable length encoding that starts with a byte that determines the operation.
An instruction has a fixed number of inputs and outputs, determined by the operation.

## Inputs

An instruction explicitly names a number of inputs.
Inputs can have various kinds.
The number and kind of an instruction's inputs depends on the operation.

- *Index* is an unsigned 32-bit value that is an index into the memory.
  This index must exist in the memory, i.e., it must have been an output of a previous instruction in the sequence.
- *Array* (e.g., in `hash_to_curve`)
- *Maybe* (e.g., in `pi_skip`)
- *u32*
- *Fr* (e.g., in `load_imm`)

## Outputs

An instruction has a number of outputs, possibly zero.
The number of ouptuts depends on the operation.

## Example

The `add` instruction has a pair of inputs `a` and `b` which are both memory indexes.

The JSON encoding is a JSON object with three named members:

- `"op"` is the operation, which is always the string `"add"`
- `"a"` is the first (left) input, which is a memory index represented by a JSON number
- `"b"` is the second (right) input, whish is also a memory index

This is denoted in the reference below as:

**JSON:** { `"op"`: `"add"`, `"a"`: Index, `"b"`: Index }

The Binary encoding of the `add` instruction consists of the hexadecimal byte value 0x11.
This is followed by the binary encoding of the inputs `a` and `b`, in that order, as (fixed length little endian?) unsigned 32-bit values.

This is denoted in the reference below as:

**Binary:** 0x11 a:u32 b:u32

# Two-phase Evaluation

ZKIR circuits are evaluated in two *phases*.
The first phase is the *rehearsal* phase, which evaluates the circuit given a (partial) proof *preimage* to construct a complete memory.
During the rehearsal phase, the proof preimage is checked for well-formedness.
The second phase is the *circuit* phase, which is given the memory produced by the rehearsal phase and uses the `midnight-circuits` library to construct a ZK proof.

## The Rehearsal Phase

The rehearsal phase is given a proof preimage, which was produced as a result of evaluating the circuit off chain.
In the Midnight network with the Compact programming language, this off-chain execution happens by generating Compact compiler-generated JavaScript code and building a proof primage.

The proof preimage consists of:

- **inputs**: the inputs to the circuit.
  In the Compact programming language, these are the circuit's arguments that it was invoked with.
- **private transcript**: the private transcript, or private inputs, are the witness return values for witnesses that were called while evaluating the circuit off chain.
- **public transcript inputs**: the public transcript inputs, or public inputs, are public inputs to the circuit.
  In the Midnight network, this is in practice the Impact VM instructions that were executed to perform ledger state accesses and updates.
- **public transcript outputs**: the public transcript outputs, or public outputs, are the results of ledger state accesses that were observed during off-chain execution.

Programs in Compact can have conditional branches.
During off-chain execution, not all branches will be taken, depending on the values of branch conditions.
Therefore, the private inputs and public outputs will only be partial; values will be missing from them for branches that were not taken.
However, the ZK proof needs to prove that values exist for these branches as well.
So a major reason for the rehearsal phase of ZKIR evaluation is to construct a full memory that contains values for all the private inputs and public outputs that exist.

### Private Inputs

The `private_input` instruction is possibly conditionally executed.
It has a single optional input *guard* index.
It produces a single output.
If there is no guard, then the instruction is unconditionally executed.

During the rehearsal phase, an index is maintained into the private transcript.
In the case where there is no guard, or where the value in the memory at the guard index is `1`, then the output of the `private_input` instruction is the private input at the current private transcript index, and the private transcript index is incremented.
In the case where the value in the memory at the guard index is `0`, then the output of the `private_input` instruction is `0`, and the private transcript index is not incremented.

### Public Outputs

The `public_input` [sic] instruction is also possibly conditionally executed.
It has a single optional input guard index and it produces a single output.
If there is no guard, then the instruction is unconditionally executed.

During the rehearsal phase, an index is maintained into the public transcript outputs.
In the case where there is no guard or where the value in the memory at the guard index is `1`, then the output of the `public_input` instruction is the public output at the current public transcript output index, and this index is incremented.
In the case where the value in the memory at the guard index is `0`, then the output of the `public_input` instruction is `0` and the public transcript output index is not incremented.

### Public Inputs

During the rehearsal phase, a complete vector of public inputs is built.
This includes the public inputs for branches that were taken, whose values are in the proof preimage's public inputs.
It also includes public inputs for branches that were not taken.
Additionally, a vector of public input *skips* is built that is a vector of optional counts.
A count in the public input skips indicates a consecutive sequence of public inputs that were skipped during off-chain execution.

Public inputs are implemented by a pair of ZKIR instructions, `declare_pub_input` and `pi_skip`.
Each `declare_pub_input` instruction is covered by exactly one `pi_skip` instruction that follows it somewhere in the ZKIR instruction sequence.
A `pi_skip` instruction can cover multiple `declare_pub_input` instructions.

The `declare_pub_input` instruction has a single input index and no output.
It specifies that the value in the memory at the input index is the next public input.
`declare_pub_input` has the effect of appending the value in the memory at the input index to the end of the public input vector and increasing the vector's length by one.
There is a index into the partial public inputs in the proof preimage, which is unconditionally incremented by `declare_pub_input`, optimistically assuming the public input was produced by the circuit's off-chain execution.

The `pi_skip` instruction is possibly conditionally executed.
It has an optional input guard index, and an input literal *count* telling how many public inputs to skip.
In the case where there is no guard or where the value in the memory at the guard index is `1`, then the public inputs were *not* skipped.
Then the `pi_skip` instruction causes the rehearsal phase to verify that the previous consecutive *count* values in the proof preimage's public inputs match exactly the ones that were appended to the complete public inputs.
A `None` optional skip is appended to the vector of public input skips (these public inputs were not skipped).
In the case where the value in the memory at the guard index is `0`, then the public inputs were skipped during off-chain execution of the circuit.
Then the `pi_skip` instruction simply decrements the index into the proof preimage's public inputs by the count, "undoing" the optimistic assumption the the public input was produced by the circuit's off-chain execution.
A skip with the given count is appended to the vector of public input skips (these public inputs were skipped).

## The Circuit Phase

The circuit phase is given the complete memory produced by the rehearsal phase and the complete public inputs.

It uses the `midnight-circuits` library to construt a zkSNARK.

# Instruction Reference

Notation [TODO]

## add

One output.  Adds a pair of field values in the prime field.

**JSON:** { `"op"`: `"add"`, `"a"`: Index, `"b"`: Index }

**Binary:** 0x11 a:u32 b:u32

**Rehearsal semantics:** the field values at indexes *a* and *b* are read from
the memory.  The memory is extended with the result of adding them in the prime
field.

**Circuit semantics:** the wires at indexes *a* and *b* are read from the
memory.  An `add` gate is built using the inputs at *a* and *b*.  The memory is
extended with the output wire of the `add` gate.

## assert

No outputs.  Asserts that a condition has the canonical true value `1`.  The
result is undefined if the condition's value is not `0` or `1`.

**JSON:** { `"op"`: `"assert"`, `"cond"`: Index }

**Binary:** 0x00 cond:u32

**Rehearsal semantics:** the field value at index *cond* is read from the
memory.  The operation fails (the rehearsal phase is aborted) if the value is 0.

**Circuit semantics:** The wire at index *cond* is read from the memory.  A
constraint is added that the value on the wire is non-zero.

## cond_select

One output.  Conditionally select between a pair of input values based on the
value of a condition.  The result is undefined if the condition's value is not
`0` or `1`.

**JSON:** { `"op"`: `"cond_select"`, `"bit"`: Index, `"a"`: Index, `"b"`: Index }

**Binary:** 0x01 bit:u32 a:u32 b:u32

**Rehearsal semantics:** the field values at indexes *bit*, *a*, and *b* are
read from the memory; the memory is extended with the value at *a* if the value
at *bit* was `1` and the value at *b* if the value at *bit* was `0`.

**Circuit semantics:** the wires at indexes *bit*, *a*, and *b* are read from
the memory.  An `is_zero` gate is built with the input at *bit*.  The output of
this gate is used as the input of a `select` gate to choose between the inputs
at *a* and *b*.  The memory is extended with the output wire of the `select`
gate.

## constrain_bits

**JSON:** { `"op"`: `"constrain_bits"`, `"var"`: Index, `"bits"`: u32 }

**Binary:** 0x02 var:u32 bits:u32

Constrains a value to a set number of bits.

**Outputs:** No outputs.

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

**JSON:** { `"op"`: `"constrain_eq"`, `"a"`: Index, `"b"`: Index }

**Binary:** 0x03 a:u32 b:u32

Constrains two values `a` and `b` to be equal.

**Outputs:** No outputs.

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

**JSON:** { `"op"`: `"constrain_to_boolean"`, `"var"`: Index }

**Binary:** 0x04 var:u32

Constrains a value `var` to be boolean (`0` or `1`).

**Outputs:** No outputs.

**Rehearsal semantics:**

    I::ConstrainToBoolean { var } => drop(idx_bool(&memory, *var)?),

**Circuit semantics:**

    I::ConstrainToBoolean { var } => {
        // Yes, this does insert a constraint.
        let _: AssignedBit<_> = std.convert(layouter, idx(&memory, *var)?)?;
    }


## copy

**JSON:** { `"op"`: `"copy"`, `"var"`: Index }

**Binary:** 0x05 var:u32

Creates a copy of a value `var`. Superfluous, but potentially useful in some
settings, and does not extend the actual circuit.

**Outputs:** One element, `var`.

**Rehearsal semantics:**

    I::Copy { var } => memory.push(idx(&memory, *var)?),

**Circuit semantics:**

    I::Copy { var } => mem_push(idx(&memory, *var)?.clone(), &mut memory)?,


## declare\_pub\_input

**JSON:** { `"op"`: `"declare_pub_input"`, `"var"`: Index }

**Binary:** 0x06 var:u32

Declares a variable as the next public input.

**Outputs:** No outputs.

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

**JSON:** { `"op"`: `"div_mod_power_of_two"`, `"var"`: Index, `"bits"`: u32 }

**Binary:** 0x0d var:u32 bits:u32

Divides with remainder by a power of two (number of bits).

**Outputs:** Two outputs, `var >> bits`, and `var & ((1 << bits) - 1)`.

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

**JSON:** { `"op"`: `"ec_add"`, `"a_x"`: Index, `"a_y"`: Index, `"b_x"`: Index, `"b_y"`: Index }

**Binary:** 0x08 a\_x:u32 a\_y:u32 b\_x:u32 b\_y:u32

Adds two elliptic curve points. UB if either is not a valid curve point.

**Outputs:** Two elements, `c_x` and `c_y`.

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

**JSON:** { `"op"`: `"ec_mul"`, `"a_x"`: Index, `"a_y"`: Index, `"scalar"`: Index }

**Binary:** 0x09 a\_x:u32 a\_y:u32 scalar:u32

Multiplies an elliptic curve point by a scalar. UB if it is not a valid curve
point.

**Outputs:** Two elements, `c_x` and `c_y`.

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

**JSON:** { `"op"`: `"ec_mul_generator"`, `"scalar"`: Index }

**Binary:** 0x0a scalar:u32

Multiplies the group generator by a scalar.

**Outputs:** Two elements, `c_x` and `c_y`.

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

**JSON:** { `"op"`: `"hash_to_curve"`, `"inputs"`, Index[] }

**Binary:** 0x0b inputs:???

Hashes a sequence of field elements to an embedded curve point.

**Outputs:** Two elements, `c_x` and `c_y`.

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

**JSON:** { `"op"`: `"less_than"`, `"a"`: Index, `"b"`: Index, `"bits"`: u32 }

**Binary:** 0x19 a:u32 b:u32 bits:u32

Checks if `a` < `b`, intepreting both as `bits`-bit unsigned integers.  UB if
`a` or `b` exceed `bits`.

**Outputs:** One boolean output `a < b`.

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

**JSON:** { `"op"`: `"load_imm"`, `"imm"`: Fr??? }

**Binary:** 0x0c imm:???

Loads a constant into the circuit.

**Outputs:** One output, `imm`.

**Rehearsal semantics:**

    I::LoadImm { imm } => memory.push(*imm),

**Circuit semantics:**

    I::LoadImm { imm } => mem_push(std.assign_fixed(layouter, imm.0)?, &mut memory)?,


## mul

**JSON:** { `"op"`: `"mul"`, `"a"`: Index, `"b"`: Index }

**Binary:** 0x12 a:u32 b:u32

Multiplies `a` and `b` in the prime field.

**Outputs:** One output `a * b`.

**Rehearsal semantics:**

    I::Mul { a, b } => memory.push(idx(&memory, *a)? * idx(&memory, *b)?),

**Circuit semantics:**

    I::Mul { a, b } => mem_push(
        std.mul(layouter, idx(&memory, *a)?, idx(&memory, *b)?, None)?,
        &mut memory,
    )?,


## neg

**JSON:** { `"op"`: `"neg"`, `"a"`: Index }

**Binary:** 0x13 a:u32

Negates `a` in the prime field.

**Outputs:** One output `-a`.

**Rehearsal semantics:**

    I::Neg { a } => memory.push(-idx(&memory, *a)?),

**Circuit semantics:**

    I::Neg { a } => mem_push(std.neg(layouter, idx(&memory, *a)?)?, &mut memory)?,


## not

**JSON:** { `"op"`: `"not"`, `"a"`: Index }

**Binary:** 0x17 a:u32

Boolean not gate.  NOTE: This gate is never emitted by the compiler.

**Outputs:** One output `!a`.

**Rehearsal semantics:**

    I::Not { a } => memory.push((!idx_bool(&memory, *a)?).into()),

**Circuit semantics:**

    I::Not { a } => mem_push(lnot(std, layouter, idx(&memory, *a)?)?, &mut memory)?,


## output

**JSON:** { `"op"`: `"output"`, `"var"`: Index }

**Binary:** 0x0e var:u32

Outputs a `var` from the circuit, including it in the communications commitment

**Outputs:** No outputs (at the level of the IR VM), despite the name.

**Rehearsal semantics:**

    I::Output { var } => outputs.push(idx(&memory, *var)?),

**Circuit semantics:**

    I::Output { var } => outputs.push(idx(&memory, *var)?.clone()),


## persistent_hash

**JSON:** { `"op"`: `"persistent_hash"`, `"alignment"`: Alignment, `"inputs"`: Index[] }

**Binary:** 0x1d alignment:??? inputs:???

Calls a long-term hash function on a sequence of items with a given alignment

**Outputs:** One output, `H(inputs)`, in the binary format.

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

**JSON:** { `"op"`: `"pi_skip"`, `"guard"`: Maybe<Index>, `"count"`: u32 }

**Binary:** 0x07 guard:??? count:u32

A marker informing the proof assembler that a set of public inputs belong
together (typically as an instruction), and whether they are active or not.

Every `declare_pub_input` should be *followed* by a `pi_skip` covering it.

**Outputs:** No outputs, but adds activity information to `IrSource::prove` and
`IrSource::check`.

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

**JSON:** { `"op"`: `"private_input"`, `"guard"`: Maybe<Index> }

**Binary:** 0x1b guard:???

Retrieves a public input from the public transcript outputs.

**Outputs:** Outputs one element, the next private transcript output, or `0` if
the guard fails

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

**JSON:** { `"op"`: `"public_input"`, `"guard"`: Maybe<Index> }

**Binary:** 0x1a guard:???

Retrieves a public input from the public transcript outputs.

**Outputs:** Outputs one element, the next public transcript output, or `0` if
the guard fails.

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

**JSON:** { `"op"`: `"reconstitute_field"`, `"divisor"`: Index, `"modulus"`: Index, `"bits"`: u32 }

**Binary:** 0x1c divisor:u32 modulus:u32 bits:u32

Takes two inputs, `divisor` and `modulus`, and outputs `divisor << bits |
modulus`, guaranteeing that the result does not overflow the field size, and
that `modulus < (1 << bits)`. Inverse of `DivModPowerOfTwo`.

**Outputs:** One.

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

**JSON:** { `"op"`: `"test_eq"`: `"a"`: Index, `"b"`: Index }

**Binary:** 0x10 a:u32 b:u32

Tests if `a` and `b` are equal.

**Outputs:** One boolean output, `a == b`.

**Rehearsal semantics:**

    I::TestEq { a, b } => memory.push((idx(&memory, *a)? == idx(&memory, *b)?).into()),

**Circuit semantics:**

    I::TestEq { a, b } => {
        let bit = std.is_equal(layouter, idx(&memory, *a)?, idx(&memory, *b)?)?;
        mem_push(std.convert(layouter, &bit)?, &mut memory)?;
    }


## transient_hash

**JSON:** { `"op"`: `"transient_hash"`, `"inputs"`: Index[] }

**Binary:** 0x0f inputs:???

Calls a circuit-friendly hash function on a sequence of items.

**Outputs:** One output, `H(inputs)`.

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
