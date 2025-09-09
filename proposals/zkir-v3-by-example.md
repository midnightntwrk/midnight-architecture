**Overview:**
This document is an example of what ZKIR v3 circuits will look like.
It is structured as a series of transformations made on a ZKIR v2 example circuit.
Out implementation plan will likely follow this sequence of transformations, building and testing each in turn.
If you just want to see the final version 3 circuit, scroll down to the bottom of the document.

All of the JSON output was produced by hand, so it may well contain bugs introduced by that translation.

# An Example Circuit

We consider part of the Zswap contract found in the [Midnight ledger](https://github.com/midnightntwrk/midnight-ledger/blob/main/zswap/zswap.compact).

```typescript
export circuit output(
  pk: Either<ZswapCoinPublicKey, ContractAddress>,
  coin: CoinInfo,
  rc: Field
): [] {
  const coinCom = persistentHash<CoinPreimage>(
    CoinPreimage {
      info: coin,
      dataType: pk.is_left,
      data: pk.is_left ? pk.left.bytes : pk.right.bytes,
      sep: "mdn:cc"
    });
  merkleTree.insertHash(disclose(coinCom));
  if(!disclose(pk.is_left)) {
    contractAddr = disclose(pk.right);
  }
  const colorBase = hashToCurve<[Bytes<32>, Uint<16>]>([coin.color, segment]);
  const pedersenBlinding = ecMulGenerator(rc);
  const pedersenCommit = ecMul(colorBase, coin.value);
  valueCom = disclose(ecAdd(pedersenBlinding, pedersenCommit));
}
```

This is compiled into the following ZKIR version 2 circuit:

```json
{
  "version": { "major": 2, "minor": 0 },
  "do_communications_commitment": true,
  "num_inputs": 11,
  "instructions": [
    { "op": "constrain_to_boolean", "var": 0 },
    { "op": "constrain_bits", "var": 1, "bits": 8 },
    { "op": "constrain_bits", "var": 2, "bits": 248 },
    { "op": "constrain_bits", "var": 3, "bits": 8 },
    { "op": "constrain_bits", "var": 4, "bits": 248 },
    { "op": "constrain_bits", "var": 5, "bits": 8 },
    { "op": "constrain_bits", "var": 6, "bits": 248 },
    { "op": "constrain_bits", "var": 7, "bits": 8 },
    { "op": "constrain_bits", "var": 8, "bits": 248 },
    { "op": "constrain_bits", "var": 9, "bits": 128 },
    { "op": "load_imm", "imm": "01" },
    { "op": "load_imm", "imm": "00" },
    { "op": "cond_select", "bit": 0, "a": 12, "b": 11 },
    { "op": "cond_select", "bit": 0, "a": 1, "b": 3 },
    { "op": "cond_select", "bit": 0, "a": 2, "b": 4 },
    { "op": "load_imm", "imm": "6D646E3A6363" },
    { "op": "persistent_hash", "alignment": [{ "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 16, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 1, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 6, "tag": "bytes" } }], "inputs": [5, 6, 7, 8, 9, 0, 14, 15, 16] },
    { "op": "load_imm", "imm": "70" },
    { "op": "declare_pub_input", "var": 19 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 12 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "declare_pub_input", "var": 19 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 12 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "load_imm", "imm": "32" },
    { "op": "declare_pub_input", "var": 20 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "50" },
    { "op": "declare_pub_input", "var": 21 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "load_imm", "imm": "11" },
    { "op": "load_imm", "imm": "20" },
    { "op": "declare_pub_input", "var": 22 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 23 },
    { "op": "declare_pub_input", "var": 17 },
    { "op": "declare_pub_input", "var": 18 },
    { "op": "pi_skip", "guard": 11, "count": 6 },
    { "op": "load_imm", "imm": "91" },
    { "op": "declare_pub_input", "var": 24 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "A1" },
    { "op": "declare_pub_input", "var": 25 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "declare_pub_input", "var": 19 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "load_imm", "imm": "0E" },
    { "op": "declare_pub_input", "var": 26 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "pi_skip", "guard": 11, "count": 2 },
    { "op": "declare_pub_input", "var": 25 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "02" },
    { "op": "declare_pub_input", "var": 19 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 27 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "declare_pub_input", "var": 20 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "declare_pub_input", "var": 21 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 12 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "load_imm", "imm": "0A" },
    { "op": "declare_pub_input", "var": 28 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "declare_pub_input", "var": 22 },
    { "op": "declare_pub_input", "var": 12 },
    { "op": "pi_skip", "guard": 11, "count": 2 },
    { "op": "declare_pub_input", "var": 24 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "A2" },
    { "op": "declare_pub_input", "var": 29 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "10" },
    { "op": "load_imm", "imm": "03" },
    { "op": "cond_select", "bit": 13, "a": 30, "b": 12 },
    { "op": "declare_pub_input", "var": 32 },
    { "op": "declare_pub_input", "var": 13 },
    { "op": "declare_pub_input", "var": 13 },
    { "op": "declare_pub_input", "var": 13 },
    { "op": "cond_select", "bit": 13, "a": 31, "b": 12 },
    { "op": "declare_pub_input", "var": 33 },
    { "op": "pi_skip", "guard": 13, "count": 5 },
    { "op": "cond_select", "bit": 13, "a": 22, "b": 12 },
    { "op": "declare_pub_input", "var": 34 },
    { "op": "declare_pub_input", "var": 13 },
    { "op": "declare_pub_input", "var": 13 },
    { "op": "cond_select", "bit": 13, "a": 23, "b": 12 },
    { "op": "declare_pub_input", "var": 35 },
    { "op": "cond_select", "bit": 13, "a": 3, "b": 12 },
    { "op": "declare_pub_input", "var": 36 },
    { "op": "cond_select", "bit": 13, "a": 4, "b": 12 },
    { "op": "declare_pub_input", "var": 37 },
    { "op": "pi_skip", "guard": 13, "count": 6 },
    { "op": "cond_select", "bit": 13, "a": 24, "b": 12 },
    { "op": "declare_pub_input", "var": 38 },
    { "op": "pi_skip", "guard": 13, "count": 1 },
    { "op": "load_imm", "imm": "30" },
    { "op": "declare_pub_input", "var": 39 },
    { "op": "pi_skip", "guard": 11, "count": 1 },
    { "op": "load_imm", "imm": "05" },
    { "op": "declare_pub_input", "var": 21 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 40 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "public_input", "guard": null },
    { "op": "load_imm", "imm": "0C" },
    { "op": "declare_pub_input", "var": 42 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 27 },
    { "op": "declare_pub_input", "var": 41 },
    { "op": "pi_skip", "guard": 11, "count": 4 },
    { "op": "hash_to_curve", "inputs": [7, 8, 41] },
    { "op": "ec_mul_generator", "scalar": 10 },
    { "op": "ec_mul", "a_x": 43, "a_y": 44, "scalar": 9 },
    { "op": "ec_add", "a_x": 45, "a_y": 46, "b_x": 47, "b_y": 48 },
    { "op": "declare_pub_input", "var": 30 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 27 },
    { "op": "pi_skip", "guard": 11, "count": 5 },
    { "op": "load_imm", "imm": "-02" },
    { "op": "declare_pub_input", "var": 22 },
    { "op": "declare_pub_input", "var": 11 },
    { "op": "declare_pub_input", "var": 27 },
    { "op": "declare_pub_input", "var": 51 },
    { "op": "declare_pub_input", "var": 51 },
    { "op": "declare_pub_input", "var": 49 },
    { "op": "declare_pub_input", "var": 50 },
    { "op": "pi_skip", "guard": 11, "count": 7 },
    { "op": "declare_pub_input", "var": 24 },
    { "op": "pi_skip", "guard": 11, "count": 1 }
  ]
}
```

# Sybolic Names

Instruction outputs in ZKIR version 2 are implicitly numbered starting from the inputs and continuing with the instructions in order.
The instruction output indexes don't easily correspond to the instruction numbers because instructions can have zero, one, or two outputs.
A possible change for ZKIR version 3 is to change the implicit output indexes into explicit output names.
While this is not the most important change, it's the first one we will make here because it makes the rest of the changes easier to understand.

To make it easy to do this transformation by hand, we first give the outputs names of the form _vN_ where _N_ is the output index of the ZKIR v2 insruction.


```json
{
  "version": { "major": 3, "minor": 0 },
  "do_communications_commitment": true,
  "inputs": ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10"],
  "instructions": [
    { "op": "constrain_to_boolean", "var": "v0" },
    { "op": "constrain_bits", "var": "v1", "bits": 8 },
    { "op": "constrain_bits", "var": "v2", "bits": 248 },
    { "op": "constrain_bits", "var": "v3", "bits": 8 },
    { "op": "constrain_bits", "var": "v4", "bits": 248 },
    { "op": "constrain_bits", "var": "v5", "bits": 8 },
    { "op": "constrain_bits", "var": "v6", "bits": 248 },
    { "op": "constrain_bits", "var": "v7", "bits": 8 },
    { "op": "constrain_bits", "var": "v8", "bits": 248 },
    { "op": "constrain_bits", "var": "v9", "bits": 128 },
    { "op": "load_imm", "output": "v11", "imm": "01" },
    { "op": "load_imm", "output": "v12", "imm": "00" },
    { "op": "cond_select", "output": "v13", "bit": "v0", "a": "v12", "b": "v11" },
    { "op": "cond_select", "output": "v14", "bit": "v0", "a": "v1", "b": "v3" },
    { "op": "cond_select", "output": "v15", "bit": "v0", "a": "v2", "b": "v4" },
    { "op": "load_imm", "output": "v16", "imm": "6D646E3A6363" },
    { "op": "persistent_hash", "outputs": ["v17", "v18"],
	  "alignment": [{ "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 16, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 1, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 6, "tag": "bytes" } }],
	  "inputs": ["v5", "v6", "v7", "v8", "v9", "v0", "v14", "v15", "v16"] },
    { "op": "load_imm", "output": "v19", "imm": "70" },
    { "op": "declare_pub_input", "var": "v19" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v12" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "declare_pub_input", "var": "v19" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v12" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "load_imm", "output": "v20", "imm": "32" },
    { "op": "declare_pub_input", "var": "v20" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v21", "imm": "50" },
    { "op": "declare_pub_input", "var": "v21" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "load_imm", "output": "v22", "imm": "11" },
    { "op": "load_imm", "output": "v23", "imm": "20" },
    { "op": "declare_pub_input", "var": "v22" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v23" },
    { "op": "declare_pub_input", "var": "v17" },
    { "op": "declare_pub_input", "var": "v18" },
    { "op": "pi_skip", "guard": "v11", "count": 6 },
    { "op": "load_imm", "output": "v24", "imm": "91" },
    { "op": "declare_pub_input", "var": "v24" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v25", "imm": "A1" },
    { "op": "declare_pub_input", "var": "v25" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "declare_pub_input", "var": "v19" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "load_imm", "output": "v26", "imm": "0E" },
    { "op": "declare_pub_input", "var": "v26" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "pi_skip", "guard": "v11", "count": 2 },
    { "op": "declare_pub_input", "var": "v25" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v27", "imm": "02" },
    { "op": "declare_pub_input", "var": "v19" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v27" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "declare_pub_input", "var": "v20" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "declare_pub_input", "var": "v21" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v12" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "load_imm", "output": "v28", "imm": "0A" },
    { "op": "declare_pub_input", "var": "v28" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "declare_pub_input", "var": "v22" },
    { "op": "declare_pub_input", "var": "v12" },
    { "op": "pi_skip", "guard": "v11", "count": 2 },
    { "op": "declare_pub_input", "var": "v24" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v29", "imm": "A2" },
    { "op": "declare_pub_input", "var": "v29" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v30", "imm": "10" },
    { "op": "load_imm", "output": "v31", "imm": "03" },
    { "op": "cond_select", "output": "v32", "bit": "v13", "a": "v30", "b": "v12" },
    { "op": "declare_pub_input", "var": "v32" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "cond_select", "output": "v33", "bit": "v13", "a": "v31", "b": "v12" },
    { "op": "declare_pub_input", "var": "v33" },
    { "op": "pi_skip", "guard": "v13", "count": 5 },
    { "op": "cond_select", "output": "v34", "bit": "v13", "a": "v22", "b": "v12" },
    { "op": "declare_pub_input", "var": "v34" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "cond_select", "output": "v35", "bit": "v13", "a": "v23", "b": "v12" },
    { "op": "declare_pub_input", "var": "v35" },
    { "op": "cond_select", "output": "v36", "bit": "v13", "a": "v3", "b": "v12" },
    { "op": "declare_pub_input", "var": "v36" },
    { "op": "cond_select", "output": "v37", "bit": "v13", "a": "v4", "b": "v12" },
    { "op": "declare_pub_input", "var": "v37" },
    { "op": "pi_skip", "guard": "v13", "count": 6 },
    { "op": "cond_select", "output": "v38", "bit": "v13", "a": "v24", "b": "v12" },
    { "op": "declare_pub_input", "var": "v38" },
    { "op": "pi_skip", "guard": "v13", "count": 1 },
    { "op": "load_imm", "output": "v39", "imm": "30" },
    { "op": "declare_pub_input", "var": "v39" },
    { "op": "pi_skip", "guard": "v11", "count": 1 },
    { "op": "load_imm", "output": "v40", "imm": "05" },
    { "op": "declare_pub_input", "var": "v21" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v40" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "public_input", "output": "v41", "guard": null },
    { "op": "load_imm", "output": "v42", "imm": "0C" },
    { "op": "declare_pub_input", "var": "v42" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v27" },
    { "op": "declare_pub_input", "var": "v41" },
    { "op": "pi_skip", "guard": "v11", "count": 4 },
    { "op": "hash_to_curve", "outputs": ["v43", "v44"], "inputs": ["v7", "v8", "v41"] },
    { "op": "ec_mul_generator", "outputs": ["v45", "v46"], "scalar": "v10" },
    { "op": "ec_mul", "outputs": ["v47", "v48"], "a_x": "v43", "a_y": "v44", "scalar": "v9" },
    { "op": "ec_add", "outputs": ["v49", "v50"], "a_x": "v45", "a_y": "v46", "b_x": "v47", "b_y": "v48" },
    { "op": "declare_pub_input", "var": "v30" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v27" },
    { "op": "pi_skip", "guard": "v11", "count": 5 },
    { "op": "load_imm", "output": "v51", "imm": "-02" },
    { "op": "declare_pub_input", "var": "v22" },
    { "op": "declare_pub_input", "var": "v11" },
    { "op": "declare_pub_input", "var": "v27" },
    { "op": "declare_pub_input", "var": "v51" },
    { "op": "declare_pub_input", "var": "v51" },
    { "op": "declare_pub_input", "var": "v49" },
    { "op": "declare_pub_input", "var": "v50" },
    { "op": "pi_skip", "guard": "v11", "count": 7 },
    { "op": "declare_pub_input", "var": "v24" },
    { "op": "pi_skip", "guard": "v11", "count": 1 }
  ]
}
```

# Immediate Inputs

In ZKIR version 2, instruction inputs are always instruction output indexes.
The exception is a few inputs that are defined immediates, such as the bit width in `constrain_bits` and the immediate value in `load_imm`.
With the change just above, inputs are symbolic ouput names instead of indexes.

We could make a further change to allow instruction inputs to also be immediate values.
We could then get rid of the `load_imm` instruction.
In the JSON representation, a string starting with a digit or a minus sign is an immediate field value and all others are named instruction outputs.

With that change, we have fewer names:

```json
{
  "version": { "major": 3, "minor": 0 },
  "do_communications_commitment": true,
  "inputs": ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10"],
  "instructions": [
    { "op": "constrain_to_boolean", "var": "v0" },
    { "op": "constrain_bits", "var": "v1", "bits": 8 },
    { "op": "constrain_bits", "var": "v2", "bits": 248 },
    { "op": "constrain_bits", "var": "v3", "bits": 8 },
    { "op": "constrain_bits", "var": "v4", "bits": 248 },
    { "op": "constrain_bits", "var": "v5", "bits": 8 },
    { "op": "constrain_bits", "var": "v6", "bits": 248 },
    { "op": "constrain_bits", "var": "v7", "bits": 8 },
    { "op": "constrain_bits", "var": "v8", "bits": 248 },
    { "op": "constrain_bits", "var": "v9", "bits": 128 },
    { "op": "cond_select", "output": "v13", "bit": "v0", "a": "0x0", "b": "0x1" },
    { "op": "cond_select", "output": "v14", "bit": "v0", "a": "v1", "b": "v3" },
    { "op": "cond_select", "output": "v15", "bit": "v0", "a": "v2", "b": "v4" },
    { "op": "persistent_hash", "outputs": ["v17", "v18"],
	  "alignment": [{ "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 16, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 1, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 6, "tag": "bytes" } }],
	  "inputs": ["v5", "v6", "v7", "v8", "v9", "v0", "v14", "v15", "0x6d646e3a6363"] },
    { "op": "declare_pub_input", "var": "0x70" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x0" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0x70" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x0" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0x32" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x50" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0x11" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x20" },
    { "op": "declare_pub_input", "var": "v17" },
    { "op": "declare_pub_input", "var": "v18" },
    { "op": "pi_skip", "guard": "0x1", "count": 6 },
    { "op": "declare_pub_input", "var": "0x91" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0xa1" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x70" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0xe" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "pi_skip", "guard": "0x1", "count": 2 },
    { "op": "declare_pub_input", "var": "0xa1" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x70" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x2" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0x32" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x50" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x0" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "declare_pub_input", "var": "0xa" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x11" },
    { "op": "declare_pub_input", "var": "0x0" },
    { "op": "pi_skip", "guard": "0x1", "count": 2 },
    { "op": "declare_pub_input", "var": "0x91" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0xa2" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "cond_select", "output": "v32", "bit": "v13", "a": "0x10", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v32" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "cond_select", "output": "v33", "bit": "v13", "a": "0x3", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v33" },
    { "op": "pi_skip", "guard": "v13", "count": 5 },
    { "op": "cond_select", "output": "v34", "bit": "v13", "a": "0x11", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v34" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "declare_pub_input", "var": "v13" },
    { "op": "cond_select", "output": "v35", "bit": "v13", "a": "0x20", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v35" },
    { "op": "cond_select", "output": "v36", "bit": "v13", "a": "v3", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v36" },
    { "op": "cond_select", "output": "v37", "bit": "v13", "a": "v4", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v37" },
    { "op": "pi_skip", "guard": "v13", "count": 6 },
    { "op": "cond_select", "output": "v38", "bit": "v13", "a": "0x91", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v38" },
    { "op": "pi_skip", "guard": "v13", "count": 1 },
    { "op": "declare_pub_input", "var": "0x30" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 },
    { "op": "declare_pub_input", "var": "0x50" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x5" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "public_input", "output": "v41", "guard": null },
    { "op": "declare_pub_input", "var": "0xc" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x2" },
    { "op": "declare_pub_input", "var": "v41" },
    { "op": "pi_skip", "guard": "0x1", "count": 4 },
    { "op": "hash_to_curve", "outputs": ["v43", "v44"], "inputs": ["v7", "v8", "v41"] },
    { "op": "ec_mul_generator", "outputs": ["v45", "v46"], "scalar": "v10" },
    { "op": "ec_mul", "outputs": ["v47", "v48"], "a_x": "v43", "a_y": "v44", "scalar": "v9" },
    { "op": "ec_add", "outputs": ["v49", "v50"], "a_x": "v45", "a_y": "v46", "b_x": "v47", "b_y": "v48" },
    { "op": "declare_pub_input", "var": "0x10" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x2" },
    { "op": "pi_skip", "guard": "0x1", "count": 5 },
    { "op": "declare_pub_input", "var": "0x11" },
    { "op": "declare_pub_input", "var": "0x1" },
    { "op": "declare_pub_input", "var": "0x2" },
    { "op": "declare_pub_input", "var": "-0x2" },
    { "op": "declare_pub_input", "var": "-0x2" },
    { "op": "declare_pub_input", "var": "v49" },
    { "op": "declare_pub_input", "var": "v50" },
    { "op": "pi_skip", "guard": "0x1", "count": 7 },
    { "op": "declare_pub_input", "var": "0x91" },
    { "op": "pi_skip", "guard": "0x1", "count": 1 }
  ]
}
```

# Simplify Public Input Handling

The handling of public inputs via `declare_pub_input` and `pi_skip` instructions is complicated.

First, there seems to be some redundancy.
We will emit an instruction sequence like:

```json
    { "op": "cond_select", "output": "v33", "bit": "v13", "a": "0x3", "b": "0x0" },
    { "op": "declare_pub_input", "var": "v33" },
    { "op": "pi_skip", "guard": "v13", "count": 5 },
```

In the first instruction in the sequence, _v33_ is given the value 0x3 if _v13_ is true and 0x0 otherwise.
This value (either 0x3 or 0x0) is declared as a public input.
Then, the `pi_skip` instruction is guarded by _v13_.
It has the semantics of keeping the value (0x3 or 0x0) if _v13_ is true, and replacing it with 0 otherwise.
However, when _v13_ is true, this value is always 0x3.

So it seems that some of these `cond_select` instructions exist to make public inputs zero,
which is not necessary when the corresponding `pi_skip` has the same guard condition.

The next observation is that we always have a sequence of `declare_pub_input` instructions,
corresponding to an Impact VM instruction.
Then we have a guarded `pi_skip` that covers them and mentions the length of the sequence.

A simpler representation is:

- `declare_pub_input` is changed to `declare_pub_inputs` and takes a sequence of inputs corresponding to an Impact VM instruction, and
- `pi_skip` is eliminated in favor of making `declare_pub_inputs` itself guarded.

We can represent `declare_pub_inputs` with a literal guard of 0x1 as an unconditional one, with no guard.

With those simplifications, we have:

```json
{
  "version": { "major": 3, "minor": 0 },
  "do_communications_commitment": true,
  "inputs": ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10"],
  "instructions": [
    { "op": "constrain_to_boolean", "var": "v0" },
    { "op": "constrain_bits", "var": "v1", "bits": 8 },
    { "op": "constrain_bits", "var": "v2", "bits": 248 },
    { "op": "constrain_bits", "var": "v3", "bits": 8 },
    { "op": "constrain_bits", "var": "v4", "bits": 248 },
    { "op": "constrain_bits", "var": "v5", "bits": 8 },
    { "op": "constrain_bits", "var": "v6", "bits": 248 },
    { "op": "constrain_bits", "var": "v7", "bits": 8 },
    { "op": "constrain_bits", "var": "v8", "bits": 248 },
    { "op": "constrain_bits", "var": "v9", "bits": 128 },
    { "op": "cond_select", "output": "v13", "bit": "v0", "a": "0x0", "b": "0x1" },
    { "op": "cond_select", "output": "v14", "bit": "v0", "a": "v1", "b": "v3" },
    { "op": "cond_select", "output": "v15", "bit": "v0", "a": "v2", "b": "v4" },
    { "op": "persistent_hash", "outputs": ["v17", "v18"],
	  "alignment": [{ "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 16, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 1, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 6, "tag": "bytes" } }],
	  "inputs": ["v5", "v6", "v7", "v8", "v9", "v0", "v14", "v15", "0x6d646e3a6363"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x32"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x1", "0x1", "0x20", "v17", "v18"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0xe", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x2"] },
    { "op": "declare_pub_inputs", "inputs": ["0x32"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa"] },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa2"] },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x10", "0x1", "0x1", "0x1", "0x3"] },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x11", "0x1", "0x1", "0x20", "v3", "v4"] },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0x30"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x5"] },
    { "op": "public_input", "output": "v41", "guard": null },
    { "op": "declare_pub_inputs", "inputs": ["0xc", "0x1", "0x2", "v41"] },
    { "op": "hash_to_curve", "outputs": ["v43", "v44"], "inputs": ["v7", "v8", "v41"] },
    { "op": "ec_mul_generator", "outputs": ["v45", "v46"], "scalar": "v10" },
    { "op": "ec_mul", "outputs": ["v47", "v48"], "a_x": "v43", "a_y": "v44", "scalar": "v9" },
    { "op": "ec_add", "outputs": ["v49", "v50"], "a_x": "v45", "a_y": "v46", "b_x": "v47", "b_y": "v48" },
    { "op": "declare_pub_inputs", "inputs": ["0x10", "0x1", "0x1", "0x1", "0x2"] },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x1", "0x2", "-0x2", "-0x2", "v49", "v50"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
  ]
}
```

# Typed ZKIR

In the program above, everything is represented as fields.

We can institute a type system.

- _v0_ is the boolean value `pk.is_left` in Compact and so we can represent that as a `Bit`
- _v1_ and _v2_ constitute the 32 byte array `pk.left` (a `ZswapCoinPublicKey`) and so we can represent that as a single `Byte[32]`
- Likewise, _v3_ and _v4_ are the 32 byte array, `pk.right` (a `ContractAddress`)
- _v5_ and _v6_ are `coin.nonce`, a 32 byte array
- _v7_ and _v8_ are `coin.color`, a 32 byte array
- _v9_ is `value`, a 128-bit unsigned integer
- _v10_ is `rc`, a field value

We can annotate the types of the inputs and remove the explicit constraint instructions.
We will continue to represent the unsigned integer `value` as a constrained field value.

The 32 byte arrays need to be represented as pairs of field values for passing to the runtime function `persistent_hash` and also when the occur in Impact VM instructions.
We introduce a type-directed `encode` instruction with a variable number of field-typed outputs.

The instructions `hash_to_curve`, `ec_mul_generator`, `ec_mul`, and `ec_add` each output a single `Point`-typed value.
Likewise, their inputs have `Point` types where appropriate.
Like for byte arrays, `Point`s need to be encoded into field values when they appear in Impact instructions.

```json
{
  "version": { "major": 3, "minor": 0 },
  "do_communications_commitment": true,
  "inputs": ["pk.is_left", "pk.left",   "pk.right",  "coin.nonce", "coin.color", "value", "rc"],
  "types":  ["Bit",        "Bytes[32]", "Bytes[32]", "Bytes[32]",  "Bytes[32]",  "Field", "Field"],
  "instructions": [
    { "op": "constrain_bits", "var": "v9", "bits": 128 },
    { "op": "cond_select", "output": "v13", "bit": "pk.is_left", "a": "0x0", "b": "0x1" },
    { "op": "cond_select", "output": "v14", "bit": "pk.is_left", "a": "pk.left", "b": "pk.right" },
	{ "op": "encode", "outputs": ["tmp0", "tmp1"], "var": "coin.nonce" },
	{ "op": "encode", "outputs": ["tmp2", "tmp3"], "var": "coin.color" },
	{ "op": "encode", "outputs": ["tmp4", "tmp5"], var: "v14" },
    { "op": "persistent_hash", "outputs": ["v17", "v18"],
	  "alignment": [{ "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 16, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 1, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 32, "tag": "bytes" } }, { "tag": "atom", "value": { "length": 6, "tag": "bytes" } }],
	  "inputs": ["tmp0", "tmp1", "tmp2", "tmp3", "value", "pk.is_left", "tmp4", "tmp5", "0x6d646e3a6363"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x32"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x1", "0x1", "0x20", "v17", "v18"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0xe", "0x1"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa1"] },
    { "op": "declare_pub_inputs", "inputs": ["0x70", "0x1", "0x1", "0x2"] },
    { "op": "declare_pub_inputs", "inputs": ["0x32"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa"] },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x0"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0xa2"] },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x10", "0x1", "0x1", "0x1", "0x3"] },
	{ "op": "encode", outputs: ["tmp6", "tmp7"], var: "pk.right" },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x11", "0x1", "0x1", "0x20", "tmp6", "tmp7"] },
    { "op": "declare_pub_inputs", "guard": "v13", "inputs": ["0x91"] },
    { "op": "declare_pub_inputs", "inputs": ["0x30"] },
    { "op": "declare_pub_inputs", "inputs": ["0x50", "0x1", "0x1", "0x5"] },
    { "op": "public_input", "output": "v41" },
    { "op": "declare_pub_inputs", "inputs": ["0xc", "0x1", "0x2", "v41"] },
    { "op": "hash_to_curve", "output": "colorBase", "inputs": ["coin.color", "v41"] },
    { "op": "ec_mul_generator", "output": "pedersenBlinding", "scalar": "rc" },
    { "op": "ec_mul", "output": "pedersenCommit", "a": "colorBase", "scalar": "coin.value" },
    { "op": "ec_add", "output": "v49", "a": "pedersenBlinding", "b": "pedersenCommit" },
    { "op": "declare_pub_inputs", "inputs": ["0x10", "0x1", "0x1", "0x1", "0x2"] },
	{ "op": "encode", "outputs": ["tmp8", "tmp9"], "var": "v49" },
    { "op": "declare_pub_inputs", "inputs": ["0x11", "0x1", "0x2", "-0x2", "-0x2", "tmp8", "tmp9"] },
    { "op": "declare_pub_inputs", "inputs": ["0x91"] },
  ]
}
```
