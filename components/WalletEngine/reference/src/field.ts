export type Field = {
  bytes: number;
  modulus: bigint;
};

export const BlsScalar: Field = {
  bytes: 32,
  modulus: BigInt(
    "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
  ),
}

export const JubjubScalar: Field = {
  bytes: 32,
  modulus: BigInt(
    "0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7",
  ),
};

// Take little endian bytes representation and convert to a bigint
export function toScalar(bytes: Buffer): bigint {
  return BigInt(`0x${Buffer.from(bytes).reverse().toString("hex")}`);
}

// A little-endian bytes representation of a field element
export function fromScalar(scalar: bigint, padToField?: Field): Buffer {
  const stringified = scalar.toString(16);
  const padded =
    padToField != undefined
      ? stringified.padStart(padToField.bytes * 2, "0")
      : stringified;
  return Buffer.from(padded, "hex").reverse();
}
