export type Field = {
  bytes: number;
  modulus: bigint;
};

export const ErisScalar: Field = {
  bytes: 56,
  modulus: BigInt("0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001"),
};

export const PlutoScalar: Field = {
  bytes: 56,
  modulus: BigInt("0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001"),
};

// Take little endian bytes representation and convert to a bigint
export function toScalar(bytes: Buffer): bigint {
  return BigInt(`0x${Buffer.from(bytes).reverse().toString("hex")}`);
}

// A little-endian bytes representation of a field element
export function fromScalar(scalar: bigint, padToField?: Field): Buffer {
  const stringified = scalar.toString(16);
  const padded = padToField != undefined ? stringified.padStart(padToField.bytes * 2, "0") : stringified;
  return Buffer.from(padded, "hex").reverse();
}
