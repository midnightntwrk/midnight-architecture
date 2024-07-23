import * as crypto from "node:crypto";

export type Field = {
  bytes: number;
  modulus: bigint;
};
export const JubJubScalar: Field = {
  bytes: 32,
  modulus: BigInt(
    "0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7",
  ),
};

export const ErisScalar: Field = {
  bytes: 56,
  modulus: BigInt(
    "0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001",
  ),
};

// Take little endian bytes representation and convert to a bigint
function toScalar(bytes: Buffer): bigint {
  return BigInt(`0x${Buffer.from(bytes).reverse().toString("hex")}`);
}

// A little-endian bytes representation of a field element
export function fromScalar(scalar: bigint, field: Field): Buffer {
  return Buffer.from(
    scalar.toString(16).padStart(field.bytes * 2, "0"),
    "hex",
  ).reverse();
}

function sha256(a: Buffer, b: Buffer): Buffer {
  return crypto.createHash("sha-256").update(a).update(b).digest();
}

function sampleBytes(
  bytes: number,
  domainSeparator: Buffer,
  seed: Buffer,
): Buffer {
  const rounds = Math.ceil(bytes / 32);
  const result = Buffer.alloc(bytes);
  for (let i = 0; i < rounds; i++) {
    const indexAsBytes = Buffer.alloc(8);
    indexAsBytes.writeBigUInt64LE(BigInt(i));
    const segment = sha256(domainSeparator, sha256(indexAsBytes, seed));
    segment.copy(result, i * 32); // last segment gets truncated if overflows
  }
  return result;
}

export function encryptionSecretKey(
  seed: Buffer,
  field: Field,
): { intermediateBytes: Buffer; key: bigint } {
  const domainSeparator = Buffer.from("midnight:esk", "utf-8");
  // Generating 8 bytes more is important to get a better distribution of keys
  const sampledBytes = sampleBytes(field.bytes + 8, domainSeparator, seed);
  return {
    key: BigInt(toScalar(sampledBytes) % field.modulus),
    intermediateBytes: sampledBytes,
  };
}

export function coinKeys(seed: Buffer): {
  secretKey: Buffer;
  publicKey: Buffer;
} {
  const secretKey = sha256(Buffer.from("midnight:csk", "utf-8"), seed);
  return {
    secretKey,
    publicKey: sha256(secretKey, Buffer.from("mdn:pk", "utf-8")),
  };
}
