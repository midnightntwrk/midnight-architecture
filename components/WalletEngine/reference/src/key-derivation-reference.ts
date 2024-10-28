import * as crypto from "node:crypto";
import { ErisScalar, Field, PlutoScalar, toScalar } from "./field.js";

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

export function sampleKey(
  seed: Buffer,
  margin: number,
  domainSeparator: Buffer,
  field: Field,
): { intermediateBytes: Buffer; key: bigint } {
  // Generating some more bytes is important to get a better distribution of keys
  const sampledBytes = sampleBytes(field.bytes + margin, domainSeparator, seed);
  return {
    key: BigInt(toScalar(sampledBytes) % field.modulus),
    intermediateBytes: sampledBytes,
  };
}

export function encryptionSecretKey(seed: Buffer): {
  intermediateBytes: Buffer;
  key: bigint;
} {
  const field = ErisScalar;
  const domainSeparator = Buffer.from("midnight:esk", "utf-8");
  return sampleKey(seed, 8, domainSeparator, field);
}

export function dustSecretKey(seed: Buffer): {
  intermediateBytes: Buffer;
  key: bigint;
} {
  const field = PlutoScalar;
  const domainSeparator = Buffer.from("midnight:dsk", "utf-8");
  return sampleKey(seed, 8, domainSeparator, field);
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
