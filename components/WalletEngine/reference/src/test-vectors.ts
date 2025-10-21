import {
  FormatContext,
  Bech32mCodec,
  ShieldedAddress,
  ShieldedEncryptionSecretKey,
  ShieldedCoinPublicKey,
  DustAddress,
  UnshieldedAddress,
} from "./address-format-reference.js";
import { fromScalar, JubJubScalar, BLSScalar } from "./field.js";
import {
  encryptionSecretKey,
  dustSecretKey,
  coinKeys,
  unshieldedKeyPairFromUniformBytes,
  dustKeys,
} from "./key-derivation-reference.js";
import * as ledger from "@midnight-ntwrk/ledger-v6";
import * as crypto from "node:crypto";

export const networkIds = [null, "my-private-net", "dev", "test", "my-private-net-5"]; //null stands for mainnet
export const seeds = [
  Buffer.alloc(32, 0),
  Buffer.alloc(32, 1),
  Buffer.alloc(32, 2),
  Buffer.alloc(32, 4),
  Buffer.alloc(32, 8),
  Buffer.alloc(32, 16),
  Buffer.alloc(32, 32),
  Buffer.alloc(32, 64),
  Buffer.alloc(32, 255),
  Buffer.from("b49408db310c043ab736fb57a98e15c8cedbed4c38450df3755ac9726ee14d0c", "hex"), //random
  Buffer.from("06004625b6cb2ccead21b15fee2a940c404365702b697b4721bfeecfc6b1b15e", "hex"), //random
  Buffer.from("215ca8a6923ec73f241c92ef702ccfc277aa5856bc94f59afa7e82ec94547850", "hex"), //random
  Buffer.from("a2a1ef19b0ea7580f8ee5c96ef320001cccd280a40252c08160482505403bbcf", "hex"), //esk 36 bytes
  Buffer.from("bf1b28679110bec8dd00dfcd5f0ebced627201899ebd6bf8bc63bbfeda742c13", "hex"), //esk 35 bytes
  Buffer.from("543fc6d478ab5e43f6fb8afe6f671e70e113d579e899b7f27e11ae45ed4e94b5", "hex"), //esk 34 bytes
  Buffer.from("c024176f9266a23f49096275da2910028018128f3775d3b9ae95ebc7144d2549", "hex"), //esk 33 bytes
];

export function generateKeyDerivationTestVectors(seeds: Buffer[]) {
  return seeds.map((seed) => {
    const esk = encryptionSecretKey(seed);
    const dsk = dustSecretKey(seed);
    const coinKeyPair = coinKeys(seed);
    const unshieldedKeyPair = unshieldedKeyPairFromUniformBytes(seed); //In this case the seed is the secret key, matching HD Wallet behavior
    return {
      seed: seed.toString("hex"),
      unshielded: {
        secretKey: unshieldedKeyPair.secretKey?.toString("hex") ?? null,
        publicKey: unshieldedKeyPair.publicKey?.toString("hex") ?? null,
      },
      encryption: {
        secretKeyRepr: fromScalar(esk.key, JubJubScalar).toString("hex"),
        secretKeyDecimal: esk.key.toString(10),
        secretKeyIntermediateBytes: esk.intermediateBytes.toString("hex"),
      },
      dust: {
        secretKeyRepr: fromScalar(dsk.key, BLSScalar).toString("hex"),
        secretKeyDecimal: dsk.key.toString(10),
        secretKeyIntermediateBytes: dsk.intermediateBytes.toString("hex"),
      },
      coin: {
        secretKey: coinKeyPair.secretKey.toString("hex"),
        publicKey: coinKeyPair.publicKey.toString("hex"),
      },
    };
  });
}

export function generateAddressFormattingTestVectors(seeds: Buffer[]) {
  const mkFormatterNullable =
    <T>(formatter: (item: T) => { hex: string; bech32m: string }) =>
    (item: null | T): { hex: string | null; bech32m: string | null } => {
      return item == null ? { hex: null, bech32m: null } : formatter(item);
    };

  const mkFormatter =
    <T>(
      context: FormatContext,
      type: {
        codec: Bech32mCodec<T>;
      },
    ) =>
    (item: T): { hex: string; bech32m: string } => {
      return {
        hex: type.codec.dataToBytes(item).toString("hex"),
        bech32m: type.codec.encode(context, item).toString(),
      };
    };

  const contexts = seeds.flatMap((seed) => networkIds.map((networkId) => ({ seed, networkId })));
  return contexts.map(({ seed, networkId }) => {
    const shieldedKeys = ledger.ZswapSecretKeys.fromSeed(seed);
    const coinKeyPair = coinKeys(seed);
    const esk = encryptionSecretKey(seed);
    const unshieldedKeyPair = unshieldedKeyPairFromUniformBytes(seed);
    const dustKeyPair = dustKeys(seed);

    const shieldedAddressFormatter = mkFormatter({ networkId }, ShieldedAddress);
    const shieldedESKFormatter = mkFormatter({ networkId }, ShieldedEncryptionSecretKey);
    const shieldedCPKFormatter = mkFormatter({ networkId }, ShieldedCoinPublicKey);
    const dustAddressFormatter = mkFormatter({ networkId }, DustAddress);
    const unshieldedAddressFormatter = mkFormatterNullable(
      mkFormatter({ networkId }, UnshieldedAddress),
    );

    return {
      seed: seed.toString("hex"),
      networkId,
      unshieldedAddress: unshieldedAddressFormatter(
        unshieldedKeyPair.publicKey
          ? new UnshieldedAddress(crypto.hash("sha-256", unshieldedKeyPair.publicKey, "buffer"))
          : null,
      ),
      shieldedAddress: shieldedAddressFormatter(
        new ShieldedAddress(
          new ShieldedCoinPublicKey(coinKeyPair.publicKey),
          Buffer.from(shieldedKeys.encryptionPublicKey, "hex"),
        ),
      ),
      dustAddress: dustAddressFormatter(new DustAddress(dustKeyPair.publicKey)),
      shieldedESK: shieldedESKFormatter(new ShieldedEncryptionSecretKey(esk.key)),
      shieldedCPK: shieldedCPKFormatter(new ShieldedCoinPublicKey(coinKeyPair.publicKey)),
    };
  });
}

export function generateTestVectors(seeds: Buffer[]) {
  return {
    keyDerivation: generateKeyDerivationTestVectors(seeds),
    addresses: generateAddressFormattingTestVectors(seeds),
  };
}
