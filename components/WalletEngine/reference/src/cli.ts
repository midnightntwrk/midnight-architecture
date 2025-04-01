/**
 * A small CLI utility to generate test vectors for wallet keys given a set of predefined seeds
 */

import * as zswap from "@midnight-ntwrk/zswap";
import { program } from "commander";
import * as jestDiff from "jest-diff";
import isEqual from "lodash-es/isEqual.js";
import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";
import { Observable } from "rxjs";
import * as rx from "rxjs";
import {
  Bech32m,
  Bech32mCodec,
  FormatContext,
  MidnightBech32m,
  ShieldedAddress,
  ShieldedCoinPublicKey,
  ShieldedEncryptionSecretKey,
  UnshieldedAddress,
} from "./address-format-reference.js";
import { ErisScalar, fromScalar, PlutoScalar } from "./field.js";
import { coinKeys, dustSecretKey, encryptionSecretKey, unshieldedKeyPairFromUniformBytes } from "./key-derivation-reference.js";

const networkIds = [null, "my-private-net", "dev", "test", "my-private-net-5"]; //null stands for mainnet
const seeds = [
  Buffer.alloc(32, 0),
  Buffer.alloc(32, 1),
  Buffer.alloc(32, 2),
  Buffer.alloc(32, 4),
  Buffer.alloc(32, 8),
  Buffer.alloc(32, 16),
  Buffer.alloc(32, 32),
  Buffer.alloc(32, 64),
  Buffer.alloc(32, 255),
  Buffer.from("b49408db310c043ab736fb57a98e15c8cedbed4c38450df3755ac9726ee14d0c", "hex"),
  Buffer.from("06004625b6cb2ccead21b15fee2a940c404365702b697b4721bfeecfc6b1b15e", "hex"),
  Buffer.from("215ca8a6923ec73f241c92ef702ccfc277aa5856bc94f59afa7e82ec94547850", "hex"),
  Buffer.from(
    //It forces esk to be 54 bytes long serialized
    "cfe40bcac30e818d3d4d35d79846b2df2f45c1bde9b7c2d8070095729d769af3",
    "hex",
  ),
  Buffer.from(
    //It forces esk to be 55 bytes long serialized
    "97b43b7a3747b7f70491fe089c56fe1f6d01e602b7a3ec09cda89d7de324b7e9",
    "hex",
  ),
];

function generateKeyDerivationTestVectors(seeds: Buffer[]) {
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
        secretKeyRepr: fromScalar(esk.key, ErisScalar).toString("hex"),
        secretKeyDecimal: esk.key.toString(10),
        secretKeyIntermediateBytes: esk.intermediateBytes.toString("hex"),
      },
      dust: {
        secretKeyRepr: fromScalar(dsk.key, PlutoScalar).toString("hex"),
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

function generateAddressFormattingTestVectors(seeds: Buffer[]) {
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
    // @ts-ignore
    const state: zswap.LocalState = zswap.LocalState.fromSeedSpec(seed);
    const coinKeyPair = coinKeys(seed);
    const unshieldedKeyPair = unshieldedKeyPairFromUniformBytes(seed);

    const shieldedAddressFormatter = mkFormatter({ networkId }, ShieldedAddress);
    const shieldedESKFormatter = mkFormatter({ networkId }, ShieldedEncryptionSecretKey);
    const shieldedCPKFormatter = mkFormatter({ networkId }, ShieldedCoinPublicKey);
    const unshieldedAddressFormatter = mkFormatterNullable(mkFormatter({ networkId }, UnshieldedAddress));

    return {
      seed: seed.toString("hex"),
      networkId,
      unshieldedAddress: unshieldedAddressFormatter(
        unshieldedKeyPair.publicKey ? new UnshieldedAddress(crypto.hash("sha-256", unshieldedKeyPair.publicKey, "buffer")) : null,
      ),
      shieldedAddress: shieldedAddressFormatter(
        new ShieldedAddress(new ShieldedCoinPublicKey(coinKeyPair.publicKey), Buffer.from(state.encryptionPublicKey, "hex")),
      ),
      shieldedESK: shieldedESKFormatter(new ShieldedEncryptionSecretKey(state.yesIKnowTheSecurityImplicationsOfThis_encryptionSecretKey())),
      shieldedCPK: shieldedCPKFormatter(new ShieldedCoinPublicKey(coinKeyPair.publicKey)),
    };
  });
}

function generateTestVectors(seeds: Buffer[]) {
  return {
    keyDerivation: generateKeyDerivationTestVectors(seeds),
    addresses: generateAddressFormattingTestVectors(seeds),
  };
}

program.description("Generate&test test vectors for key derivation and address formatting").showHelpAfterError();

program
  .command("gen", {
    isDefault: true,
  })
  .description("Generate test vectors and print them or save to a file")
  .option("--dir <dir>", "If and where to output generated vectors")
  .option("--print", "Whether to print generated values", false)
  .action((options) => {
    const results = generateTestVectors(seeds);
    if (options.print) {
      process.stdout.write(JSON.stringify(results, null, 2));
      process.stdout.write("\n");
    }

    if (options.dir) {
      Object.entries(results).forEach(([key, value]) => {
        fs.mkdirSync(options.dir, { recursive: true });
        fs.writeFileSync(path.resolve(options.dir, `${key}.json`), JSON.stringify(value, null, 2), "utf-8");
      });
    }
  });

program
  .command("test-vectors")
  .description("Test vectors from file against implementation")
  .requiredOption("--dir <dir>", "Where to look for vectors to test")
  .action((options) => {
    Object.entries(generateTestVectors(seeds)).forEach(([name, values]) => {
      const pathToLoad = path.resolve(options.dir, `${name}.json`);
      const fromFile = JSON.parse(fs.readFileSync(pathToLoad, "utf-8"));

      if (isEqual(values, fromFile)) {
        process.stderr.write(`${name} loaded from ${pathToLoad} matches the implementation\n`);
      } else {
        const diff = jestDiff.diff(values, fromFile, {
          aAnnotation: "generated",
          bAnnotation: options.file,
          contextLines: 4,
        });
        process.stderr.write(`
Stored vectors of ${name} and loaded from ${pathToLoad} do not match the implementation:
${diff}
`);
      }
    });
  });

program
  .command("test-addr")
  .description("Tests address format implementation")
  .action(async () => {
    const initial = (): number => {
      return Math.ceil((Math.random() * Number.MAX_SAFE_INTEGER) / 2);
    };
    const generateSeeds = (initialSeed: number, amount: number): Observable<Buffer> => {
      return rx.range(initialSeed, amount).pipe(
        rx.map((i) => crypto.hash("sha256", i.toString(16).padStart(32 * 2, "0"), "buffer")),
        rx.shareReplay(),
      );
    };

    const toBech32 = <T extends { [Bech32m]: Bech32mCodec<T> }>(data: T): MidnightBech32m => {
      return data[Bech32m].encode({ networkId: null }, data);
    };

    const equals = <T extends { [Bech32m]: Bech32mCodec<T> }>(a: T, b: T): boolean => {
      return a[Bech32m].dataToBytes(a).equals(b[Bech32m].dataToBytes(b));
    };

    const testParity = <T extends { [Bech32m]: Bech32mCodec<T> }>(implSpec: (seed: Buffer) => T, implZswap: (seed: Buffer) => T) => {
      return (seeds: Observable<Buffer>) => {
        return rx.firstValueFrom(
          seeds.pipe(
            rx.map((seed) => {
              const spec = implSpec(seed);
              const zswap = implZswap(seed);
              const specBech32 = toBech32(spec).toString();
              const zswapBech32 = toBech32(zswap).toString();
              return { seed, spec, zswap, specBech32, zswapBech32 };
            }),
            rx.filter((keys) => {
              return !equals(keys.spec, keys.zswap) || keys.specBech32 != keys.zswapBech32;
            }),
            rx.reduce((acc: Array<{ seed: Buffer; spec: T; zswap: T; specBech32: string; zswapBech32: string }>, keys) => {
              return acc.concat([keys]);
            }, []),
          ),
        );
      };
    };

    const testRoundtrip =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T | null) =>
      (seeds: Observable<Buffer>) => {
        return rx.firstValueFrom(
          seeds.pipe(
            rx.concatMap((seed) => {
              const data = implementation(seed);

              if (data == null) {
                return [];
              }

              const asBech32 = toBech32(data).toString();
              const fromBech32 = data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(asBech32));
              return [{ seed, data, asBech32, fromBech32 }];
            }),
            rx.filter((keys) => {
              return !equals(keys.data, keys.fromBech32);
            }),
            rx.reduce((acc: Array<{ seed: Buffer; data: T; asBech32: string; fromBech32: T }>, keys) => acc.concat(keys), []),
          ),
        );
      };

    const testWrongCredentialType =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T | null) =>
      (seeds: Observable<Buffer>) => {
        return rx.firstValueFrom(
          seeds.pipe(
            rx.concatMap((seed) => {
              const data = implementation(seed);

              if (data == null) {
                return [];
              }

              const asBech32 = toBech32(data);
              const withChangedCredential = new MidnightBech32m("foo", asBech32.network, asBech32.data).toString();
              return [{ seed, data, asBech32, withChangedCredential }];
            }),
            rx.filter((keys) => {
              try {
                keys.data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(keys.withChangedCredential));
                return true;
              } catch (e) {
                return false;
              }
            }),
            rx.reduce(
              (acc: Array<{ seed: Buffer; data: T; asBech32: MidnightBech32m; withChangedCredential: string }>, keys) => acc.concat(keys),
              [],
            ),
          ),
        );
      };

    const testWrongNetwork =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T | null) =>
      (seeds: Observable<Buffer>) => {
        return rx.firstValueFrom(
          seeds.pipe(
            rx.concatMap((seed) => {
              const data = implementation(seed);

              if (data == null) {
                return [];
              }

              const asBech32 = toBech32(data);
              const withChangedNetwork = new MidnightBech32m(asBech32.type, "foo", asBech32.data).toString();
              return [{ seed, data, asBech32, withChangedNetwork }];
            }),
            rx.filter((keys) => {
              try {
                keys.data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(keys.withChangedNetwork));
                return true;
              } catch (e) {
                return false;
              }
            }),
            rx.reduce(
              (acc: Array<{ seed: Buffer; data: T; asBech32: MidnightBech32m; withChangedNetwork: string }>, keys) => acc.concat(keys),
              [],
            ),
          ),
        );
      };

    let gotFailure = false;
    const doTest = async <T>(name: string, testFunction: (seeds: Observable<Buffer>) => Promise<T[]>, seeds: Observable<Buffer>) => {
      console.group(name);
      const failures = await testFunction(seeds);
      if (failures.length == 0) {
        console.log(`PASS`);
      } else {
        gotFailure = true;
        console.log(`FAILURE`);
        console.group();
        failures.forEach((d) => console.log(d));
        console.groupEnd();
      }
      console.groupEnd();
    };

    const keysFromSeed = (seed: Buffer) => {
      // @ts-ignore
      const state: zswap.LocalState = zswap.LocalState.fromSeedSpec(seed);
      const coinKeyPair = coinKeys(seed);

      return { state, coinKeyPair };
    };

    const saddrSpec = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedAddress(new ShieldedCoinPublicKey(keys.coinKeyPair.publicKey), Buffer.from(keys.state.encryptionPublicKey, "hex"));
    };

    const saddrZswap = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedAddress(
        new ShieldedCoinPublicKey(Buffer.from(keys.state.coinPublicKey, "hex")),
        Buffer.from(keys.state.encryptionPublicKey, "hex"),
      );
    };

    const scpkSpec = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedCoinPublicKey(keys.coinKeyPair.publicKey);
    };

    const scpkZswap = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedCoinPublicKey(Buffer.from(keys.state.coinPublicKey, "hex"));
    };

    const sesk = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedEncryptionSecretKey(keys.state.yesIKnowTheSecurityImplicationsOfThis_encryptionSecretKey());
    };

    const unshieldedAddr = (seed: Buffer) => {
      const keys = unshieldedKeyPairFromUniformBytes(seed);
      return keys.publicKey != null ? new UnshieldedAddress(crypto.hash("sha-256", keys.publicKey, "buffer")) : null;
    };

    const seeds = generateSeeds(initial(), 1_000);

    await doTest("Shielded address parity", testParity(saddrSpec, saddrZswap), seeds);

    await doTest("Shielded coin key parity", testParity(scpkSpec, scpkZswap), seeds);

    await doTest("Shielded address spec roundtrip", testRoundtrip(saddrSpec), seeds);
    await doTest("Shielded address zswap roundtrip", testRoundtrip(saddrZswap), seeds);
    await doTest("Shielded coin public key spec roundtrip", testRoundtrip(scpkSpec), seeds);
    await doTest("Shielded coin public key zswap roundtrip", testRoundtrip(scpkZswap), seeds);
    await doTest("Shielded encryption secret key roundtrip", testRoundtrip(sesk), seeds);

    await doTest("Shielded address spec wrong credential type", testWrongCredentialType(saddrSpec), seeds);
    await doTest("Shielded address zswap wrong credential type", testWrongCredentialType(saddrZswap), seeds);
    await doTest("Shielded coin public key spec wrong credential type", testWrongCredentialType(scpkSpec), seeds);
    await doTest("Shielded coin public key zswap wrong credential type", testWrongCredentialType(scpkZswap), seeds);
    await doTest("Shielded encryption secret key wrong credential type", testWrongCredentialType(sesk), seeds);

    await doTest("Shielded address spec wrong network", testWrongNetwork(saddrSpec), seeds);
    await doTest("Shielded address zswap wrong network", testWrongNetwork(saddrZswap), seeds);
    await doTest("Shielded coin public key spec wrong network", testWrongNetwork(scpkSpec), seeds);
    await doTest("Shielded coin public key zswap wrong network", testWrongNetwork(scpkZswap), seeds);
    await doTest("Shielded encryption secret key wrong network", testWrongNetwork(sesk), seeds);

    // TODO: add parity test once ledger releases version with unshielded tokens implementation
    await doTest("Unshielded address roundtrip", testRoundtrip(unshieldedAddr), seeds);
    await doTest("Unshielded address wrong credential type", testWrongCredentialType(unshieldedAddr), seeds);
    await doTest("Unshielded address wrong network", testWrongNetwork(unshieldedAddr), seeds);

    console.log(`Test result: ${gotFailure ? "FAILURE" : "PASS"}`);

    process.exit(gotFailure ? 1 : 0);
  });

program.parse(process.argv);
