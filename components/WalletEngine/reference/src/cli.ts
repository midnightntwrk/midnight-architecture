/**
 * A small CLI utility to generate test vectors for wallet keys given a set of predefined seeds
 */

import * as ledger from "@midnight-ntwrk/ledger";
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
} from "./address-format-reference.js";
import { ErisScalar, fromScalar, PlutoScalar } from "./field.js";
import { coinKeys, dustSecretKey, encryptionSecretKey } from "./key-derivation-reference.js";

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
  Buffer.from("b49408db310c043ab736fb57a98e15c8cedbed4c38450df3755ac9726ee14d0c", "hex"), //random
  Buffer.from("06004625b6cb2ccead21b15fee2a940c404365702b697b4721bfeecfc6b1b15e", "hex"), //random
  Buffer.from("215ca8a6923ec73f241c92ef702ccfc277aa5856bc94f59afa7e82ec94547850", "hex"), //random
  Buffer.from("a2a1ef19b0ea7580f8ee5c96ef320001cccd280a40252c08160482505403bbcf", "hex"), //esk 36 bytes
  Buffer.from("bf1b28679110bec8dd00dfcd5f0ebced627201899ebd6bf8bc63bbfeda742c13", "hex"), //esk 35 bytes
  Buffer.from("543fc6d478ab5e43f6fb8afe6f671e70e113d579e899b7f27e11ae45ed4e94b5", "hex"), //esk 34 bytes
  Buffer.from("c024176f9266a23f49096275da2910028018128f3775d3b9ae95ebc7144d2549", "hex"), //esk 33 bytes
];

function generateKeyDerivationTestVectors(seeds: Buffer[]) {
  return seeds.map((seed) => {
    const esk = encryptionSecretKey(seed);
    const dsk = dustSecretKey(seed);
    const coinKeyPair = coinKeys(seed);
    return {
      seed: seed.toString("hex"),
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
    const keys = ledger.SecretKeys.fromSeed(seed);
    const coinKeyPair = coinKeys(seed);

    const shieldedAddressFormatter = mkFormatter({ networkId }, ShieldedAddress);
    const shieldedESKFormatter = mkFormatter({ networkId }, ShieldedEncryptionSecretKey);
    const shieldedCPKFormatter = mkFormatter({ networkId }, ShieldedCoinPublicKey);

    return {
      seed: seed.toString("hex"),
      networkId,
      shieldedAddress: shieldedAddressFormatter(
        new ShieldedAddress(new ShieldedCoinPublicKey(coinKeyPair.publicKey), Buffer.from(keys.encryptionPublicKey, "hex")),
      ),
      shieldedESK: shieldedESKFormatter(new ShieldedEncryptionSecretKey(keys.encryptionSecretKey)),
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
      type Keys = {
        seed: Buffer;
        spec: T;
        ledger: T;
        specBech32: string;
        ledgerBech32: string;
      };

      return (seeds: Observable<Buffer>) => {
        return rx.firstValueFrom(
          seeds.pipe(
            rx.map((seed): Keys => {
              const specKey = implSpec(seed);
              const ledgerKey = implZswap(seed);
              const specBech32 = toBech32(specKey).toString();
              const ledgerBech32 = toBech32(ledgerKey).toString();
              return { seed, spec: specKey, ledger: ledgerKey, specBech32, ledgerBech32 };
            }),
            rx.filter((keys) => {
              return !equals(keys.spec, keys.ledger) || keys.specBech32 != keys.ledgerBech32;
            }),
            rx.reduce((acc: Keys[], keys: Keys) => {
              return acc.concat([keys]);
            }, []),
          ),
        );
      };
    };

    const testRoundtrip =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T) =>
      (seeds: Observable<Buffer>) => {
        type Keys = {
          seed: Buffer;
          data: T;
          asBech32: string;
          fromBech32: T;
        };

        return rx.firstValueFrom(
          seeds.pipe(
            rx.map((seed) => {
              const data = implementation(seed);
              const asBech32 = toBech32(data).toString();
              const fromBech32 = data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(asBech32));
              return { seed, data, asBech32, fromBech32 };
            }),
            rx.filter((keys) => {
              return !equals(keys.data, keys.fromBech32);
            }),
            rx.reduce((acc: Keys[], keys: Keys) => acc.concat([keys]), []),
          ),
        );
      };

    const testWrongCredentialType =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T) =>
      (seeds: Observable<Buffer>) => {
        type Keys = {
          seed: Buffer;
          data: T;
          asBech32: MidnightBech32m;
          withChangedCredential: string;
        };

        return rx.firstValueFrom(
          seeds.pipe(
            rx.map((seed) => {
              const data = implementation(seed);
              const asBech32 = toBech32(data);
              const withChangedCredential = new MidnightBech32m("foo", asBech32.network, asBech32.data).toString();
              return { seed, data, asBech32, withChangedCredential };
            }),
            rx.filter((keys) => {
              try {
                keys.data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(keys.withChangedCredential));
                return true;
              } catch (e) {
                return false;
              }
            }),
            rx.reduce((acc: Keys[], keys: Keys) => acc.concat([keys]), []),
          ),
        );
      };

    const testWrongNetwork =
      <T extends { [Bech32m]: Bech32mCodec<T> }>(implementation: (seed: Buffer) => T) =>
      (seeds: Observable<Buffer>) => {
        type Keys = {
          seed: Buffer;
          data: T;
          asBech32: MidnightBech32m;
          withChangedNetwork: string;
        };

        return rx.firstValueFrom(
          seeds.pipe(
            rx.map((seed) => {
              const data = implementation(seed);
              const asBech32 = toBech32(data);
              const withChangedNetwork = new MidnightBech32m(asBech32.type, "foo", asBech32.data).toString();
              return { seed, data, asBech32, withChangedNetwork };
            }),
            rx.filter((keys) => {
              try {
                keys.data[Bech32m].decode({ networkId: null }, MidnightBech32m.parse(keys.withChangedNetwork));
                return true;
              } catch (e) {
                return false;
              }
            }),
            rx.reduce((acc: Keys[], keys: Keys) => acc.concat([keys]), []),
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
      const keys: ledger.SecretKeys = ledger.SecretKeys.fromSeed(seed);
      const coinKeyPair = coinKeys(seed);

      return { keys, coinKeyPair };
    };

    const saddrSpec = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedAddress(new ShieldedCoinPublicKey(keys.coinKeyPair.publicKey), Buffer.from(keys.keys.encryptionPublicKey, "hex"));
    };

    const saddrZswap = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedAddress(
        new ShieldedCoinPublicKey(Buffer.from(keys.keys.coinPublicKey, "hex")),
        Buffer.from(keys.keys.encryptionPublicKey, "hex"),
      );
    };

    const scpkSpec = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedCoinPublicKey(keys.coinKeyPair.publicKey);
    };

    const scpkZswap = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedCoinPublicKey(Buffer.from(keys.keys.coinPublicKey, "hex"));
    };

    const sesk = (seed: Buffer) => {
      const keys = keysFromSeed(seed);
      return new ShieldedEncryptionSecretKey(keys.keys.encryptionSecretKey);
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

    console.log(`Test result: ${gotFailure ? "FAILURE" : "PASS"}`);

    process.exit(gotFailure ? 1 : 0);
  });

program.command("find-seeds")
  .description("Find seeds generating varied length encryption secret keys")
  .action(async () => {
    const seedMap = new Map<number, {seed: string, esk: string}>;

    const insertIfNotPresent = <K, V>(map: Map<K, V>, key: K, value: V): void => {
      if(!map.has(key)) {
        map.set(key, value);
      }
    }

    while (seedMap.size < 4) {
      const seed = crypto.randomBytes(32);
      const keys = ledger.SecretKeys.fromSeed(seed);
      const esk = Buffer.from(keys.encryptionSecretKey.yesIKnowTheSecurityImplicationsOfThis_serialize(ledger.NetworkId.Undeployed));
      const length = esk.length;

      insertIfNotPresent(seedMap, length, {seed: seed.toString('hex'), esk: esk.toString('hex')});
    }

    console.log("Resulting map:")
    for (const [length, {seed, esk}] of seedMap.entries()) {
      console.log(`    length: ${length}\tseed: ${seed}\tesk: ${esk}`);
    }
    process.exit(0);

  })

program.parse(process.argv);
