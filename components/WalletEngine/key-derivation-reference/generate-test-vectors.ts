/**
 * A small CLI utility to generate test vectors for wallet keys given a set of predefined seeds
 */

import {
  coinKeys,
  encryptionSecretKey,
  Field,
  fromScalar,
  JubJubScalar,
  PlutoBase,
} from "./reference.js";
import { program, Option } from "commander";
import * as fs from "node:fs";
import * as jestDiff from "jest-diff";
import isEqual from "lodash-es/isEqual.js";

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
  Buffer.from(
    "e95875deebb99f0beb0a248fb11bc35a7aaa5be1fa07c3689b41eafa1f1cf7df",
    "hex",
  ),
  Buffer.from(
    "b981dbf119d815f3f1233fb97d2173e6788cac759269ada02cf42307328b91a8",
    "hex",
  ),
  Buffer.from(
    "b49408db310c043ab736fb57a98e15c8cedbed4c38450df3755ac9726ee14d0c",
    "hex",
  ),
  Buffer.from(
    "06004625b6cb2ccead21b15fee2a940c404365702b697b4721bfeecfc6b1b15e",
    "hex",
  ),
  Buffer.from(
    "215ca8a6923ec73f241c92ef702ccfc277aa5856bc94f59afa7e82ec94547850",
    "hex",
  ),
];

function generateTestVectors(seeds: Buffer[], field: Field) {
  return seeds.map((seed) => {
    const { key, intermediateBytes } = encryptionSecretKey(seed, field);
    const coinKeyPair = coinKeys(seed);
    return {
      seed: seed.toString("hex"),
      encryption: {
        secretKeyRepr: fromScalar(key, field).toString("hex"),
        secretKeyDecimal: key.toString(10),
        secretKeyIntermediateBytes: intermediateBytes.toString("hex"),
      },
      coin: {
        secretKey: coinKeyPair.secretKey.toString("hex"),
        publicKey: coinKeyPair.publicKey.toString("hex"),
      },
    };
  });
}

const fields = {
  JubJubScalar: JubJubScalar,
  PlutoBase: PlutoBase,
};

const fieldsOption = new Option("--field <field>", "What field to target")
  .choices(Object.keys(fields))
  .makeOptionMandatory(true);

program
  .description("Generate&test test vectors for key derivation")
  .showHelpAfterError();

program
  .command("gen", {
    isDefault: true,
  })
  .description(
    "Generate test vectors and print them, optionally saving to a file",
  )
  .option("--file <file>", "If and where to output generated vectors")
  .addOption(fieldsOption)
  .action((options) => {
    const field = fields[options.field];
    const values = generateTestVectors(seeds, field);
    const toPrint = JSON.stringify(values, null, 2);
    process.stdout.write(toPrint);
    process.stdout.write("\n");
    if (options.file) {
      fs.writeFileSync(options.file, toPrint, "utf-8");
    }
  });

program
  .command("test")
  .description("Test provided file against implementation")
  .requiredOption("--file <file>", "Where to look for vectors to test")
  .addOption(fieldsOption)
  .action((options) => {
    const field = fields[options.field];
    const values = generateTestVectors(seeds, field);
    const fromFile = JSON.parse(fs.readFileSync(options.file, "utf-8"));

    if (isEqual(values, fromFile)) {
      process.stderr.write(`${options.file} matches the implementation\n`);
    } else {
      const diff = jestDiff.diff(values, fromFile, {
        aAnnotation: "generated",
        bAnnotation: options.file,
        contextLines: 4,
      });
      process.stderr.write(`
Stored vectors do not match the implementation:
${diff}
`);
    }
  });

program.parse(process.argv);
