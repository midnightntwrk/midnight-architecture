/**
 * A small CLI utility to generate test vectors for wallet keys given a set of predefined seeds
 */

import * as ledger from "@midnight-ntwrk/ledger-v6";
import { program } from "commander";
import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";
import { generateTestVectors, seeds } from "./test-vectors.js";

program
  .description("Generate test vectors for key derivation and address formatting")
  .showHelpAfterError();

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
        fs.writeFileSync(
          path.resolve(options.dir, `${key}.json`),
          JSON.stringify(value, null, 2),
          "utf-8",
        );
      });
    }
  });

program
  .command("find-seeds")
  .description("Find seeds generating varied length encryption secret keys")
  .action(async () => {
    const seedMap = new Map<number, { seed: string; esk: string }>();

    const insertIfNotPresent = <K, V>(map: Map<K, V>, key: K, value: V): void => {
      if (!map.has(key)) {
        map.set(key, value);
      }
    };

    while (seedMap.size < 4) {
      const seed = crypto.randomBytes(32);
      const keys = ledger.ZswapSecretKeys.fromSeed(seed);
      const esk = Buffer.from(
        keys.encryptionSecretKey.yesIKnowTheSecurityImplicationsOfThis_serialize(),
      );
      const length = esk.length;

      insertIfNotPresent(seedMap, length, { seed: seed.toString("hex"), esk: esk.toString("hex") });
    }

    console.log("Resulting map:");
    for (const [length, { seed, esk }] of seedMap.entries()) {
      console.log(`    length: ${length}\tseed: ${seed}\tesk: ${esk}`);
    }
    process.exit(0);
  });

program.parse(process.argv);
