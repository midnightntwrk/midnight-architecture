import { describe, test } from "vitest";
import * as path from "node:path";
import * as fs from "node:fs";
import { generateTestVectors, seeds } from "./test-vectors.js";

const options = {
  dir:
    process.env.TEST_VECTORS_DIR ?? path.resolve(import.meta.dirname, "..", "..", "test-vectors"),
};

describe("Test vectors against reference implementation", () => {
  const vectorEntries = Object.entries(generateTestVectors(seeds));

  test.for(vectorEntries)("%s", ([name, values], { expect }) => {
    const pathToLoad = path.resolve(options.dir, `${name}.json`);
    const fromFile = JSON.parse(fs.readFileSync(pathToLoad, "utf-8"));

    expect(values).toEqual(fromFile);
  });
});
