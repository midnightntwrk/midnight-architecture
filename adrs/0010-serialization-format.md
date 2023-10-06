# 10. Serialization Format

## Status

proposed

| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2023-04-17                                                                                                                       |
| deciders  | Thomas Kerber, Jon Rossie, Alberto Garoffolo |
| consulted | Dmitry Voronov, Vincent Hanquez |
---

## Context and Problem Statement

We need a serialization format for use in Midnight-defined data structures. In
particular, this format needs to be applied to transactions, and serialized
representations of contract states.

This ADR *will not* focus on the public oracle language, or the representation
of raw values stored in contract states, and will assume these have a
separately defined encoding.

## Decision Drivers

* We need to work with Substrate
* We want deterministic encoding of values, that is each value has only one valid encoding
* The format should be easy to use from rust
* Writing an encoder/decoder should require minimal effort
* The format should not be self-describing, and be a compact binary format

## Considered Options

* JSON (via serde-json)
* CBOR (via serde/ciborium)
* Borsh
* SCALE

## Decision Outcome

Chosen option: Borsh, with custom encodings for specific types (see below), because:
* Borsh is well-specified, and easily extensible
* Borsh and SCALE are the only reviewed options that are deterministic and not self-describing
* Custom extensions because:
  * Borsh does not have a compact encoding for large integers, and we need field elements.
* Crypto primitives other than field elements (e.g. proofs, curve points, etc.)
  encoded as bytestrings of the underlying system.
* SCALE is used internally by substrate, however any the two encodings are very
  close.
* SCALE is not needed except at the substrate storage level, which is
  explicitly not covered in this document.
* SCALE is less-well specified than Borsh, and does not specify encodings for
  sets or maps, which are both key data structures.

Encoding field elements `f` as:
* `bytelen(f) as u8`
* `little_endian(f)`
where `bytelen` and `little_endian` operate on the shortest little-endian
encoding possible for `f`.

### Positive Consequences

* Clarity over on-the-wire encoding of transactions
* Increase compactness of on-the-wire encodings
* Clear encoding specification, that can easily be re-implemented
* Stop relying on different, possibly untested encodings.

### Negative Consequences

* Confusing mix of serialization:
  * Requires us to sometimes with with Borsh, and sometimes with SCALE
  * JavaScript encodings for Abcird's runtime will also require us to sometimes
    define a serde-js encoding

## Validation

By review that transaction serialization conforms to the Borsh specification.
