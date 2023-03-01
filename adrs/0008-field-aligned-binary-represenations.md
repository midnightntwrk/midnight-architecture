# 8. Field-Aligned Binary Represenations

This proposal is to adopt the [Field-Aligned Binary
format](../apis-and-common-types/field-aligned-binary) for values passed in
transcripts, and stored in ADT state.

## Status

proposed

---
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2023-03-01                                                                                                                   |
| deciders  | Thomas Kerber                                                                                                                |
| consulted | Andrzej Kopeć, Kent Dybvig, Jon Rossie                                                                                       |
| informed  | Joseph Denman                                                                                                                |
---

## Context and Problem Statement

We need to represent data in-state, on-the-wire, and in-circuit. Field elements
are the only option in-circuit, but are liable to change. We need a long-term
format that we can easily transform to field elements, and that has a compact
on-the-wire representation.

## Decision Drivers

1. The selected format should be efficiently representable as a fixed-length
   sequence of field elements.
2. The field-element representation should require minimal in-circuit data
   decoding or re-encoding.
3. The selected format should have a compact on-the-wire representation.
4. The selected format should permit changing of the underlying field without
   invalidating any data (that does not conceptually depend on it).

## Considered Options

* Plain/compressed field elements, fails at point 4., as insufficient
  structural information is available. For instance, an `n`-length bytestring
  represented as `k` field elements cannot be translated to `k'` field elements
  without information that is should be a bytestring representation.
* Plain binary representation, fails at point 2., as it would require
  significant binary decoding in-field.
* The proposed [Field-Aligned Binary format](../apis-and-common-types/field-aligned-binary).
* Variants of Field-Aligned Binary without option segments. This is much
  simpler, but prevents us from efficiently representing sum types.

## Validation

Tests should be written that:
* The Abcird compiler outputs values adhering to the FAB specification.
* The Abcird runtime complies with the FAB specification.
