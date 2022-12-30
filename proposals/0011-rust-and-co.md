# Proposal 0011: Compatibility between dependencies for Rust, JS and TS

This proposal discusses the issues of modularising our rust components, and how
we can push through to modularise anyway.

# Problem Statement

1. Who owns cryptographic operations and parameter choices that are shared
   between many components?
   * Elliptic curve being used
   * Scalar prime field
   * Embedded curve field
   * Hash function choice(s) and implementation
2. If rust crate `A` depends on `B`, and they expose TS APIs, how can the API
   of `A` handle types from `B`?
3. How can we support both nodeJS and WASM targets from rust without duplicate
   wrappers?

# Proposed Changes

1. Introduction of a `midnight-base-crypto` crate which can be used as a
   dependency by any other.
2. This is mainly a typesystem constraint: If the underlying rust libraries are
   the same, they will handle the same data.
   * Hand-write the TS API
   * Directly consume (untyped!) JS compiler output.
3. Only generate untyped JS compiler output.
   * Do not handle type conversions (leave that to the TS wrapper!)
   * Do not handle exceptions (leave that to the TS wrapper!)
   * All rust data structures as opaque data, all functions as operations on
     opaque rust data
   * Do not use library handling of builtin data types, exceptions etc
   * Push the remaining skeleton through both WASM and node-api generators.

# Desired Result

1. To be able to target WASM and Node-API with a flag change.
2. To be able to make changes to these targets in only one location.
3. To be able to have data dependencies between rust-compiled TS libraries.
