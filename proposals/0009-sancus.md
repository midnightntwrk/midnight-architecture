# Proposal 0009: A modular API for proving systems

This proposal is for the creation of a new component (proposed name:
**Sancus**, after the Roman god of trust and honesty).

This component will be directly used by the following:
1. Midnight ledger, for creating and verifying proofs
2. Abcird, as a source language to be consumed by Sancus

# Problem Statement

Proving systems are tightly coupled with the language used to express circuits,
the format of statements and witnesses, and the witness generation process.
Further, they differ greatly in their API and usage.
This makes using a given proving system an all-or-nothing experience more often
than not. To help this, an API which allows for easy changes in the proving
system is desirable. Because circuit languages are usually coupled to proving
systems, this by necessity also involves translations between circuit,
statement, and witness languages.

# Proposed Changes

This proposal is for a *new library*, **Sancus**, which extensibly loads both
*proving systems* and *translation layers*.

## Components

Sancus consists of:

1. A central rust library, which may:
   1. Statically embed proving systems and translation layers, or
   2. Dynamically load proving systems and translations layers
2. A core ABI, which implements an RPC mechanism by which various proving
   systems or translation layers can be invoked
3. A set of (statically or dynamically linked) proving system modules.
4. A set of (statically or dynamically linked) translation layer modules.
5. A central C-API implemented by the central library, with two key operations:
   1. Take over the current process and service requests on stdin to stdout
      (with logging to stderr) nonblockingly
   2. Handle a single request blockingly

Focusing on a core ABI rather than API, along with a minimal C-API, hopefully
reduces the complexity of supporting many front-end languages.

The central library should catch aborts as far as possible, and respond with as
detailed error information as possible.

## Targets

Proving systems and languages are specified by a string name, e.g.

* `ark-groth16` (proving system)
* `ark-plonk` (proving system)
* `z/k` (proving system)
* `r1cs` (language)
* `abcird-transcript` (language)

Most of the time when interacting, a proving system, language, and a set of
parameters are targeted. Parameters are flags potentially associated with a
value. E.g.

* `curve=bls12-381`
* `field_modulus=52435875175126190479447740508185965837690552500527637822603658699938581184513`
* `poly_commit=sonic_kzg10`

A change in parameters usually means targeting a different compiled proving
system and translation layer. Parameters are accessible to both, and a proving
system / translation layer must provide a parameter-less function
`parameter_target` which takes a list of parameters and either:
1. Returns a unique identifier for the compiled variant of the library to use
   for this parameter set. If this is a dynamically loaded variant, at this
   point the dynamic library is found and loaded.
2. Rejects the parameter set as incompatible.

The retrieval of the parameter identifier should only be necessary to do once.

A proving system also defines a *default language*, via a parameter-less
`default_language` function. Similarly, each language must define a *trivial
proving system* (via `trivial_proving_system`) which implements language
semantics without cryptography (this may be automatically used to implement
parts of translations?)

Finally, a pair of language identifier `lang` and proving system identifier
`prv` is targeted. If the language identifier is the default language of the
proving system, the proving system's functions are called directly. Otherwise,
a translation layer `lang->prv.default_language()` is loaded, and used to
provide a translated ABI.

If the parameter `via=<a>,<b>,...` is present, multiple translation layers are
used: `lang-><a>`, `<a>-><b>`, ..., `<z>->prv.default_language()`. The `via`
parameter **must not** be handled by a proving system or language.

At any point, this resolution may fail due to a part not being implemented.

### Versions

At any point in time, a specific version of:
1. The ABI
2. The proving system
3. The language
is targeted. Each of these versions are defined through 2 non-negative
integers, a major and minor version. The call is valid if and only if:
1. The targeted proving system and language exist
2. All targeted versions have the same major version number as the available
   ones
3. All targeted versions have a minor version number at most the one available.

## High-level ABI design

Each ABI interaction represents a call, with a pair of language identifier and
proving system identifier as a target. All calls may be requested in blocking
of non-blocking mode. Some calls *must* be implemented by a proving system /
translation layer, some *may* be implemented, and some have *default
implementations*. Any proving system or language may also implement custom
queries, which should be callable.

Modules can be compiled with some of these operations disabled, for instance
due to not requiring proving operations on a verifier node.

### Core operations

The core operations are:

* `random_setup(rand) -> srs` -- produce an srs from a known randomness seed
* `srs_update(srs, rand) -> (srs', pi)` -- (optional) produce an SRS update
  from a known randomness seed on a given SRS
* `srs_update_aggregate(pi*) -> pi'` -- (optional) aggregate a list of SRS
  updates
* `srs_update_verify(srs, srs', pi) -> b` -- (optional) verify the correctness
  of an SRS update
* `compile(srs, circuit) -> pk` -- compile an circuit to prover key (including
  verifier key)
* `witness_generation_compile(circuit) -> witgen_data` -- compile a circuit to
  witness-generation instructions
* `verifier_key(pk) -> vk` -- extract verifier key from prover key
* `generate_witness(witgen_data, input) -> (statement, witness) | error` --
  perform witness generation and relationship check
* `prove(pk, statement, witness) -> pi | error` -- prove relation
* `verify(vk, statement, pi) -> b` -- verify proof
* `batch_verify(vk, statement*, pi*) -> b` -- batch verify proofs, default
  implementation through `verify`

Of the data objects, only `srs`, `rand` and `pi` are fully owned by the proving
system.

The objects `circuit`, `input`, `statement`, `witness` are purely defined by the
*language*, with `generate_witness` coming from the languages *trivial
implementation*.

`pk`, `vk` are owned *jointly* defined by the proving system, and the languages
used along the way. The core proving system defines a `pk` and `vk`, and each
language conversion may add metadata to `pk` and `vk` that assists with
converting `statement` and `witness` between languages.

### Conversion layer operations

A language conversion layer `A->B` must implement the following:

* `translate(circuitA) -> (circuitB, pk_metadataA, sourceMap)`
* `vk_metadata(pk_metadataA) -> vk_metadataA`
* `statement_translate(statementA, vk_metadataA) -> statementB`
* `witness_translate(statementA, witnessA, pk_metadataA) -> (statementB, witnessB)`

Where source map is a mapping of source location ranges in `circuitB` to
`circuitA`.

### Top-level ABI calls

As the main operations are parameterised by a language and proving system, the
top-level ABI has some additional functionality to talk about these.

* `proving_systems() -> [ps_name]` -- returns a list of proving systems
* `proving_system_info(ps_name) -> ...` -- returns supported parameters with
  description, native language, version, and available operations.
* `languages() -> [lang_name]` -- returns a list of supported languages with
  versions. The same language may be supported with different major versions.
* `language_info(lang_name, version) -> ...` -- returns supported parameters
  with description.
* `info() -> ...` -- returns version info, compile metadata, target
  architecture, etc.
* `load_proving_system(ps_name, version, parameters) -> psid` -- loads a given
  proving system with parameters, and returns the identifier
* `load_language(lang_name, lang_version, lang_parameters, target_name,
  target_version, target_parameters) -> langid` -- loads a given language
  translation layer, and returns the identifier
* All calls listed in Core Operations, supplied with `langid` and `psid`.

## Low-level ABI design

The ABI shall use a CBOR RPC design, with each message consisting of a single
CBOR object. Each message shall contain a protocol version, as well as a unique
request ID. Requests to a specific language/proving system pair shall also
contains versions for both. A final version of this proposal shall include a
CDDL specification for the CBOR.

## C API design

The top-level C API should be minimal:

```
struct result {
  uint64_t length;
  uint8_t *const buffer;
}
void serve_requests();
result handle_request(uint64_t length, uint8_t *const request_buffer);
void free_result(result *result);
```

This may also be compiled to an executable with `server_requests` as its entry
point, which runs the library as a CLI application.

We may need a separate top-level WASM API?

# Desired Result

Switching proving systems should be a matter of:
a) Implementing a new translation layer, and
b) Changing arguments in interacting with the unified proving system ABI.
