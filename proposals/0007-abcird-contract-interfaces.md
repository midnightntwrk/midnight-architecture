# Proposal 0007: Contract Interfaces in Abcird

This proposal suggests a means of specifying callable interface for external
contracts in Abcird.

# Problem Statement

The
[`claim_contract_call` public oracle
query](./0004-micro-adt-language.md#proposed-changes) should not be used
directly, but should instead be generated from another contract's public facing
interface, and the interactions with this resemble a function call in
high-level Abcird.

# Proposed Changes

## Adoption of TypeScript-style interfaces

In TypeScript, interfaces are essentially object types, but these may also define methods:

```ts
interface Foo {
  bar(baz: string): number;
}

let foo: Foo = ...;
foo.bar("baz");
```

I propose that we use adopt a similar notation in Abcird:
Allow declaring contract interfaces, with a `contract` keyword to distinguish
them, which consist of a sequence of method declarations. Objects of the
interface type allow using dot notation to call these methods.

## Use in calling contracts

Any variable with whose type is a `contract` interface will be treated as if it had the
type `ContractAddress`, which should be part of a standard library (and will be
an alias for `Field` for now), with exception of calls.

Dot-notation should be usable to call methods on such an interface variable:

```
contract Foo {
  foo(x: Field): Field;
}

circuit bar(a: Foo): Void {
  assert !(404 == a.foo(42)) "Meaning of life not found";
}
```

This notation should have the following meaningful effects in the Lares
backend, and the circuit:

### Lares backend

When a `<interface-variable>.<function>(args...)` form is processed:
1. A new environment should be started.
2. Information about the contract at address `<interface-variable>` fetched.
3. This contract's transition function `<function>` loaded.
4. This transition function called with `args...` passed as arguments to it.
5. Separate transcripts recorded for this transition function call.
6. The call should be added to the in-assembly transaction.
7. The original transactions environment is returned to, and the results returned as the value of the original `<interface-variable>.<function>(args...)` expression.
8. A random field element `<nonce>` is sampled with cryptographically-secure randomness.
9. A `claim_contract_call(<interface-variable>, <function>, comm)` public oracle call is made, where:
   * `args'` is the field-element representation of `args...` as `n` field elements.
   * `y` is the field-element representation of `<interface-variable>.<function>(args...)` as `m` field elements.
   * `comm := foldl H <nonce> (args' ++ y)`
   * `H` is defined as the built-in `transient_hash(a: Field, b: Field): Field` function.

### Circuit and transaction structure

In order to make sure that the `comm` values queried are meaningful, their correct computation
1. Needs to be ensured in-circuit
2. Needs to match a corresponding computation on the callee-contract's side.
3. Their `<nonce>` values must match.

To achieve this, each entry-point circuit will additionally a) receive
`<nonce>` via a witness function call, b) compute `comm` as above, and c)
declare `comm` as a public input.

```
circuit foo(x: Field): Field {
  ...
  return 42;
}
```

behaves like (pseudocode):

```
circuit foo(x: Field): Field {
  ...
  const result = 42;
  const comm = transient_hash(transient_hash(local$kernel$external_nonce(), x), result);
  declare_public_input(comm);
  return result;
}
```

Likewise,

```
contract Foo {
  foo(x: Field): Field;
}

circuit bar(a: Foo): Void {
  assert !(404 == a.foo(42)) "Meaning of life not found";
}
```

behaves like (pseudocode):

```
struct Foo { address: Field; }

circuit bar(a: Foo): Void {
  const result = local$kernel$call_result$Foo$foo();
  const nonce = local$kernel$fresh_nonce();
  const comm = transient_hash(transient_hash(nonce, 42), result);
  ledger$kernel$claim_contract_call(a.address, "foo", comm);
  assert !(404 == result) "Meaning of life not found";
  ...
}
```

Care must be taken to ensure that the nonces match up only in the case of one
call being the child of another.

# Desired Result

* It is possible to call another contract in a mostly intuitive way in high-level Abcird.
