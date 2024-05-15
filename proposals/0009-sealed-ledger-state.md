# Proposal 0009: Sealed Ledger State

This document proposes changes to the Compact syntax and Midnight ledger to support ledger state that is fixed at contract deployment time and immutable thereafter.

## Problem Statement

The representation of contract state in the Midnight ledger is functional, in the sense that each transaction produces a replacement state for the contract.
The "shape" of the replacement state is effectively constrained by the operations that must succeed on that state,
and further constrained in practice by the kinds of updates that can be expressed in the Compact language.

Contract state is currently represented by a vector of values, each of which is one of a fixed set of ADTs.
A transaction can "update" the state through well-defined, functionally implemented operations on these ADTs,
and the Impact VM ends the transaction by producing a new state vector to represent the contract state.

What is missing from this system is direct support for establishing a portion of the contract's state
which is *sealed* at the time the contract is deployed, with the guarantee that it can never be changed
in any post-deployment transaction.

The sealed portion of the state is not truly "constant" or "immutable" in the usual programmatic senses,
because it may be constructed incrementally in the contract's constructor using the ADTs' update operations,
but the Impact VM will never replace the sealed portion of the state after the contract is deployed.
This provides safety guarantees for contract users and opportunities for optimization by the Compact compiler.

While the preceding description of the need and outline for a solution is expressed in terms of the ledger
data structures, the contract writer's experience of sealed state is determined largely by how
such sealing is expressed in Compact.  Thus, this proposal focuses on the changes to Compact to
enable sealed state.  The actual changes to the ledger data structures could be implemented
at any point after the changes to the compiler and runtime libraries.

## Semantic Model

The ledger currently (prior to this proposal) maps contract addresses to contract states,
and a contract state holds a single state value, updated by transactions.

Under the semantic model of this proposal, the contract state will hold two values,
one fixed at deployment time and one updated by transactions.
This semantic model is reflected in Compact, regardless of whether the physical implementation of the ledger matches it.
(Of course, greater safety is enabled by enforcing sealed state in the ledger, and not only in the compiler.)

## Syntax Changes

The ledger declaration grammar currently defines a single ledger declaration
as one of the valid program elements:

```
PELT      --> LDECL

LDECL     --> ledger { LDECL-ELT ... }

LDECL-ELT --> ID : LEDGER-ADT ;
          --> constructor ( ARG, ARG, ... ) BLOCK
```

As part of this proposal, the ledger state declarations become separable
(that is, not all inside a single pair of curly braces),
and it becomes the compiler's responsibility to gather them together
to create the total ledger state for the contract.

```
PELT      --> LDECL
          --> CONSDEFN

LDECL     --> EXPORT^OPT SEALED^OPT ledger ID : LEDGER-ADT ;

SEALED    --> sealed

EXPORT    --> export

CONSDEFN  --> constructor ( ARG, ARG, ... ) BLOCK
```

Thus, the `sealed` keyword can appear as an optional modifier on a `ledger` field declaration,
in addition to the optional `export` modifier.

As before, the definition of a constructor is not mandatory, and only one constructor
definition is allowed to appear in a program.
Any ledger state fields not initialized explicitly in a constructor
are initialized to their default values.

There need not be any ledger fields declared at all.  A contract with zero ledger declarations is valid.

Any module definition can contain the same kind of program elements that can appear
at the top level of a program, except for CONSDEFN.

Any ledger state declared in a module is included in a contract's ledger if the
module is imported (directly or indirectly) into the contract's top level,
*even if the ledger state is not exported from the module*.
However, any ledger state that is declared in a module but not exported from the module
is visible only to circuits defined within the module.
This allows access to the ledger state to be controlled only by the
circuits within the module.
Explicit initialization of a module's unexported ledger state can be handled by a user-defined initialization
circuit that is exported from the module and called by the constructor.

Inspection of ledger field values via the `ledger` function defined in the generated
JavaScript code is possible for and only for those named by top-level exports of the
program (contract, if the composable contracts proposal is adopted).
This gives the Compact programmer control over field visibilty and forces the programmer
to choose unique names for ledger fields that need to be directly visible from
TypeScript or JavaScript.

### Rationale

The keyword `sealed` is proposed, rather than `constant` or `immutable`,
because the limitation on mutation begins at contract deployment time,
not immediately upon declaration.

Additional uses of the `sealed` keyword are envisioned in Compact in other contexts.
For example, if it becomes possible to declare subtypes of enumerations or
of (proposed) contract interfaces, then the `sealed` modifier may limit the
allowed subtyping to what is statically present in the same scope.

The incremental declaration of ledger state fields allows fields and related circuits
to be introduced with `include`, better supporting code reuse.

## Ledger State ADT Changes

The set of operations on each ledger state ADT must be partitioned
into *read* operations and *write* operations.
The read-write distinction must be known to the Compact compiler,
for static analysis purposes.  It must also be made clear in the
documentation describing ledger state ADTs.

## Elimination of `Cell` Syntax

(This change is at the intersection of Compact syntactic changes and ADT changes,
so it is described in its own section.)

Any `ledger` state field declaration of type *T*, where *T* is a primitive Compact type or user-defined type
(not a ledger ADT type), that is *not* modified with `sealed` is inherently writable.
Thus, the need for the `Cell` ADT "behind the scenes" to implement such a field can be inferred reliably
by the compiler.  There is no need for the contract author to declare the use of the `Cell` ADT explicitly,
and it should be removed from the syntax of Compact.

The compiler may implement sealed primitive-type fields with `Cell` also, if it is convenient to do so.

## Static Analysis and Type System Changes

Ledger state field declarations and circuit definitions may be interleaved.
Forward references are allowed.

If a ledger state field is declared with the `sealed` modifier,
then *write* operations may occur only in the context of the contract's constructor,
but not in later transactions.
*Read* operations may occur in both constructor and circuit transaction contexts.

Thus, code appearing in an *exported* circuit that might update a sealed field
would produce a compile-time error, because such a circuit could be called
in a post-deployment transaction.

For non-exported circuits, the situation is more complicated.
- A non-exported circuit that is statically known to be called *only* in the context
  of a constructor for some contract is allowed to update the sealed ledger state fields
  of that contract.
- A non-exported circuit that might be called, even indirectly, outside the context of
  a contract's constructor is *not* allowed to update that contract's sealed ledger state fields.

## Examples

### Bulletin Board Contract

The `ledger` portion of the bulletin board contract described in the Midnight developer tutorial
is as follows in the current Compact syntax (i.e., prior to the acceptance of this proposal):

```compact
ledger {
    state: Cell[STATE];
    message: Cell[Maybe[Opaque["string"]]];
    instance: Counter;
    poster: Cell[Bytes[32]];
    constructor() {
        ledger.state = STATE.vacant;
        ledger.message = none[Opaque["string"]]();
        ledger.instance.increment(1);
  }
}
```

With the acceptance of this proposal, the same ledger state would be achieved with the following declarations:

```compact
ledger state: STATE;
ledger message: Maybe[Opaque["string"]];
ledger instance: Counter;
ledger poster: Bytes[32];

constructor() {
    ledger.state = STATE.vacant;
    ledger.message = none[Opaque["string"]]();
    ledger.instance.increment(1);
}
```

None of these ledger state fields are sealed.

### Authorized Access

A contract encapsulating a field that can be read and written only by an authorized party,
whose identity is established at contract deployment time,
might be expressed as follows:

```compact
ledger value: Field;
sealed ledger authorized_pk: Bytes[32];

constructor (value: Field, authorized_pk: Bytes[32]) {
    ledger.value = value;
    ledger.authorized_pk = authorized_pk;
}

witness sk(): Bytes[32];

export circuit get(): Field {
    assert public_key(sk()) == ledger.authorized_pk;
    return ledger.value;
}

export circuit set(new_value: Field): Void {
    assert public_key(sk()) == ledger.authorized_pk;
    ledger.value = new_value;
}

export circuit public_key (sk: Bytes[32]): Void {
    return persistent_hash(pad(32, "auth-cell:pk:"), sk);
}
```

Notice that the `authorized_pk` field is written in the constructor,
but never in the circuits.
Code that might update the sealed `authorized_pk` field after the contract
is deployed, such as in an *exported* circuit, would produce a compile-time error.

## Optional Support for Field Grouping (Backward Compatibility)

Both for partial backwards compatibility and because programmers may find the grouping useful,
it would be easy to continue to support the declaration of several ledger state fields
together, either sealed or not.
If this is desired, the previously proposed grammar would be amended:

```
LDECL     --> SEALED^OPT ledger LDECL-ELT
          --> SEALED^OPT ledger { LDECL-ELT ... }

LDECL-ELT --> ID : LEDGER-ADT ;
```

This would allow declarations of the following form:

```compact
sealed ledger {
    name : Opaque["string"];
    items : Set[Boolean];
}

ledger c : Counter;

constructor (name: Opaque["string"]) {
    ledger.name = name;
    ledger.items.insert(true);
    ledger.items.insert(false);
}

```

The backwards compatibility is only partial, because constructors are still
defined outside the ledger field declarations.

## Open Question

### Unreferenced ledger state

Should the compiler include in the ledger any ledger state that is never explicitly
initialized, referenced, or updated, or should it exclude such ledger state?

