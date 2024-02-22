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
any any post-deployment transaction.

The sealed portion of the state is not truly "constant" or "immutable" in the usual programmatic senses,
because it may be constructed incrementally in the contract's constructor using the ADTs' update operations,
but the Impact VM will never replace the sealed portion of the state after the contract is deployed.
This provides safety guarantees for contract users and opportunities for optimization by the Compact compiler.

## Ledger Changes

The ledger currently maps contract addresses to contract states, and a contract state holds a single state value,
updated by transactions.
Instead, the contract state will hold two values, one fixed at deployment time and one updated by transactions.

### Comment

Additional uses for the fixed-at-deployment state have been proposed,
beyond the sealed state elements declared by the contract author.
For example, the contract's own address may be represented within this state.

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

LDECL     --> SEALED^OPT ledger ID : LEDGER-ADT ;

SEALED    --> sealed

CONSDEFN  --> constructor ( ARG, ARG, ... ) BLOCK
```

Thus, the `sealed` keyword can appear as an optional modifier on a `ledger` field declaration,
much like `export` can appear on various definitions. 

As before, the definition of a constructor is not mandatory.
Any ledger state fields not initialized explicitly in a constructor
are initialized to their default values.

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
Thus, it is implemented with the `Cell` ADT.

## Static Analysis and Type System Changes

Ledger state field declarations and circuit definitions may be interleaved,
but forward references to ledger state fields are not allowed.
Thus, any ledger state references in a circuit must name only those fields
that were declared prior to the circuit definition.

If a ledger state field is declared with the `sealed` modifier, 
then *write* operations may occur only in the contract's constructor, but not in circuits.
*Read* operations may occur in both constructor and circuit contexts.

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
Code that attempts to update the sealed `authorized_pk` field in a circuit
would produce a compile-time error.

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
