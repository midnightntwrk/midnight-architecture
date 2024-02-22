# Proposal 0011: Contract Interface Types

This document proposes changes to Compact syntax to allow the declaration of contract interface types,
expressing the type of all contracts with *at least* some set of circuits exported.

## Prerequisites

This proposal assumes the composable contracts syntax proposal as a prerequisite, because that proposal
introduces contract reference types and their semantics.  This proposal extends those types to include
abtract interfaces, in addition to concretely defined contract types.

## Problem Statement

If the only contract types that can be assigned to contract references in Compact are the concrete
types introduced in contract definitions, then dependencies on other contracts are limited to
what could be expressed by copying the full code of one contract into another.

A great deal of flexibility and compositional power can be gained by
supporting contract interface types, which express the minimal set of
foreign circuits required by the caller.  Then, different concrete
contract types can implement that interface in different ways.

## Compact Syntax Changes

Interface declarations declare a set of circuits that must be present in any implementing contract.

The following change to the grammer is proposed (assuming the changes proposed in composable contracts syntax):

```
PELT   --> IFDEFN

IFDEFN --> interface INTERFACE-NAME TPARAMS^OPT { EDECL ... }

CTDEFN --> contract CONTRACT-NAME { CTELT ... }
       --> contract CONTRACT-NAME implements IFIMPL , ... { CTELT ... }
       
IFIMPL --> INTERFACE-NAME TARGS_OPT
```

All circuits declared in the interface definition are necessarily exported, so the appearance
of the `export` modifier on a circuit declaration in an interface is accepted, but does not
affect the semantics of the declaration.

Interfaces do not contain witness or ledger declarations.
An interfaces cannot be deployed; it simply define a type that can be used to label a contract reference.

The type-checking procedure 
for contracts implementing interfaces is similar to that of the type-checking procedure for classes that implement interfaces in 
TypeScript; a contract that implements an interface must export implementations for all interface circuit declarations 
in the interface it implements. Only contracts can implement interfaces. 

A contract can implement multiple interfaces, expressed with comma-separated interface names
after the `implements` keyword.  It must provide circuit definitions for the union of the sets
of circuits declared in the list of interfaces.

### Example

For example, the `AuthCell` contract can implement 
the `IAuthCell` interface:

```
interface IAuthCell[V] {
    circuit get(): V;
    circuit set(new_value: V): Void;
    circuit public_key (sk: Bytes[32]): Void;
}

contract AuthCell implements IAuthCell[Field] {
    ...
}
```

