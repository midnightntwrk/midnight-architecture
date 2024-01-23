# Proposal 0009: Simple Composable Contracts

This is a proposal for a modification to the Compact source language and runtime to support composable contracts.

This proposal assumes that all private state is isolated between DApps.

## Problem Statement

Modular composability is a fundamental characteristic of scalable and maintainable software systems; it suggests that a
complex software system should be constructed from a set of reusable, functionally complete software modules, each with
a limited scope of responsibility. Compact does not currently have a mechanism for composing contracts, which limits Midnight's
ability to support complex DApps that make use of pre-existing services in the form of deployed contracts.

## Proposed Source Changes

### `contract` declarations

The unit of state encapsulation in Compact is the contract. Contracts in Compact are similar to [contracts](link) in Solidity in that:

1. They encapsulate state and behavior
2. They are defined using a `contract` declaration
3. They define a constructor
4. They may be instantiated
5. They may implement interfaces
6. Each instance of a contract lives at a different address on the ledger

The following is an example of a valid Compact `contract` declaration:

```
export contract Cell<V> {
    
    ledger value: V;
    
    constructor (initial_value: V) {
        self.value = initial_value;
    }
    
    circuit get(): V {
        return self.value;
    }
    
    circuit set(new_value: V): Void {
        self.value = new_value;
    }
}
```

This contract simply holds a 

#### Important Notes

1. All `ledger` declarations require explicit types.
2. All `ledger` declarations must be initialized in the constructor or in-line. There is no default initialization value, 
   and there is no `undefined` type in Compact.
3. All `ledger` and `circuit` values are private by default.
4. `contract`s cannot be nested

### `interface` declarations

Interfaces will now be defined using an `interface` declaration, which behave similarly to `interface` declarations in Typescript.

1. Interface declarations do not include `witness` signatures.
2. Interface declarations may include `ledger` declarations.

### The `Address` type

1. `Address` types are not freely interchangeable with `Contract` types. There is no way to construct a contract solely from
    an address.
2. `Contract` types cannot be stored in `ledger` variables.

### The `Contract` type

All `contract`s implicitly implement the `Contract` interface, which is defined as follows:

```
interface Contract {
    ledger address: Address;
}
```

The value of `address` is immutable. It cannot be modified.

There are some restrictions on the `Contract` type:

1. `Contract` types cannot be stored in `ledger` variables.
2. `Contract` types cannot be constructed from `Address` types.

As a result, the only ways to obtain a `Contract` type are to:

1. Instantiate a contract.
2. Receive a contract as a parameter.

### The `self` keyword

1. Can `self` be returned from a circuit?
2. Can `Contract` types be accepted and returned from circuits?

### Inheritance

There is no inheritance in Compact. Instead, contracts may implement interfaces.

### Gas

### Account API

## Proposed Runtime Changes

### `witness` implementations

Each `contract` declaration in Compact defines a set of `witness`es specific to that contract. Therefore, each `witness`
set corresponds to a particular `contract` identifier. The user must be able to provide an implementation of a `witness` set
in Typescript, and the runtime must be able to link each user provided `witness` to the correct `contract` declaration.


```

## Desired Result

