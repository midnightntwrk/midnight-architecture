# Proposal 0010: Composable Contracts V1

This document proposes changes to the syntax and compiler target of Compact to support inter-contract circuit calls.

## Terminology

- A _program_ is a set of `module`, `contract`, `circuit`, `ledger`, `witness`, and `struct` declarations that compile.
- The _executable_ of a contract is the Javascript (JS) output of the Compact compiler.
- The _ledger state_ of a contract is the portion of the contract state that is stored at a contract address on the ledger.
- The _witness state_ of a contract is the private state that is updated by the witnesses declared in a contract.
- The _runtime_ of a contract is the portion of the contract executable that is responsible for managing the intermediate 
  ledger and witness states throughout the execution of a circuit.
- An _instance_ of a contract is **??**

# Problem Statement

Currently, contract developers have no means to reuse the state and behavior of other contracts. To solve this, introduce
`contract` and `interface` declarations to Compact.

# Compact Syntax Changes

## Adoption of `contract` Declarations

The most significant change introduced in this proposal is the adoption of contract declarations. Similarly to `contract`
declarations in Solidity, or `class` declarations in Javascript, `contract` declarations in Compact denote independently-deployable
computational units that encapsulate state and behavior.

A `contract` declaration consists of:

1. The `contract` keyword.
2. The name of the contract.
3. A sequence of type parameters.
4. A sequence of `interface`s that the contract implements (more on this later).
5. The body of the contract, wrapped in braces `{ ... }`, consisting of:
   1. A single `constructor` declaration.
   2. A sequence of `ledger` declarations.
   3. A sequence of `witness` declarations.
   4. A sequence of `circuit` declarations.

For example, the following example is a declaration for a contract `AuthCell`.

```
export contract AuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];

    witness secret_key: Bytes[32];

    constructor (authorized_pk: Bytes[32], initial_value: V) {
        this.value = initial_value;
        this.authorized_pk = authorized_pk
    }

    circuit get(): V {
        assert public_key(sk) == authorized_pk;
        return this.value;
    }

    circuit set(new_value: V): Void {
        assert public_key(this.secret_key()) == owner_pk;
        this.value = new_value;
    }

    circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```



Contracts must be deployed to be useful. The deployment process consists of the following steps:

1. **Compilation**: The Compact program containing the contract definition is compiled into an executable.
2. **Deployment Transaction*: Use the contract executable to run the contract's `constructor` with specific arguments.
The result will be an initial ledger state for the contract. Construct a deployment transaction (typically with an Application
Development Library) containing the initial ledger state and the prover and verifier keys for each `circuit` defined in the `contract` being
deployed. The deployment transaction will contain a unique, generated, contract address computed from the initial state and the prover and verifier
keys included in the deployment. This address can be used to interact with the instance of the contract being deployed.
3. Interaction: After deployment, users and other contracts can interact with the contract by sending transactions to its address. Each contract on the blockchain has a unique address, ensuring that calls and transactions are routed to the correct contract.

When a contract is deployed, it is assigned a unique
contract address

### Additional Constraints on `Contract` Declarations

> No semicolon should follow a `contract` declaration.
> Contract declarations may not be nested.

### Constructor Declarations

> Constructors may not take contracts as arguments

### Adoption of `ledger` Declarations

To reduce implementation complexity and increase contract security, the following constraint is imposed.

> Only the circuits of a contract `C` can access the ledger values of `C`.

Although direct inter-contract ledger state access is useful and technically feasible, it is not a critical feature. We
therefore err on the side of caution and disallow it entirely. Future Compact versions could relax the above constraint 
by introducing access modifiers (e.g. `public`/`private`) for `ledger` declarations.

### Adoption of `witness` Declarations

### Adoption of `this` keyword

### No Direct Contract Instantiation

## Adoption of `interface` Declarations

> No semicolon follows an `interface` declaration.

### No Witnesses in Interfaces

## Coherence with Pre-existing Features

### Coherence with `module` Declarations

Module declarations may now contain `contract` declarations.

### Coherence with Standalone `circuit` Declarations



## Limitations

### No Storing Contracts in the Ledger

To minimize the complexity of the contract runtime, contracts may not be arguments or return values of ledger operations. 
For justification of this policy, consider the following contract:

**Note**: the below contract uses the in-line `ledger` declarations in this proposal, and it removes the currently required 
`Cell` wrapper around the `Bar` type in the `bar` declaration.

```
contract Bar {
    ...
    circuit bar(): Void {
      ...
    }
}

contract Foo {
    ledger b: Bar;
    circuit foo (bar: Bar): Void {
      this.b = bar;
    }
    circuit baz (): Void {
      this.b.bar();
    }
}
```

The circuit `Foo.foo` contract accepts a contract argument of type `Bar` (represented as a `ContractAddress` by the 
runtime) and stores it in the ledger value `Foo.b`. The circuit `Foo.baz` reads `Foo.b` and calls a circuit `Bar.bar`
on `b`. For circuits like `Foo.baz` to be supported, the contract runtime would need a ledger state for `b`, which would
require one of the following:

1. Fetch the ledger state of `b` dynamically, or
2. Traverse the ledger state of `Foo` before execution begins to determine which additional ledger states are required 
   (in this case the ledger state of `b`) and fetch them prior to executing `baz`.

Both of these options introduce implementation complexity. To ensure the changes proposed in this document are feasible 
for public TestNet, such contracts are disallowed. As a result, we have the following requirement.

> `compactc` should statically detect when a program attempts to write a `contract` type to a `ledger` value and report an 
  informative error.

# Compact Target Changes

## Providing Ledger State Dependencies

## Contracts as Circuit Arguments and Return Values

Consider the following contract.

```
```

- Circuits with contract parameters or contract return values are compiled into JS functions that accept JS representations
of contract addresses.

## Proving System Changes

Inter-contract circuit calls will use the exact commitment-messaging mechanism proposed [here](./0004-micro-adt-language.md#proposed-changes). 
The key difference in this proposal is that commitments occur over `contract`s instead of `interface`s.
