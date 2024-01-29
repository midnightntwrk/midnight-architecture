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

What is the runtime representation of interfaces?

1. Confirm works: interfaces in Compact are translated to interfaces in Typescript. Circuits that accept a contract
   implementing an interface will accept any contract `class` that implements the interface in Typescript.

### The `ContractAddress` type

1. `ContractAddress` types are not freely interchangeable with `Contract` types as in Solidity. There is no way to construct 
    a contract solely from an address.
2. `Contract` types cannot be stored in `ledger` variables.

### The `Contract` type

All `contract`s implicitly implement the `Contract` interface, which is defined as follows:

```
interface Contract {
    ledger address: ContractAddress;
}
```

The value of `address` is immutable. It cannot be modified.

There are some restrictions on the `Contract` type:

1. `Contract` types cannot be stored in `ledger` variables, but `ContractAddress` types can.
2. `Contract` types cannot be constructed from `ContractAddress` types.

As a result, the only ways to obtain a `Contract` type are to:

1. Instantiate a contract.
2. Receive a contract as a parameter.

### The `self` keyword

1. Can `self` be returned from a circuit?
2. Can `Contract` types be accepted and returned from circuits?

### Inheritance

There is no inheritance in Compact. Contracts may implement interfaces but not extend other contracts.

### Gas

Issues with Solidity reentrancy and gas...

### Account API

The account API will be modified to include the following:

## Proposed Runtime Changes

### `witness` implementations

Each `contract` declaration in Compact defines a set of `witness`es specific to that contract. So, each `witness`
set corresponds to a particular `contract` identifier. The user must be able to provide an implementation of a `witness` set
in Typescript, and the runtime must be able to link each user provided `witness` to the correct `contract` declaration.

## `Contract` circuit arguments and return valuers

The executable for the contract `A` in the following program:

```
export contract C {
    circuit h (): Void {
        return;
    }
}

export contract B {
    circuit g (): C {
        const c = C();
        c.h();
        return c;
    }
}

export contract A {
    circuit f (b: B): C {
        return b.g();
    }
}
```

looks like this:

 
## Desired Result

## Examples

Use combinations:

1. Constructors
    1. Accept contract as constructor argument
        1. Call circuit in contract argument
    2. Create contract in constructor body
        1. Call circuit in newly constructed contract
        2. Construct contract from ledger variable set in constructor body
    3. Assign contract in constructor body
        1. Call circuit on assigned contract

2. Circuits
    1. Accept contract as circuit argument
    2. Create contract in circuit body
    3. Assign contract in circuit body
    4. Return contract as circuit result
    5. Access contract assigned in contract constructor

```
contract Foo {

    ledger value: Field;
    witness value: Field;
    
    constructor (x: Field) {
        this.value = x;
    }
    
    circuit set (x: Field): Void {
        this.value = x;
    }
    
    circuit get (): Field {
        return this.value;
    }
}

contract Baz {

    ...
    
    circuit get (): Field {
        ...
    }
}

contract Qaz {
    ...
}

contract Qux {
    constructor (x: Field) {
        ...
    }
    
    circuit get(): Qaz {
        ...
    }
}
    
contract Bar {

    ledger sum: Field;
    ledger foo: Foo; // Represented as a ledger address
    ledger bar: Bar; // Represented as a ledger address

    constructor (foo: Foo, baz: Baz) {
        this.foo = foo;
        this.bar = new Bar(x);
        this.sum = this.foo.get() + this.bar.get() + baz.get();
    }
    
    circuit f (qux: Qux): Qaz {
        foo.set(42);
        return qux.get();
    }
}

contract Quz {
    circuit f (qux: Qux): Field {
        return qux.get();
    }
}

contract Qux {
    constructor (x: Field) {
        ...
    }
    
    circuit get(): Qaz {
        ...
    }
}
    
contract Quy {
    circuit f (x: Field): Field {
        qux = new Qux(x);
        return qux.get();
    }
}

-> Map[ContractAddress, ContractState]
-> read from environment P and V keys for Qux
-> attach those keys

Tx {
    contractStates: Map[ContractAddress, ContractState]
}

---------------------------
Problem:

// trusted contract
contract Qux {
    // e.g. should always return the same value
    circuit get(): Field {
        ...
    }
}

// malicous contract
contract MaliciousQux {
    // e.g. returns different values
    circuit get(): Field {
        ...
    }
}

// trusting contract
contract Quy {
    circuit f (x: Field): Field {
        // Treating the constructor as a circuit and using the commitment scheme applied to support inter-contract calls 
        // will not be sufficient to prove that Qux behaves as Quy expects. Malicious actor could replace 'Qux.get' verifier 
        // key with 'MaliciousQux.get' verifier key. The result is that 
        qux = new Qux(x);
        return qux.get();
    }
}

---------------------------

Solution:






// malicious actor
// call f like honest actor
// reach new Qux
// I substitute new malicious qux instead

// which behaves differently from the above.
contract Qux {
    ledger f: Field;
    constructor (x: Field) {
        this.f = x;
    }
}

witness vk: Opaque["string"];

contract Quy {
    circuit f (x: Field): Field {
        const ea = hash(v, initialState); // would be a performance concert due to size of state and v
        qux = new Qux(x);
        return qux.get();
    }
}

// 

// Million dollar question: What would effectively link the behavior of Qux to Quy?

    - Hash of circuits/prover keys/verifier keys?


Thomas: complicated question of how deploys in a contract should be handled with marginal benefit.

```

## Group Example

Thomas: When are we just building a layer of abstractions without deployed instances, versus
        when we are using a public service?

        This is known as an oracle in other systems. Maybe price of USD.


// Use AuthCell to determine the conversion rate of tokens to USD?
// Authorized party sets the auth cell value, which Liquidity pool uses to perform conversions.

1. Deploying AuthCell for the oracle
2. Writing LiquidityPool against pre-deployed AuthCell


```

export contract AuthOracle[V] {

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

struct ConversionRate {
    from: QualifiedCoinInfo;
    to: QualifiedCoinInfo;
    rate: UInt64;
};

export contract LiquidityPool {

    ledger tokens: Set[QualifiedCoinInfo];

    circuit add_liquidity (rateOracle: AuthOracle[ConversionRate], token: QualifiedCoinInfo): Void {
        ...
    }
}

```