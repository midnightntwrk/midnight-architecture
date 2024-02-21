# Proposal 0009: Composable Contracts Syntax

This document proposes changes to the Compact syntax to support contract declarations and internal contract calls.

## Terminology

- A _program_ is a set of `module`, `contract`, `circuit`, `ledger`, `witness`, and `struct` declarations that compile.
- The _executable_ of a contract is the Javascript output of the Compact compiler.
- The _ledger state_ of a contract is the portion of the contract state that is stored at a contract address on the ledger.
- The _witness state_ of a contract is the private state that is updated by the witnesses declared in a contract.
- The _runtime_ of a contract is the portion of the contract executable that is responsible for managing the intermediate
  ledger and witness states throughout the execution of a circuit.
- An _instance_ of a contract is a copy of a contract templated by a contract definition. Analogous to a class instance
  (object) in Javascript, each instance of a contract has an independent ledger and witness state.
- An _internal contract call_ is when a circuit in one contract calls a circuit defined in another contract.

# Problem Statement

Currently, contract developers have no means to reuse the state and behavior of other contracts and no means to abstract
the state and behavior of contracts. To solve these issues, this document proposes the addition of `contract` and `interface`
declarations to Compact. For Midnight TestNet, the critical addition here is `contract` declarations, so `interface`
declarations are considered a stretch goal.

## Compact Syntax Changes

### `contract` Declarations

The most significant change introduced in this proposal is the addition of contract declarations. Similarly to contract
declarations in Solidity, contract declarations in Compact denote independently-deployable computational units that 
encapsulate state and behavior.

A contract declaration consists of the `contract` keyword, followed by the name of the contract and a body wrapped in braces `{}`. 
For example, the following is a valid (body-less) declaration for the `AuthCell` contract. Contracts may not be generic, i.e.,
they may not have type parameters (see [Limitations](#no-parametrically-polymorphic-contracts)).

```
contract AuthCell {
    ...
}
```

The body of a contract contains a sequence (of length >= 1) of circuit declarations. A circuit declaration consists of the `circuit` keyword
followed by a name, a sequence of parameters wrapped in parentheses `()`, a return type, a body wrapped in braces `{}`, and an optional `export`
modifier. The syntax for circuit signatures is unchanged from the current Compact version. Adding circuit declarations (without specifying
their implementations) to the previous example might look as follows:

```
contract AuthCell {

    export circuit get(): Field {
        ...
    }

    export circuit set(new_value: Field): Void {
        ...
    }

    export circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

Circuits with an `export` modifier are externally callable, while circuits without an `export` modifier are not, just as
is the case for the current Compact version.

The body of the contract also contains a sequence (of length >= 1, see [Limitations](#contracts-must-have-a-public-state) section) 
of ledger declarations. A ledger declaration consists of the `ledger` keyword followed by a mutability specifier (`let` or `const`)
and the name and type of the ledger variable. The previous example with ledger declarations might look as follows:

```
contract AuthCell {

    ledger let value: Field;
    ledger const authorized_pk: Bytes[32];
    
    export circuit get(): Field {
        ...
    }

    export circuit set(new_value: Field): Void {
        ...
    }

    export circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

The body of `AuthCell` contains two ledger variable declarations: `value` and `authorized_pk`. The type of `value` is `Field`, 
and the type of `authorized_pk` is `Bytes[32]`, a fixed-length byte array. The mutability specifiers indicate
whether the value can be modified. The `const` keyword indicates that the value cannot be changed, while the `let` keyword 
indicates that the value can be mutated freely. Both ledger variables together constitute the public state of the contract. 
All ledger variable types _except_ contract values have default values. This is discussed in a [later section](#internal-contract-calls).

The example above does not use the `Cell` syntax to wrap the types of mutable ledger variables. This is intentional. 
The `Cell` syntax should be removed in favor of the `let` mutability specifier so that a syntactic symmetry exists
between `let` and `const` ledger variables.

The body of a contract also contains a sequence (of length >= 0) of witness declarations. A witness declaration consists of the `witness`
keyword followed by a name, an (optional) sequence of parameters wrapped in parentheses `()`, and a return type. Witnesses do not have a body.
They are just signatures. The previous example with witness declarations might look as follows:

```
contract AuthCell {

    ledger let value: Field;
    ledger const authorized_pk: Bytes[32];

    witness sk(): Bytes[32];

    export circuit get(): Field {
        ...
    }

    export circuit set(new_value: Field): Void {
        ...
    }

    export circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

The `AuthCell` contract above contains only a single witness, `sk`. In many programming languages, one _tends_ to have
functions with signatures `() => T` always return the same value. Although `AuthCell` does not explicitly _require_ `sk` 
to always return the same value, that is the convention we assume in the `AuthCell` implementation above (see
[Limitations](#support-for-const-and-mutable-witness-variables) for a discussion of this convention). Witnesses 
cannot accept contract types as arguments or return contract types as results for similar reasons that ledger operations cannot. 
For a justification of this constraint, see the [Limitations](#no-storing-contracts-in-the-ledger) section.

The `let` and `const` modifiers used for the `ledger` declarations indicate the mutability of the ledger variables.
the `let` modifier used for `value` requires that `value` is mutable, while the `const` modifier used for `authorized_pk` requires
that `authorized_pk` is immutable.

The body of the contract may also contain a single `constructor` declaration. Constructor declarations consist of the
`constructor` keyword followed by a sequence of parameters wrapped in parentheses `()`, and a body wrapped in braces `{}`.
The body of the constructor initializes the ledger and witness state of the contract by performing a sequence of ledger
and witness invocations. The previous example with a constructor might look as follows:

```
contract AuthCell {

    ledger let value: Field;
    ledger const authorized_pk: Bytes[32];

    witness sk(): Bytes[32];

    constructor (value: Field, authorized_pk: Bytes[32]) {
        ...
    }

    export circuit get(): Field {
        ...
    }

    export circuit set(new_value: Field): Void {
        ...
    }

    export circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

A contract does not need to have a constructor. If a contract does not have a constructor, the ledger variables are initialized
to their default values. Exceptions to this rule are `ledger const` ledger variables

Although each contract defines a constructor, Compact does not support invoking contract constructors,
and it does not support dynamic contract instantiation. For a justification of this constraint, see the [Limitations](#no-dynamic-contract-instantiation)
section.

Circuits, ledger variables, and witnesses can be accessed in the body of a contract with the `this` keyword, which functions
similarly to `this` in Javascript. With all of these elements, the implementations of the `get` and `set` circuits, as well 
as the `constructor`, can be completed. The previous example with implementations might look as follows:

```
contract AuthCell {

    ledger let value: Field;
    ledger const authorized_pk: Bytes[32];

    witness sk(): Bytes[32];

    constructor (value: Field, authorized_pk: Bytes[32]) {
        this.value = value;
        this.authorized_pk = authorized_pk
    }

    export circuit get(): Field {
        assert this.public_key(this.sk()) == this.authorized_pk;
        return this.value;
    }

    export circuit set(new_value: Field): Void {
        assert this.public_key(this.sk()) == this.authorized_pk;
        this.value = new_value;
    }

    export circuit public_key (sk: Bytes[32]): Void {
        return persistent_hash(pad(32, "auth-cell:pk"), sk);
    }
}
```

Notice that `public_key` does not access any witnesses or ledger variables. Circuits like this are called _pure_ circuits,
just as they are in the current Compact version. Contract declarations may not contain other contract or `struct` declarations.
This restriction is imposed to simplify the implementation. Future Compact versions may relax this restriction.

### Modules

Modules may contain contract declarations, but not all contract declarations must be contained in an explicit
`module` wrapper. Contracts may or may not be exported from modules using the `export` keyword. Contracts that are not
exported from a module cannot be accessed outside the enclosing module. However, _all_ contracts in a program, regardless
of whether they are exported, and regardless of the module in which they are defined, can be deployed. Modules may also 
contain circuit declarations, but note that any such circuit is necessarily a pure circuit since it does not have access 
to the ledger variables or witnesses of a contract. Finally, modules may also contain `struct` declarations, just as in 
the current Compact version.

**Question for Kent**: Are files that export contracts but contain no module declarations automatically wrapped in a module
identified by the file name of the file containing the contract declarations? How does this work when a file contains both
a module and top-level declarations?

## Internal Contract Calls

An internal contract call is when a circuit in one contract calls a circuit in another contract. Internal contract calls
will be supported with the following additions to the syntax described so far:

- Contract constructors may accept contract-typed arguments. 
- Contract values be assigned to `ledger const` variables. 
- A circuit can call a circuit defined on a contract value using dot notation.

and the following usage constraints: 

- A constructor cannot call the circuits of a contract parameter.
- A circuit cannot accept contract arguments or return contract values.
- A witness cannot accept contract arguments or return contract values.

For justifications for these constraints, see the [Limitations] section.

Given the above constraints, and given that contracts cannot be dynamically instantiated, the only way for a circuit to
get a contract value is to read one from a `ledger const` variable. Using the running `AuthCell` example, this situation
might look like the following.

Contract parameters are like normal circuit parameters except the type of the circuit parameter is either the name of a contract
or the name of an interface. Using the running `AuthCell` example, an internal contract call might look as follows:

```
contract AuthCellUser {

    ledger const auth_cell: AuthCell;
    
    constructor (auth_cell: AuthCell) {
        this.auth_cell = auth_cell;
    }
    
    export circuit use_auth_cell(): Void {
        const v = this.auth_cell.get();
        this.auth_cell.set(f + 1);
        return v;
    }
}
```

The `use_auth_cell` circuit in the `AuthCellUser` calls `this.auth_cell.get` to retrieve the field value stored in `auth_cell`, 
stores the result, and then calls `this.auth_cell.set` to increment the original value by one. The `use_auth_cell` 
circuit returns the original value.

Although a contract can call a circuit on a contract to which it has reference, a contract cannot directly access 
the ledger variables or witnesses of another contract. For example, `use_auth_cell` cannot directly access `authorized_pk` 
or `value` in `AuthCell`. Nor can it directly access `sk`. See the [Limitations](#no-external-ledger-variable-accesses) section for a justification of this 
constraint.

## The Compact Standard Library

Due to uncertainty about the semantics of ledger kernel operations and ZSwap witnesses in a version of Compact with
contract declarations, the Compact standard library will be treated as a special case. The kernel operations will be
in-lined using the same techniques that are used currently.

## Limitations

The following limitations are imposed on the version of Compact proposed in this document. Some sections also include 
requirements on `compactc` that the limitations imply.

### Only `const` Contract Ledger Variables

For security purposes, we only permit storing contract values in `ledger const` variables. This is because the value of
such variables is set in the contract constructor at the time the contract is deployed. We must assume that the deployer
trusts the instance of the contract that is stored in the `ledger const` variable, but the deployer _cannot_ trust an
instance of a contract that is passed as a parameter to a circuit, since all circuits are callable by anyone. We have the
following requirement:

> `compactc` should statically detect when a circuit attempts to assign a contract value to a `ledger let` variable and
report an informative error.

### Default Contract Ledger Variables

Since there is no natural default value for a contract-typed ledger variable (and to avoid the hornet's nest of `null`), 
all `ledger const` variables storing contracts must be explicitly initialized in the contract constructor. We have the
following requirement:

> `compactc` should statically detect when a contract-typed ledger variable is not initialized and report an informative error.

### Circuits May Not Accept/Return Contract Parameters/Values

To minimize the complexity of the contract runtime, contracts may not be passed as arguments to circuits. This constraint 
makes contracts more secure, since allowing consumers of a contract to pass arbitrary contracts in circuit parameters 
means that the state of the contract being called can be modified by a contract that is potentially unknown to the deployer. 
This also leads to the following requirement:

> `compactc` should statically detect when a circuit attempts to accept a contract as a parameter and report an informative
error

Circuits may not return contract values. At the moment, this doesn't look like a security issue. The constraint is imposed
for implementation simplicity and because the implications of such a feature are unclear. See [Open Questions](
#can-circuits-return-contract-values) for a discussion. This also leads to the following requirement:

> `compactc` should statically detect when a contract attempts to return a contract from a circuit and report an informative
error

### Witnesses May Not Accept/Return Contract Parameters/Values

The runtime will likely represent contracts by their addresses, and it is unclear how the witness implementor would
expect a contract to be represented. This leads to the requirement:

> `compactc` should statically detect when a witness attempts to accept a contract parameter or return a contract value
and report an informative error

### Contracts Must Have a Public State

Each contract must have at least one ledger declaration in its body. This constraint is imposed because, otherwise, the 
declared contract has no ledger state, and it is semantically meaningless to deploy a contract with no ledger state to 
the blockchain. This leads to the following requirement.

> `compactc` should statically detect when a contract attempts to define a contract without a public state and report an
informative error.

### No Calling Circuits of Contract Parameters in Constructors

The current proposal does not allow the circuits of contract parameters to be called in the constructor of a contract.
This is because it isn't clear what it means to prove the correctness of a circuit that is called in a constructor. We have
the following requirement:

> `compactc` should statically detect when a constructor attempts to call a circuit defined on a contract argument and
report an informative error.

### Contracts May Not Be Passed 

### No Dynamic Contract Instantiation

Although each contract defines a constructor, such constructors may not be invoked to instantiate a contract dynamically.
This constraint is imposed to minimize the complexity of the contract runtime. Although dynamic instantiation is a useful
and desirable feature, more work is required to understand the semantics of dynamic contract instantiation, as well as 
its broader implications for contract security. The key question dynamic instantiation raises is, what does it mean to
prove the correctness of a contract instantiation? There is no clear answer to this question at present, making implementation
infeasible for our timeline.

### No External Ledger Variable Accesses

In object-oriented languages, the members of a class can often be accessed with dot notation (e.g. `foo.bar`). The ledger
declarations in a contract somewhat resemble member declarations on classes. However, to reduce implementation complexity
and preserve strict, common-sense contract security, we impose the constraint that only the circuits declared in a contract
can access the ledger values declared in the same contract. Direct inter-contract ledger state access is useful and technically feasible, but it is not a critical feature. We
therefore err on the side of caution and disallow it entirely. Future Compact versions could relax the above constraint
by introducing access modifiers (e.g. `public`/`private`) for `ledger` declarations.

### If a Circuit Does Not Exist for a Contract, the Runtime Must Fail With An Informative Error

`Contract` parameters will be represented at runtime as the contract address for the contract being passed. If the runtime
attempts to call a circuit that does not exist on a contract (is not present in the corresponding instance of `ContractState`),
then the runtime must fail with an error indicating as much.

### No Parametrically Polymorphic Contracts

The current proposal does not support parametrically polymorphic contracts. This is because it is unclear what it means
to deploy a parametrically polymorphic contract. In typical parametrically polymorphic languages, one must eventually
supply a concrete type for a type parameter. What does it mean to supply a concrete type to a parametrically polymorphic
contract? Is the concrete type supplied when the contract is deployed? If so, how would such a type be represented on chain?
Is the concrete type fixed for the lifetime of the contract? If not, under what conditions can the concrete type change, and
what is the mechanism for doing so?

## Proving System Changes

Internal contract calls will use the exact commitment-messaging mechanism proposed [here](./0007-abcird-contract-interfaces.md).
The key difference in this proposal is that commitments occur over contracts instead of interfaces.

## Stretch Goals

The following sections describe features that are nice to have but not strictly necessary for Midnight DevNet.

### `interface` Declarations

Contract declarations introduce a mechanism for state and behavior encapsulation in Compact. To support modularity and
composability, Compact also needs a mechanism to abstract the state and behavior of contracts. This is the purpose of
interface declarations.

Interface declarations in Compact are similar to interface declarations in Typescript. An interface declaration consists
of the `interface` keyword, followed by the name of the interface, and a body wrapped in braces `{}`. Unlike contracts,
interfaces may be parametrically polymorphic, since interfaces are compile-time entities. The body of an interface contains 
a sequence of interface circuit declarations. The syntax for an interface circuit declaration is the same as the syntax 
for a contract circuit declaration but without a circuit body wrapped in braces. The following is an example of a valid 
interface declaration.

```
interface IAuthCell[V] {
    circuit get(): V;
    circuit set(new_value: V): Void;
    circuit public_key (sk: Bytes[32]): Void;
}
```

Interfaces do not contain witness or ledger declarations, and the circuits defined in interfaces may not have access (`export`)
modifiers. Interfaces are not deployed to the blockchain; they are simply a type-level construct. The type-checking procedure 
for contracts implementing interfaces is similar to that of the type-checking procedure for classes that implement interfaces in 
Typescript; a contract that implements an interface must provide implementations for all interface circuit declarations 
in the interface it implements. Only contracts can implement interfaces. For example, the `AuthCell` contract can implement 
the `IAuthCell` interface:

```
interface IAuthCell[V] {
    circuit get(): V;
    circuit set(new_value: V): Void;
    circuit public_key (sk: Bytes[32]): Void;
}

contract AuthCell implements IAuthCell[Field] {

    ledger let value: Field;
    ledger const authorized_pk: Bytes[32];

    witness sk(): Bytes[32];

    constructor (value: Field, authorized_pk: Bytes[32]) {
        this.value = value;
        this.authorized_pk = authorized_pk
    }

    export circuit get(): Field {
        assert public_key(this.sk()) == authorized_pk;
        return this.value;
    }

    export circuit set(new_value: Field): Void {
        assert public_key(this.sk()) == this.authorized_pk;
        this.value = new_value;
    }

    export circuit public_key (sk: Bytes[32]): Void {
        return persistent_hash(pad(32, "auth-cell:pk"), sk);
    }
}
```

Although we support contracts implementing interfaces, we do not support multiple interface inheritance (using `implements`
followed by a comma-separated list of interfaces the contract satisfies), and we do not support contract inheritance analogous
to class inheritance in Javascript. This is to simplify the implementation. Future Compact versions may relax
this constraint.

### Support for Const and Mutable Witness Variables

In the `AuthCell` example, the `sk()` witness always returns the same value. As such, it should be possible to specify
such in the source language. Analogous to `let` and `const` ledger variables, future Compact versions may consider adding
`let` and `const` witness variables. The mutability of these variables could be reflected in the generated Typescript code
as `readonly` or non-`readonly` properties of the generated `Witness` type. One approach to enforcing the mutability of
a witness is to record the value of all `const` witnesses prior to beginning the execution of a circuit, and to ensure that
the value returned by each `const` witness is the same for the duration of the execution of the circuit.

### Accessing Pure Circuits via Dot Notation

It would be very useful for the pure circuits of a contract to be accessible from another contract using dot notation,
similarly to how `static` methods are available to other classes in Javascript.

## Open Questions

### Can Circuits of Contract Parameters be Called in the Constructor?

The current proposal does not allow the circuits of contract parameters to be called in the constructor of a contract.
This is because there isn't a clear answer to the question, what does it mean to prove the correctness of a circuit that
is invoked in a constructor?

### Can Circuits Return Contract Values?

The current proposal does not allow circuits to return contract values, but (according to the author's understanding) there
is no fundamental reason why this should not be possible. Passing contracts as parameters to circuits is different from 
returning contracts from circuits. Assuming the former is not possible, then, in the latter case, the outer contract 
necessarily trusts the inner contract that returns the contract value, since the outer contract specifies the inner 
contract in its constructor.

### Can Contract Values Be Stored In ADTs?

If there is support for assigning contract values to `let const` ledger declarations, then we have to decide if contracts
can be stored in ADT ledger declarations. This seems technically possible, since a contract state resolution process would
need to traverse the contract state dependency graph anyway. However, it is unclear what the implications of this feature
are.

## Future Directions

The standard library should be accessed through the same composition mechanisms as regular contracts. The ledger kernel
and ZSwap witnesses are special cases to some extent, but they should not be treated as such unless absolutely necessary.
One idea is to introduce a special `System` contract (analogous to Java's [System](https://docs.oracle.com/javase/8/docs/api/java/lang/System.html) class) that contains the ledger 
kernel and ZSwap witnesses, as well as the circuits for sending and receiving funds. Such should not be instantiable and 
should be accessible from any contract without having to receive it as a parameter.

Future versions should attempt to support [dynamic contract instantiation](#no-dynamic-contract-instantiation) and some
form of interface inheritance, and [direct inter-contract](#no-external-ledger-variable-accesses) ledger state access.
