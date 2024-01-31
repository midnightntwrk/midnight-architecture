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
declarations to Compact.

## Compact Syntax Changes

### `contract` Declarations

The most significant change introduced in this proposal is the addition of contract declarations. Similarly to `contract`
declarations in Solidity, or `class` declarations in Javascript, `contract` declarations in Compact denote independently-deployable
computational units that encapsulate state and behavior.

A contract declaration consists of the `contract` keyword, followed by the name of the contract, optional type parameters,
and a body wrapped in braces `{}`. For example, the following is a valid (body-less) declaration for the
`AuthCell` contract.

```
contract AuthCell[V] {
    ...
}
```

The body of a contract contains a sequence of circuit declarations. A circuit declaration consists of the `circuit` keyword
followed by a name, a sequence of parameters wrapped in parentheses `()`, a return type, and a body wrapped in braces `{}`.
Circuit declaration _signatures_ are mostly from Compact version **??**. Adding circuit declarations (without specifying
their implementations) to the previous example might look as follows:

```
contract AuthCell[V] {

    circuit get(): V {
        ...
    }

    circuit set(new_value: V): Void {
        ...
    }

    circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

The body of the contract also contains a sequence (of length >= 1) of ledger variable declarations. A ledger declaration
consists of the `ledger` keyword followed by the name and type of the ledger variable. The previous example with ledger
declarations might look as follows:

```
contract AuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];
    
    circuit get(): V {
        ...
    }

    circuit set(new_value: V): Void {
        ...
    }

    circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

The body of `AuthCell` contains two ledger variable declarations: `value` and `authorized_pk`. The type of `value` is `V`,
a generic, and the type of `authorized_pk` is `Bytes[32]`, a fixed-length byte array. Both ledger variables together constitute
the public state of the contract. Note, all ledger variables are initialized to default values. Note, for brevity, the syntax
above removes the `Cell` wrapper around the `V` and `Bytes[32]` types required by Compact version **??**. Ledger declarations
may declare any ADT type supported by Compact version **??**. However, ledger operations cannot accept contract types as
arguments or return contract types. For a justification of this constraint, see the [Limitations](#no-storing-contracts-in-the-ledger)
section.

The body of the contract may also contain a sequence of witness declarations. A witness declaration consists of the `witness`
keyword followed by a name, an (optional) sequence of parameters wrapped in parentheses `()`, a return type. Witnesses do not have a body.
They are just signatures. Witnesses without a parameter list are treated as constants. The previous example with witness
declarations might look as follows:

```
contract AuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];

    witness sk: Bytes[32];

    circuit get(): V {
        ...
    }

    circuit set(new_value: V): Void {
        ...
    }

    circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

The `AuthCell` contract above contains only a single witness value, which is immutable. Note the difference between the
`sk` witness and the `authorized_pk` and `values` ledger variables. The `sk` witness is immutable, whereas
the `authorized_pk` and `values` ledger variables are mutable. More complex witnesses are possible, i.e., those behave
as functions. Furthermore, future Compact versions may consider adding `const` or `var` modifiers to ledger variables to
allow for immutable and mutable ledger variables, respectively. Witnesses cannot accept contract types as arguments or return
contract types as results for similar reasons that ledger operations cannot. For a justification of this constraint, see
the [Limitations](#no-storing-contracts-in-the-ledger) section.

The body of the contract may also contain a single `constructor` declaration. Constructor declarations consist of the
`constructor` keyword followed by a sequence of parameters wrapped in parentheses `()`, and a body wrapped in braces `{}`.
The body of the constructor initializes the ledger and witness state of the contract by performing a sequence of ledger
and witness invocations. The previous example with a constructor might look as follows:

```
contract AuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];

    witness sk: Bytes[32];

    constructor (value: V, authorized_pk: Bytes[32]) {
        ...
    }

    circuit get(): V {
        ...
    }

    circuit set(new_value: V): Void {
        ...
    }

    circuit public_key (sk: Bytes[32]): Void {
        ...
    }
}
```

A contract does not need to have a constructor. If a contract does not have a constructor, the ledger variables are initialized
to their default values. Although each contract defines a constructor, Compact does not support invoking contract constructors,
and it does not support dynamic contract instantiation. For a justification of this constraint, see the [Limitations](#no-dynamic-contract-instantiation)
section. Furthermore, constructors cannot accept contract-typed parameters. For a justification of this constraint, see the
[Limitations](#no-contracts-as-constructor-parameters) section.

Ledger variables and witnesses can be accessed in the body of a contract with the `this` keyword, which functions
similarly to `this` in Javascript. With all of these elements, the implementations of the `get` and `set` circuits, as well as the `constructor`, can be
completed. The previous example with implementations might look as follows:

```
contract AuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];

    witness sk: Bytes[32];

    constructor (value: V, authorized_pk: Bytes[32]) {
        this.value = value;
        this.authorized_pk = authorized_pk
    }

    circuit get(): V {
        assert public_key(this.sk) == authorized_pk;
        return this.value;
    }

    circuit set(new_value: V): Void {
        assert public_key(this.sk) == this.authorized_pk;
        this.value = new_value;
    }

    circuit public_key (sk: Bytes[32]): Void {
        return persistent_hash(pad(32, "auth-cell:pk"), sk);
    }
}
```

Notice that `public_key` does not access any witnesses or ledger variables. Circuits like this are called _pure_ circuits,
just as they are in the current Compact version. Contract declarations may not contain other contract or `struct` declarations.
This restriction is imposed to simplify the implementation. Future Compact versions may relax this restriction.

### Modules

Modules may contain contract declarations, but not all contract declarations need to be must be contained in an explicit
`module` wrapper. Contracts may or may not be exported from modules using the `export` keyword. Contracts that are not
exported from a module cannot be accessed outside the enclosing module. However, _all_ contracts in a program, regardless
of whether they are exported, and regardless of the module in which they are defined, can be deployed. This will make
more sense after section on [internal contract calls](#internal-contract-calls). Modules may also contain `interface` declarations,
which are explored in the next section. Modules may also contain circuit declarations, but note that any such circuit is
necessarily a pure circuit, since it does not have access to the ledger variables or witnesses of a contract. Finally, modules
may also contain `struct` declarations, just as in the current Compact version.

**Question for Kent**: Are files that export contracts but contain no module declarations automatically wrapped in a module
identified by the file name of the file containing the contract declarations? How does this work when a file contains both
a module and top-level declarations?

### `interface` Declarations

Contract declarations introduce a mechanism for state and behavior encapsulation in Compact. To support modularity and
composability, Compact also needs a mechanism to abstract the state and behavior of contracts. This is the purpose of
interface declarations.

Interface declarations in Compact are similar to interface declarations in Typescript. An interface declaration consists
of the `interface` keyword, followed by the name of the interface, optional type parameters, and a body wrapped in braces
`{}`. The body of an interface contains a sequence of interface circuit declarations. The syntax for an interface circuit
declaration is the same as the syntax for a contract circuit declaration, but without a circuit body wrapped in braces. The
following is an example of a valid interface declaration.

```
interface IAuthCell[V] {
    circuit get(): V;
    circuit set(new_value: V): Void;
    circuit public_key (sk: Bytes[32]): Void;
}
```

Interfaces do not contain witness or ledger declarations. Interfaces are not deployed to the blockchain; they are simply a
type-level construct. The type-checking procedure for contracts implementing interfaces is similar to that of the type-checking
procedure for classes that implement interfaces in Typescript; a contract that implements an interface must provide implementations
for all interface circuit declarations in the interface it implements. Only contracts can implement interfaces. For example, the
`AuthCell` contract can implement the `IAuthCell` interface:

```
interface IAuthCell[V] {
    circuit get(): V;
    circuit set(new_value: V): Void;
    circuit public_key (sk: Bytes[32]): Void;
}

contract AuthCell[V] implements IAuthCell[V] {

    ledger value: V;
    ledger authorized_pk: Bytes[32];

    witness sk: Bytes[32];

    constructor (value: V, authorized_pk: Bytes[32]) {
        this.value = value;
        this.authorized_pk = authorized_pk
    }

    circuit get(): V {
        assert public_key(this.sk) == authorized_pk;
        return this.value;
    }

    circuit set(new_value: V): Void {
        assert public_key(this.sk) == this.authorized_pk;
        this.value = new_value;
    }

    circuit public_key (sk: Bytes[32]): Void {
        return persistent_hash(pad(32, "auth-cell:pk"), sk);
    }
}
```

Although we support contracts implementing interfaces, we do not support multiple interface inheritance (using `implements`
followed by a comma-separated list of interfaces the contract satisfies), and we do not contract inheritance analogous
to class inheritance in Javascript. This is to simplify the implementation. Future Compact versions may relax
this constraint.

## Internal Contract Calls

An internal contract call is when a circuit in one contract calls a circuit in another contract. Since contracts cannot
be dynamically instantiated, the only way to get a contract value is to pass it as parameter to the circuit that needs it.
Contract parameters are like normal circuit parameters except the type of the circuit parameter is either the name of a contract
or the name of an interface. Using the running `AuthCell` example, an internal contract call might look as follows:

```
contract AuthCellUser {
    circuit use_auth_cell(auth_cell: AuthCell[Field]): Void {
        const v = auth_cell.get();
        auth_cell.set(f + 1);
        return v;
    }
}
```

The `use_auth_cell` circuit in the `AuthCellUser` contract accepts a contract argument of type `AuthCell[Field]`, calls
the `get` circuit on `auth_cell`, stores the result, and then calls the `set` circuit on `auth_cell` to increment the
original value by one. The `use_auth_cell` circuit returns the original value. The `use_auth_cell` circuit could also
return the value of `auth_cell` itself, although, at present, although doing so would not be useful since the caller
of `use_auth_cell` already has a reference to `auth_cell`.

One contract cannot directly access the ledger variables or witnesses of another contract. For example, `use_auth_cell`
cannot directly access `authorized_pk` or `value` in `AuthCell`. Nor can it directly access `sk`. See the
[Limitations](#no-external-ledger-variable-accesses) section for a justification of this constraint.

Any pure circuit in a contract can be accessed from another contract using dot notation similar to how static methods are
accessed in Javascript. For example, the `public_key` circuit in `AuthCell` can be accessed using `AuthCell.public_key`.

**Open Question**: The above is not strictly necessary, since any pure circuit can be lifted to a top-level circuit.
Maybe we should remove this feature to simplify the implementation?

**Open Question**: Can `pure_circuits` also accept contract arguments and return contract values? Doing so is seemingly
redundant, since only the pure circuits of the contract argument can be called any pure circuit defined in a contract
can be accessed directly with dot notation.

## The Compact Standard Library (In Progress)

Ideally, the Compact standard library should be accessed through the same composition mechanisms as regular
contracts. The ledger kernel and ZSwap witnesses are special cases to some extent, but they should not be treated as such
unless absolutely necessary.

One idea is to introduce a `System` contract (analogous to Java's [System](https://docs.oracle.com/javase/8/docs/api/java/lang/System.html)
class) that contains the ledger kernel and ZSwap witnesses, as well as the circuits for sending and receiving funds. Such
a contract should never be instantiable, and it should be accessible from any contract without having to receive it as a
parameter.

## Limitations

### No Storing Contracts in the Ledger

To minimize the complexity of the contract runtime, contracts may not be arguments or return values of ledger operations.
To see why, consider the following contract.

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
for public TestNet, such contracts are disallowed. We also have the following requirement.

> `compactc` should statically detect when a program attempts to write a `contract` type to a `ledger` value and report an
informative error.

### No Contracts as Constructor Parameters

To minimize the complexity of the contract runtime, contracts may not be constructor parameters. To see why, consider when
passing contracts as constructor parameters would be useful. Remember that contract constructors cannot be directly invoked
in Compact. Hence, the only way to pass a contract as a constructor parameter would be to pass it as an argument to the
`initialState` function in the contract executable produced by `compactc`. Since contracts cannot be arguments to ledger
operations or witnesses, such a contract parameter would only be useful if the contract constructor were to invoke a circuit
defined on the contract. But, this creates a similar issue to the issue that dynamic contract invocations create. Namely,
what does it mean to prove the correctness a circuit executed inside a contract constructor? Due to the ambiguity here,
this feature is not supported. We also have the following requirement:

> `compactc` should statically detect when a contract attempts to define a contract-typed constructor parameter and report
an informative error.

### No Dynamic Contract Instantiation

Although each contract defines a constructor, such constructors may not be invoked to instantiate a contract dynamically.
This constraint is imposed to minimize the complexity of the contract runtime. Although dynamic instantiation is a useful
and desirable feature, more work must is required to understand the semantics of dynamic contract instantiation, as well
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

## Proving System Changes

Internal contract calls will use the exact commitment-messaging mechanism proposed [here](./0004-micro-adt-language.md#proposed-changes).
The key difference in this proposal is that commitments occur over `contract`s instead of `interface`s.
