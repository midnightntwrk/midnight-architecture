# Proposal 0010: Composable Contracts Syntax

This document proposes changes to the Compact syntax to support
1. the declaration of several contracts in a single file
2. ledger state fields holding references to contracts
3. circuits making calls to the circuits of other contracts

## Terminology

- A _program_ is a set of `module`, `contract`, and type definitions, along with `include`, `import`, and `export` declarations.
- The _executable_ of a contract is the JavaScript output of the Compact compiler.
- The _ledger state_ of a contract is the portion of the contract state that is stored at a contract address on the ledger.
- The _witness state_ of a contract is the private state that is updated by the witnesses declared in a contract.
- The _runtime_ of a contract is the portion of the contract executable that is responsible for managing the intermediate
  ledger and witness states throughout the execution of a circuit.
- An _instance_ of a contract is a specific deployed instantiation of a contract type, with its own ledger and witness state.
- An _foreign contract call_ is when a circuit in one contract calls a circuit defined in another contract.

## Problem Statement

Compact provides no means for a contract to reuse the functionality of another contract, 
other than copying the code from one contract into another.
Contract developers want to write contracts that depend on already-deployed contracts.

Concretely, the need is for contract *B* to hold a reference to another contract *A* 
and for the circuits of *B* to be able to call circuits in *A*, 
so that *B*’s functionality depends on the functionality of *A*.

Meeting this need requires the introduction of *contract types* within Compact, 
so that ledger fields and variables may hold references to contracts.

## Compact Syntax Changes

### `contract` Definitions

Prior to this proposal, there is no name *in Compact* for the ledger state, witnesses, and circuits that describe a contract.
In order to refer to contract types in Compact, it is necessary to add a construct to the language
that collects the elements of the contract and associates them with an identifier.

The following change to the grammar is proposed:

```
PELT   --> CTDEFN

CTDEFN --> contract CONTRACT-NAME { CTELT ... }

CTELT  --> INCLD
       --> LDECL
       --> CDEFN
       --> WDECL
```

The grammar productions for ledger declarations and witness declarations
are *removed* from top-level program elements.  They may occur *only* within a contract definition.
Pure circuits may be defined outside of contract definitions, without access to any
ledger state.

If the proposal for sealed ledger state is adopted, an additional grammar rule must be added
for a separately declared constructor,

```
CTELT  --> CONSDEFN
```

and, like other contract elements, removed from top-level program elements.

### Example

The following is an example of a contract using this syntax and assuming
the adoption of the proposal for sealed ledger state fields.
Without the adoption of that proposal, the example would encapsulate
the two ledger state fields and the constructor in a single declaration,
and `value` would have type `Cell[Field]`.

```compact
contract AuthCell {
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
}
```

### Restrictions

Contracts may not be generic, i.e., they may not have type parameters
(see [Limitations](#no-parametrically-polymorphic-contracts)).

Circuits with an `export` modifier are externally callable, while circuits without an `export` modifier are not, just as
is the case for the current Compact version.

The body of the contract must declare at least one contract state field 
(see [Limitations](#contracts-must-have-a-public-state) section).

### Interactions with Module Definitions

Modules may contain contract definitions, but not all contract declarations must be contained in an explicit
`module` wrapper. Contract type names may or may not be exported from modules using the `export` keyword.
Contract type names that are not exported from a module cannot be accessed outside the enclosing module
*in Compact*. However, _all_ contracts in a program, regardless
of whether they are exported and regardless of the module in which they are defined, can be deployed. Modules may also 
contain circuit declarations, but note that any such circuit is necessarily a pure circuit since it does not have access 
to the ledger variables or witnesses of a contract.

**Question for Kent**: Are files that export contracts but contain no module declarations automatically wrapped in a module
identified by the file name of the file containing the contract declarations? How does this work when a file contains both
a module and top-level declarations?

## Contract References

Any contract type name in scope may be used as the type of a ledger state field or a local `const` binding statement.
Constructor parameters and witness function parameters may also be declared to hold contract types.
**Circuit parameter types, circuit return types, and witness return types may not include contract types.**

There is no "null" contract reference value and no default value for contract types.

The preceding rules imply that all ledger state fields or ADTs holding contract references must be initialized
in the constructor of a contract.  Furthermore, almost all uses of ledger state fields
holding contract references may be declared `sealed` (assuming the adoption of the proposal for sealed ledger state).
The only way a ledger state field of contract type could be updated is with some other value in the ledger state,
already provided at the time a contract was deployed.  In other words, all possible references from one
contract to another are known at the time the referring contract is deployed, regardless of sealing declarations.

It appears that no changes to the Compact grammar are necessary to support contract types.
They will be parsed in the same way as user-defined types, such as enumerations and structure types.

Changes to the type checker are clearly required to support contract types,
both to reject programs that attempt to use contract types in invalid places
and to validate foreign contract calls, described in the next section.

If the proposal for contract interface types is adopted, then all of the preceding rules
about contract types also apply to contract interface types.

## Foreign Contract Calls

An foreign contract call is when a circuit in one contract calls a circuit in another contract.
No changes to the grammar are necessary to support this, because the foreign circuits
will be parsed as ledger accessors.

The Compact type checker must verify that any foreign contract call refers to an exported
circuit of the appropriate contract type (or contract interface type, if that proposal is adopted).

### Example

This example demonstrates the use of contract types and foreign contract calls.
It assumes that the above definition of `AuthCell` is in scope.

```
contract AuthCellUser {

    sealed ledger auth_cell: AuthCell;
    
    constructor (auth_cell: AuthCell) {
        ledger.auth_cell = auth_cell;
    }
    
    export circuit use_auth_cell(): Void {
        const v = ledger.auth_cell.get();
        ledger.auth_cell.set(v + 1);
        return v;
    }
}
```

The `use_auth_cell` circuit in the `AuthCellUser` calls the foreign circuits `get` and `set` from the `AuthCell` contract,
by referring to the `auth_cell` ledger state field in its own ledger state.

Although a contract can call a circuit on a contract to which it has reference, a contract cannot directly access 
the ledger variables or witnesses of another contract. For example, `use_auth_cell` cannot directly access `authorized_pk` 
or `value` in `AuthCell`. Nor can it directly access `sk`. See the [Limitations](#no-external-ledger-variable-accesses) section for a justification of this 
constraint.

### The Compact Standard Library

Due to uncertainty about the semantics of ledger kernel operations and ZSwap witnesses in a version of Compact with
contract definitions, the Compact standard library will be treated as a special case. The kernel operations will be
in-lined using the same techniques that are used currently.

## Limitations

The following limitations are imposed on the version of Compact proposed in this document. Some sections also include 
requirements on `compactc` that the limitations imply.

### Default Contract Ledger Variables

Since there is no natural default value for a contract-typed ledger variable (and to avoid the hornet's nest of `null`), 
all ledger state fields holding contract references must be initialized in the contract constructor. We have the
following requirement:

> `compactc` must statically detect when a contract-typed ledger state field is not initialized and report an informative error.

### Contract Types May Not Appear in Circuit Parameter/Return Types

To minimize the complexity of the contract runtime, contracts may not be passed as arguments to circuits. This constraint 
makes contracts more secure, since allowing consumers of a contract to pass arbitrary contracts in circuit parameters 
means that the state of the contract being called can be modified by a contract that is potentially unknown to the deployer. 
This also leads to the following requirement:

> `compactc` must statically detect the use of contract types in circuit parameters and report an informative error.

Circuits may not return contract values. At the moment, this doesn't look like a security issue. The constraint is imposed
for implementation simplicity and because the implications of such a feature are unclear. 

See [Open Questions](#can-circuits-return-contract-values) for a discussion. This also leads to the following requirement:

> `compactc` must statically detect the use of contract types in circuit return types and report an informative error.

### Contract Types May Not Appear in Witness Parameter/Return Types

If witnesses return contract values, they may inject unknown contracts into a context
where all contracts were otherwise known at deployment time.  This is a security risk
and must be rejected.

> `compactc` must statically detect the use of contract types in witness return types and report an informative error.

There appears to be no security risk created by circuits that deliver contract references into the contract's
private state through witness functions.  On the other hand, there exist ambiguities about the form
and type under which such references would be represented in the TypeScript target.  Thus, this proposal
*allows* the compiler to reject the use of contract types in witness parameter types.

> `compactc` may statically detect the use of contract types in witness parameter types and report an informative error.

### Contracts Must Have a Public State

Each contract must have at least one ledger declaration in its body. This constraint is imposed because, otherwise, the 
defined contract has no ledger state, and it is semantically meaningless to deploy a contract with no ledger state to 
the blockchain. This leads to the following requirement.

> `compactc` must statically detect when a contract attempts to define a contract without a public state and report an informative error.

### No Calling Circuits of Contract Parameters in Constructors

The current proposal does not allow the circuits of contract parameters to be called in the constructor of a contract.
This is because it isn't clear what it means to prove the correctness of a circuit that is called in a constructor. We have
the following requirement:

> `compactc` must statically detect when a constructor attempts to call a circuit defined on a contract argument and report an informative error.

### No Dynamic Contract Instantiation

Although each contract defines a constructor, such constructors may not be invoked to instantiate a contract dynamically.
This constraint is imposed to minimize the complexity of the contract runtime. Although dynamic instantiation is a useful
and desirable feature, more work is required to understand the semantics of dynamic contract instantiation, as well as 
its broader implications for contract security. The key question dynamic instantiation raises is, what does it mean to
prove the correctness of a contract instantiation? There is no clear answer to this question at present, making implementation
infeasible for our timeline.

### No External Ledger Variable Accesses

In object-oriented languages, the fields of a class can often be accessed with dot notation (e.g. `obj.fld`). The ledger
declarations in a contract somewhat resemble field declarations in classes. However, to reduce implementation complexity
and preserve strict, common-sense contract security, we impose the constraint that only the circuits declared in a contract
can access the ledger values declared in the same contract. 
Direct inter-contract ledger state access may be technically feasible, but it is not a critical feature. We
therefore err on the side of caution and disallow it entirely. Future Compact versions could relax the above constraint
by introducing access modifiers (e.g. `public`/`private`) for `ledger` declarations.

### If a Circuit Does Not Exist for a Contract, the Runtime Must Fail With An Informative Error

The runtime representation of a contract reference is the address at which the contract is deployed on the blockchain.
If the runtime attempts to call a circuit that does not exist on a contract (is not present in the corresponding instance of `ContractState`),
then the runtime must fail with an error indicating as much.

### No Parametrically Polymorphic Contracts

The current proposal does not support parametrically polymorphic contracts.

Deploying a contract with one instantiated type and referring to it with another one is unsafe,
and the mechanisms are not yet implemented to detect and prevent such unsafe actions in the Impact VM.
Thus, contracts cannot be parameterized by type.

> `compactc` must reject contract definitions containing type parameters.

Because contract definitions can appear inside modules, and modules can be defined with type parameters,
the possibility exists that type parameters could appear in modules.  The Compact compiler is allowed
to reject this situation entirely.

> `compactc` may reject any appearance of a contract definition inside a type-parameterized module.

## Proving System Changes

Foreign contract calls will use the exact commitment-messaging mechanism proposed [here](./0007-abcird-contract-interfaces.md).
The key difference in this proposal is that commitments occur over contracts instead of interfaces.

## Optional Extensions

### Replace `ledger` with `this` in circuits

Compact uses the `ledger` keyword to declare ledger state fields.
Currently, it also uses the `ledger` keyword to access the ledger state
of the current contract in circuits.  To improve clarity in the presence of
foreign contract references, it may be helpful to replace `ledger` with `this`
when referring to the ledger state of the current contract in circuits.

### Access Pure Foreign Circuits using Dot Notation

It would be very useful for the pure circuits of a contract to be accessible from another contract using dot notation,
even without a reference to an instance of the contract,
similarly to how `static` methods are available to other classes in JavaScript.

## Future Directions

The standard library should be accessed through the same composition mechanisms as regular contracts. The ledger kernel
and ZSwap witnesses are special cases to some extent, but they should not be treated as such unless absolutely necessary.
One idea is to introduce a special `System` contract (analogous to Java's [System](https://docs.oracle.com/javase/8/docs/api/java/lang/System.html) class) that contains the ledger 
kernel and ZSwap witnesses, as well as the circuits for sending and receiving funds. Such should not be instantiable and 
should be accessible from any contract without having to receive it as a parameter.

Future versions should attempt to support [dynamic contract instantiation](#no-dynamic-contract-instantiation) and some
form of interface inheritance, as well as [direct inter-contract](#no-external-ledger-variable-accesses) ledger state access.

## Open Questions

### Can Circuits Return Contract Values?

Calling a foreign circuit that returns a contract value would seem to introduce contract references
into a contract after deployment, violating the goal of knowing all contract references at
deployment time.  On the other hand, it can be proven inductively that the potential call graph
of circuits is still closed at deployment time.

Does this make it acceptable to have contract types in the return types of circuits?

### Can Contract Values Be Stored In ADTs?

This proposal has not explicitly ruled out the storage of contract references in arbitrary ADTs,
because all the referenced contracts must still be provided at deployment time.  On the other hand,
it may be simpler and clearer to restrict contract types to appearing directly as
ledger state field types, perhaps with the additional requirement that they be sealed.
Is this necessary or desirable?

