# Proposal 0010: Composable Contracts Syntax

This document proposes changes to the Compact syntax to support
1. the declaration of several contracts in a single file
2. ledger state fields holding references to contracts
3. circuits making calls to the circuits of other contracts

## Terminology

- A Compact source _program_ is a set of contract definitions and pure circuit definitions along with
  supporting items.
- A Compact _contract_ is a set of ledger declarations, witness declarations, and circuit definitions,
  along with supporting items.
- In both case, _supporting items_ are pragmas, include forms, module definitions,
  import declarations, export declarations, type (struct and enum) definitions, and
  external circuit declarations.
- The _target files_ produced by the Compact compiler for a contract contain the executable
  TypeScript code (in the form of a TypeScript declaration file and
  a JavaScript implementation file), the proof circuits, and the
  proof keys for the contract.
- The _ledger state_ of a contract is the portion of the contract state that is stored at a contract address on the ledger.
- The _private state_ of a contract is the state that is queried or updated by the witnesses declared in a contract.
- The _runtime_ of a contract is the portion of the contract executable code that is responsible for managing the intermediate
  ledger and private states throughout the execution of a circuit.
- An _instance_ of a contract is a specific deployed instantiation of a contract type, with its own ledger and private state.
- An _inter-contract call_ is when a circuit in one contract calls a circuit defined in another contract
  directly and as part of a single transaction.
  (Some other smart contract systems call this an "internal" contract call, but we use the term
  "inter-contract" to avoid confusion with other, more obvious meanings for "internal".)

## Problem Statement

Compact currently provides no means for a contract to reuse the functionality of another contract, 
other than copying the code from one contract into another.
Contract developers want to write contracts that depend on already-deployed contracts.

Concretely, the need is for contract *B* to hold a reference to another contract *A* 
and for the circuits of *B* to be able to call circuits in *A*, directly and in a single
transaction, so that *B*’s functionality depends on the functionality of *A*.

Meeting this need requires the introduction of *contract types* within Compact, 
so that ledger fields and variables may hold references to contracts.

## Compact Syntax Changes

### Programs

We assume throughout this proposal that the proposal for sealed ledger state is adopted.

With this proposal, programs become, in essence, collections of contract definitions and pure
circuit definitions.
So to the existing set of program elements we add a program element for contract definitions:

```
PELT   --> CTDEFN
```

Since witness declarations, ledger declarations, and constructor definitions are inherently
contract-level entities, PELT can no longer be one of these.

```
PELT   --> WDECL        _removed_
       --> LDECL        _removed_
       --> CONSDEFN     _removed_
```

Modules at the program level can contain exactly the same set of PELTs as a program.

### Contract Definitions

Prior to this proposal, there is no name *in Compact* for the ledger state, witnesses, and circuits that describe a contract.
In order to refer to contract types in Compact, it is necessary to add a construct to the language
that collects the elements of the contract and associates them with an identifier.
That identifier becomes available as a *contract type* in Compact, used to describe references
to any instance of the contract.

With this proposal, we adopt the following grammar for contract definitions:

```
CTDEFN  --> EXPORT^OPT contract CONTRACT-NAME { CTELT ... }

CTELT   --> CTMELT
        --> CONSDEFN

CTMELT  --> PRAGMA
        --> INCLD
        --> CTMDEFN
        --> IDECL
        --> XDECL
        --> LDECL
        --> CDEFN
        --> EDECL
        --> WDECL
        --> STRUCT
        --> ENUMDEF

CTMDEFN --> EXPORT_OPT module MODULE-NAME TPARAMS_OPT { CTMELT ... }

EXPORT --> export
```

As specified by the grammar, a constructor definition can appear only at
the top level of a contract body and not within a module.
Furthermore, although not specified by the grammar, at most one constructor
definition can appear in each contract.

An empty contract is valid.

As is the case for the current Compact version, circuits that are exported from a contract
are externally callable, while circuits that are not exported from a contract are not.

### Exported vs Non-Exported Contracts

The Compact compiler produces target files for each contract whose type name is
exported by a program.
The contract type name exported from the program is used as a stem for various names
outside of Compact, such as target file names and TypeScript type names.
For a contract defined in and exported from a module, then imported by and reexported
from a program, the contract type name might differ from its original name due to the
addition of a prefix when the module is imported.

No target files are produced for a contract whose type name is not exported by a program,
though executable portions of its circuits may appear in the target files of
exported circuits for purposes of performing inter-contract calls.
This permits the definition of a separately compiled and deployed contract to be included
or imported into a program for the sole purpose of allowing the contract to be called from
other contracts for which target files are produced.
It also allows the programmer to resolve naming conflicts for like-named contracts
imported from different modules via the existing support for import prefixing.

If the proposal for contract interfaces is adopted, interfaces provide another way for
one contract to call another without generating target files for the other.

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

## Contract References

Any contract type name in scope may be used as the type of a ledger state field or a local `const` binding.
Such a field or variable holds a *reference to an instance of a contract of that type*.
Constructor parameters and witness function parameters may also be declared to hold contract references.
**Circuit parameter types, circuit return types, and witness return types may not incorporate contract types.**

There is no "null" contract reference value and no default value for contract types.

The preceding rules imply that all ledger state fields or ADTs holding contract references must be initialized
in the constructor of a contract.  Furthermore, almost all uses of ledger state fields
holding contract references may be declared `sealed` (assuming the adoption of the proposal for sealed ledger state).
The only way a ledger state field of contract type could be updated is with some other value in the ledger state,
already provided at the time a contract was deployed.  In other words, all possible references from one
contract to another are known at the time the referring contract is deployed, regardless of sealing declarations.

It appears that no changes to the Compact grammar are necessary to support contract references
and the types that describe them.
They will be parsed in the same way as user-defined types, such as enumerations and structure types.

Changes to the type checker are clearly required to support contract types,
both to reject programs that attempt to use contract types in invalid places
and to validate inter-contract calls, described in the next section.

If the proposal for contract interface types is adopted, then all of the preceding rules
about contract types also apply to contract interface types.  That is, a variable
may be declared to have a contract interface type, meaning that the variable holds a reference
to an instance of some contract exporting at least the set of circuits declared in the interface.

## Inter-Contract Calls

An inter-contract call is when a circuit in one contract calls a circuit in another contract.
No changes to the grammar are necessary to support this, because the references to circuits
in another contract will be parsed as ledger accessors.

The Compact type checker must verify that any inter-contract call refers to an exported
circuit of the appropriate contract type (or contract interface type, if that proposal is adopted).

### Example

This example demonstrates the use of contract types and inter-contract calls.
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

The `use_auth_cell` circuit in the `AuthCellUser` calls the circuits `get` and `set` from the `AuthCell` contract,
by referring to the `auth_cell` ledger state field in its own ledger state.

Although a contract can call a circuit on a contract to which it has reference, a contract cannot directly access 
the ledger variables or witnesses of another contract. For example, `use_auth_cell` cannot directly access `authorized_pk` 
or `value` in `AuthCell`. Nor can it directly access `sk`. 
See the [Further Constraints](#no-external-ledger-variable-accesses) section for a justification of this 
constraint.

### The Compact Standard Library

Due to uncertainty about the semantics of ledger kernel operations and ZSwap witnesses in a version of Compact with
contract definitions, the Compact standard library will be treated as a special case. The kernel operations will be
in-lined using the same techniques that are used currently.

## Further Constraints

The following constraints are imposed on the version of Compact proposed in this document. Some sections also include 
requirements on `compactc` that the constraints imply.

### Default Contract Ledger Variables

Since there is no natural default value for a contract-typed ledger variable (and to avoid the hornet's nest of `null`), 
all ledger state fields holding contract references must be initialized in the contract constructor. We have the
following requirement:

> `compactc` must statically detect when a contract-typed ledger state field might not be initialized and report an informative error.

### No Calling Circuits of Contract Parameters in Constructors

Contract references may be passed as parameters to constructors, but
the current proposal does not allow the invocation of circuits on those references *within the constructor*.
This restriction is intended to limit initial implementation complexity and might be lifted in a later version.

> `compactc` must statically detect the possibility of an inter-contract call in a constructor and report an informative error.

### Contract Types May Not Appear in Circuit Parameter/Return Types

To minimize the complexity of the contract runtime, contracts may not be passed as arguments to circuits. This constraint 
makes contracts more secure, since allowing consumers of a contract to pass arbitrary contracts in circuit parameters 
means that the state of the contract being called can be modified by a contract that is potentially unknown to the deployer. 
This also leads to the following requirement:

> `compactc` must statically detect the use of contract types in circuit parameters and report an informative error.

Circuits may not return contract values. This constraint is imposed for implementation simplicity.
See [Open Questions](#can-circuits-return-contract-values) for a discussion. 

This also leads to the following requirement:

> `compactc` must statically detect the use of contract types in circuit return types and report an informative error.

### Contract Types May Not Appear in Witness Return Types

If witnesses return contract values, they may inject unknown contracts into a context
where all contracts were otherwise known at deployment time.  This is a security risk
and must be rejected.

> `compactc` must statically detect the use of contract types in witness return types and report an informative error.

There appears to be no security risk created by circuits that deliver contract references into the contract's
private state through witness functions.  Thus, witness parameter types may incorporate contract types.

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

## Proving System Changes

Inter-contract calls will use the exact commitment-messaging mechanism proposed [here](./0007-abcird-contract-interfaces.md).
The key difference in this proposal is that commitments occur over contracts instead of interfaces.

## Optional Extensions

### Eliminate the `ledger` qualifier for accessing ledger state

Compact uses the `ledger` keyword to declare ledger state fields.
Currently, it also uses the `ledger` keyword as a prefix to access the ledger
state of the current contract in circuits.  Calling circuits and
witnesses requires no such qualifier.

The programmer experience will be more consistent if the `ledger.` prefix is
eliminated, so that ledger fields are simply in scope inside the circuits
of a contract.  The presence of multiple contracts in the same
Compact code aggravates the problem, because it is no longer meaningful
to refer to *the* ledger state when each contract has its own ledger state.

Name resolution should follow standard scoping rules, and modules make it possible
to hide names that should not be visible outside a narrow scope.

### Access Pure Circuits in Other Contracts using Dot Notation

It would be very useful for the pure circuits of a contract to be accessible from another contract using dot notation,
even without a reference to an instance of the contract,
similarly to how `static` methods are available to other classes in JavaScript.
If the proposal for contract interface types is adopted, then this feature would apply
only to the pure circuits of concretely defined contracts, not to interfaces.

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

Calling a circuit in another contract that returns a contract value might seem to introduce contract references
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

