# ZKIR v3

This document contains a draft specification of ZKIR v3. The purpose
of this specification is twofold: 

1. it is an opportunity to rectify several limitations in the current
   design of ZKIR, and
   
2. we unambigously define the shape and intended semantics of ZKIR
   circuits. 

(TODO: elaborate on the specific design improvements v3 makes over
v2). 

**Contents** 

1. Overview and Key Design Features
2. Language Definition 
3. Typing 
4. Gate Reference
5. Representation (JSON/binary)

## Overview 

Key design features

* SSA with named wires 
* Builtin control flow, explicit joining of paths using `ϕ` functions
* qualified wire polymorphism 
* abstract over available gates to facilitate easy extension/updates 

## Documentation 

ZKIR may in the future become a user-facing component that users may
leverage to construct transactions while circumventing compact and/or
midnight JS. 

In this case, we should properly document the following (TODO: check): 

* Syntax
* Well-formedness (i.e., typing rules) 
* Intended semantics
  - computational behavior: to understand the computation embedded in
	the circuit.  
  - circuit semantics: ZKIR circuits are translated into more primitve
    ZK circuits. These more primitive circuits with their inputs are
    the "statements" for which we generate ZK proofs, which is the
    thing that is _actually_ recorded on the chain. Who is responsible
    for generating these? Where is this documented? 
* Which components use ZKIR and how they depend on it: 
  * Proof server
  * Ledger
  * Compiler 
* Representation format 
  * Binary
  * JSON 
  
Ultimately these may end up in user-facing docs, but should be
documented internally first. 

## Language 

A ZKIR v3 "program" is a circuit, consisting of a sequence of
instructions with nested control flow. Concrete representations of
circuits, as used by the the compiler and proof server, may include
additonal meta-data about the circuit. We discuss these
representations further in this document. 

**Circuits** 

Formally, we define a circuit as a non-empty tree of instructions,
with nested `if`-statements to capture control flow. 

```
circuit := <instruction>
         | LET <var_1> ... <var_n> = <instruction> IN <circuit>
         | IF <var> THEN <circuit> ELSE <circuit>
```

Except for the final insruction in a block block, the output wire(s)
of an instruction are bound to a fresh set of variables, with one new
unique variable for each output wire.

**Instructions** 

There are 2 types of instructions: gate references and phi
functions. 

```
instruction := GATE <gate> <arg_1> ... <arg_n>  
             | PHI <var> <var> 
   
arg := <var>
     | <constant> 
```

A gate reference refers to a known gate, giving an argument
for each input wire of the gate, where arguments are variables
referencing output wires of other instructions, or
constants. Conceptually, gates represent the atomic units of
computation in a circuit. The number of output wires of a gate
reference depends on the specific gate that we refer to. 

A phi function takes exactly 2 variables referencing output wires. The
purpose of a phi function is to join two variables that are assigned
on different control flow paths, and as such it has exactly one output
wire corresponding to the joined wire of its inputs.  

**Variable scoping**

While there is only a single namespace for variables, it is important
to recognize that their scoping may be different depending on the
context in which they are used. More concretely, in the input of phi
functions we may refer to variables that are outside the current
lexical scope. 

Concretely, we distinguish 2 types of variable scopes: 

_Lexical scoping_, where the variables in scope are those variables
that are defined in an ancester node in the abstract syntax tree. 

_Control flow scoping_, where the variables in scope are those
variables that _dominate a predecessor of the current node in the
control flow graph_. By reflexivity of dominance, this (trivially)
includes all variables defined in a predecessor block.

In ZKIR v3, lexical scoping implies dominance, meaning that in the
inputs of a phi function we may refer to all variables in the lexical
scope, but we may also refer to variables that dominate one of its
predecessors in the control-flow graph. 


## Metavariables 

We use the following metavariables to range over syntactic objects: 

```
g ∈ gate 
a ∈ arg 
I ∈ instruction 
Ω ∈ circuit 
x ∈ var 
```

## Typing 

### Type Syntax

Types in ZKIR v3 distinghuish between _signatures_ and _types_. 

A gate _signature_ describes the type of a gate, i.e., the types of
its in- and ouput wires. Signatures support polymorphic quantification
of type variables, as well as qualifying constraints that capture
e.g. that a wire should hold a numeric value.

A _type_ describes the kind of value that flows through a wire. It may
either be a base type such as `field` or `bool`, or a variable. 

The syntax of types in ZKIR v3 is defined as follows: 

```
signature := FORALL <typevar> <signature> 
          | <qualified>
   
qualified := <constraint> => <qualified>
          | [ <type_1> , ... , <type_n> ] ->> [ <type_1> , ... , <type_m> ]

type := <typevar> 
      | <basetype> 

basetype := field | bool | biguing | ecpoint | ... 

constraint := NUM <type>
           | <type_1> <: <type_2>
```

To illustrate, consider the following examples.

1. A negation gate, that inverts a boolean value: 

		neg : `[bool] ->> [bool]`

2. A constant gate, that "forgets" its second wire input: 

		const : `FORALL α (FORALL β ([α, β] => [α]))`

3. A polymorphic addition gate, that adds two numeric values: 

		add : `FORALL α (NUM α => [α, α] ->> [α])` 
		

### Metavariables 

We use the following metavariables ranging over type-level syntactic objects: 

```
Σ ∈ signature
ρ ∈ qualified 
T ∈ type 
B ∈ basetype 
C ∈ constraint 
α ∈ typevar 
```

### well-scopedness of Types and Signatures

Types and signatures are well-scoped with respect to a type
environment `Δ` which tracks the lexical scope of type
variables. Judgments of the form `Δ ⊢ Σ`, `Δ ⊢ T`, etc... prove that a
signature `Σ` or type `T` is well-scoped with respect to type
environment `Δ`. 

A _closed_ signature is a signature that is well-scoped under the
empty environment: `∅ ⊢ Σ`. Similarly, a closed type is a type that is
well-scoped under the empty environment: `∅ ⊢ T`. 


**Variable quantification**

A universally quantified signature is well-scoped if the
quantification's body is well-scoped with respect to the surrounding
type environment extended with the quantified variable `α`:

```
Δ,α ⊢ Σ 
--------
Δ ⊢ ∀α.Σ 
```

**Constraints** 

A qualified type `C => ρ` is well-scoped, if both `C` and `ρ` are
well-scoped. 

```
Δ ⊢ C 
Δ ⊢ ρ 
----------
Δ ⊢ C => ρ
```

**Gates** 

A gate type is well-scoped if all its in and output wires have a
well-scoped type. 

```
1 <= x <= n , 1 <= y <= m 
Δ ⊢ T_ix 
Δ ⊢ T_oy 
---------------------------------------------------
Δ ⊢ [ T_i1 , ... , T_in ] ->> [ T_o1 , ... , T_om ]
```

**Variable reference**

A variable reference `α` is well-scoped if `α` is a member of `Δ`. 

```
α ∈ Δ 
-----
Δ ⊢ α 
```

**Base types** 

Base types cannot refer to type variables, so they are trivially
well-scoped. 

```
-----
Δ ⊢ B
```

**Numeric constraint** 

A constraint that a type `T` is numeric is well-scoped if `T` is
well-scoped. 

```
Δ ⊢ T 
--------------
Δ ⊢ Numeric(T)
```

**Subtype constraint** 

Subtype constraints are well-scoped if the subtype `T_1` and supertype
`T_2` are both well-scoped. 

```
Δ ⊢ T_1 
Δ ⊢ T_2 
--------------
Δ ⊢ T_1 <: T_2
```

### Typing Rules 

## Gate Reference 

## Semantics 

(TODO: several things to clarify

* Proof preimage 
* branching 
* bottom values representing untaken paths
* impact 

) 

## Implementation 

Where and how should a re-design of ZKIR be implemented? 

(TODO: cross-check and extend this info w/ input from relevant
architects & engineering teams). 

**Compiler** 

Generates circuits as part of the compilation process. 

* Generation pass would need to be updated
* Current generation pass is AFAIK an "identity" pass that prints a
  JSON string as a side-effect. This really ought to be factored into
  a separate Nanopass IR definition. 
  
**Proof server** 

(TODO: details) 

**Ledger** 

(TODO: details) 

### Consideration

Several components deal with ZKIR. Right now, it appears that all of
them maintain their own internal definition of the representation,
making the current setup very britlle. The preferred setup would have
a single source of truth for the syntax of ZKIR circuits that these
components draw from.

More of a "nice to have" from the perspective of software robustness
and maintainability. 

## Represenations

* JSON
* BINARY 

(TODO: what meta-data 
