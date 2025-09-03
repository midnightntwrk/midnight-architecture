
# A New Version of ZKIR

This document details a proposed re-design of ZKIR. 

## Introduction 

The reasons for re-designing ZKIR are: 

* lacks a specification of its syntax and semantics, 
* does not contain any type information, and 
* does not reify many capabilities of the underlying proof system. 

As a result, the precise process of embedding contract logic into
circuits remains opaque to both internal and external users
alike. Furthermore, contract developers that use Compact for defining
smart contract logic cannot take full advantage of the power of the
underlying proof system.

The core issue is that current ZKIR only targets a limited subset of
the functionality exposed by the proof system through the `ZkStdlib`
interface defined in `compact_std_lib.rs` (in the `midnight-zk`
repository). This has two main consequences. First, it means that
there is a chunk of functionality that cannot be accessed through
Compact, because it lies outside the image of the ZKIR "virtual
machine". Second, ZKIR is unityped and treats every value as an
element of the native field whereas both Compact and the proof system
track more fine-grained information about types, which may lead to
redundancies and/or inefficiencies.

### Design Philosophy 

Users should be able to take full advantage of the capabilities of
Midnight's proof system. This means that all functionality exposed by
the `ZkStdlib` should be accesible through ZKIR, one way or
another. Wherever the proof system maintains type information, so
should ZKIR.

### Contents

We structure the design proposal as follows:

1. Overview and Key Design Features
2. Language Definition 
3. Typing 
4. Gate Reference
5. Representation (JSON/binary)

## Overview of the Language 

Computations are represented as an arithmetic circuit using a Static
Single Assignment (SSA) form, where each variable, conceptualized as a
named wire, is assigned a value exactly once. This structure provides
a clear and explicit data-flow graph, simplifying many compiler
analyses and optimizations. To accommodate conditional logic, the
language incorporates built-in control flow constructs. Crucially, it
maintains the SSA property across divergent execution paths by using
explicit ϕ (phi) functions. When control flow paths merge, a ϕ
function selects the appropriate incoming wire based on which path was
taken, ensuring that every wire continues to have a single,
unambiguous source.

The language features type system built on qualified wire
polymorphism, an extension of Hindley-Milner style inference that
incorporates type class-like constraints. This allows operations to be
abstractly defined over any wire type that satisfies certain
properties or "qualifications." For example, an addition gate can be
specified to operate on any type `T` that fulfills a suitable
constraint, rather than being hardcoded for specific types like
`BigUint` or field elements.

A key design principle is the strict separation between program
structure (if-blocks + phi nodes) and arithmetic operations (gates):
control flow is handled orthogonally from the computation performed by
gates. This means the core features—the type system, control-flow
constructs, and overall semantics—are defined completely independently
from the concrete set of gates available. This modularity allows the
language to be easily extended with new types and operations. 

## Formal Syntax Definition  

A ZKIR v3 circuit consists of a sequence of instructions with nested
control flow, in SSA form.

**Circuits** 

Formally, we define a circuit as a sequence of instructions: 

```
circuit := [<instruction>]
```

Where we use `<..>` to denote a metavariable/nonterminal, and square
brackets to denote a sequence.

**Instructions** 

There are 2 types of instructions: gate references and conditional
branching.

```
instruction := (<var_1>, ..., <var_n>) <- GATE <gate> <arg_1> ... <arg_n>  
             | if(<var>) then { <circuit> } else { <circuit> } join { [join] }
			 
join := <var> ← phi(<var>,<var>) 
   
arg := <var>
    |  <constant> 
	|  (<arg>,<arg>) 
	|  {<arg>, ... , <arg>}
	|  just(<arg>) 
	|  nothing 
```

A gate reference refers to a known gate, giving an argument for each
input wire of the gate, where arguments are either variables or
constants. A gate reference binds its output to variables `var_1`
through `var_n` in the remainder of the current lexical
scope. Conceptually, gates represent atomic units of computation
corresponding to operations exposed in the proof system's API. In
practice, these operations can represent complex computation (such as
hashing) built out of many smaller cryptographic primitives.

A conditional takes a variable `var`, and depending on its value,
executes the corresponding branch . Every conditional must be followed
by a (possibly empty) sequence of joins/phi nodes. The purpose of a
join is to make the wire outputs of gate references in conditional
branches available in the lexical scope **after** the if-block. 

**Variable Scoping**

Typically, in SSA with explicit joins, we must maintain a distinction
between lexical scope and control-flow scope, where the inputs to phi
nodes are control-flow scoped. By restricting the invokation of phi
nodes to an explicit sequence following conditionals, we avoid the
need for control-flow scoping. Instead, the first argument to a join
is scoped by the lexical scope at the _end_ of the `THEN` branch, and
vice versa. 

This setup is akin to having a sequence of phi nodes after an
if-statement, but this way we enforce, by consruction, that the input
variables to a join must dominate a predecessor of the current
block. Furthermore, it enforces by construction that for each phi
node, for every possible way control may flow to that node, exactly
`1` of the variables will be assigned, so the result of joining is
always defined and canonical.


## Metavariables 

We use the following metavariables to range over syntactic objects: 

```
g ∈ gate 
a ∈ arg 
I ∈ instruction 
Ω ∈ circuit 
φ* ∈ joins 
φ ∈ join 
x ∈ var 
k ∈ constant 
```

## Type System 

ZKIR v3 will be statically and strongly typed. 

Types in ZKIR v3 distinghuish between _signatures_ and _types_. 

A gate _signature_ describes the type of a gate, i.e., the types of
its in- and ouput wires. Signatures support polymorphic quantification
of type variables, as well as qualifying constraints that capture
e.g. that a wire should hold a numeric value.

A _type_ describes the kind of values that flows through a wire, or
assiciated with private inputs, public inputs, and constants.  Types
may either be a base type such as `field` or `bool`, or a variable.

***Semantics of polymorphism** 

Polymorphism in ZKIR mimis the use of generic trait parameters in the
proof system. In practice, this means that polymorphism in ZKIR is a
blend of parametric polymorphism, and qualified/ad-hoc polymorphism. 

In summary: 

* Polymorphic types are *ad-hoc*: we deploy a type-directed semantics
  that selects the corresponding operation in the proof system,
  depending on how a variable is instantiated. 
  
* Polymorphic curves and fields are *parametric*: we use the same
  operation in the proof system, independent of how a variable is
  instantiated.

A crucial stipulation about ZKIR's polymorphism, is that **only
monomorphic ZKIR circuits can be interpreted as an arithmetic
circuit**. That is, if a circuit's typing still contains unassigned
type variables, we cannot translate gate references into calls to the
proof system's API. 

### Types

The syntax of types in ZKIR v3 is defined as follows: 

```
standalone-field := ... --- fields not associated with an elliptic curve 

field := <curve>.<fieldtype> 
	  |  <standalone-field>
	  |  native 
	  |  <name> 

fieldtype := base | scalar 

curve := jubjub 
      |  bls12-381 
	  |  secp256k1 
	  |  native 
	  |  <name> 

basetype := Element(<field>)
         |  Bit             
         |  Byte            
         |  BigUInt        
         |  Point(<curve>)      
         |  Vector(<type>)   
		 |  <name>

-- Defines the native curve to be the jubjub curve 
NativeCurve : curve 
NativeCurve = jubjub 

 -- defines the native field to be the bls scalar field
NativeField : field 
NativeField = bls12-381.scalar
```

For example, types we could write are 

```
Point(native)  --> ec point on the native curve
Element(secp256k1.scalar) --> elements of the Secp256k1 scalar field 
Point(C)   --> an ec on the variable curve C 
Element(F) --> an element on the variable curve F 
Vector(T) --> a vector with elements of variable type T 
```

### Mapping ZKIR types to types in the Proof system 

Types in ZKIR v3, with the exception of type variables, can be mapped
onto Rust types. 

```
⟦-⟧ : basetype → Rust type 
⟦ Element native   ⟧ = AssignedNative<⟦native⟧>
⟦ Element(<field>) ⟧ | ⟦field⟧ ≡ ⟦native⟧ = AssignedNative<⟦native⟧> 
                     | otherwise          = AssignedField<⟦native⟧, ⟦field⟧ , MultiEmulationParams>
⟦ Bit              ⟧ = AssignedBit<⟦native⟧>
⟦ Byte             ⟧ = AssignedByte<⟦native⟧> 
⟦ BigUint          ⟧ = AssignedBigUint<⟦native⟧> 
⟦ Point(<curve>)   ⟧ | ⟦curve⟧::Base ≡ ⟦native⟧ = AssignedNative<⟦curve⟧>
                     | otherwise                = AssignedForeignPoint<⟦native⟧,⟦curve⟧,MultiEmulationParams>
⟦ Vector(<type>)   ⟧ = AssignedVector<⟦native⟧, ⟦type⟧ >
⟦ <name>           ⟧ = ** ERROR: No rust type corresponding to type variables **

⟦-⟧ : field → Rust type
⟦ native        ⟧ = blstrs::Scalar -- defines the native field to be the bls scalar field
⟦ jubjub.base   ⟧ = blstrs::Scalar
⟦ jubjub.scalar ⟧ = blstrs::Fr
⟦ bls.base      ⟧ = blstrs::Fp 
⟦ bls.scalar    ⟧ = blstrs::Scalar
⟦ secp.base     ⟧ = Secp256k1::Fp
⟦ secp.scalar   ⟧ = Secp256k1::Fq 
⟦ <name>        ⟧ ** ERROR: No rust type corresponding to field variables ** 

⟦-⟧ : curve → Rust type 
⟦ jubjub ⟧ = blstrs::JubjubExtended
⟦ bls    ⟧ = blstrs::G1Projective 
⟦ secp   ⟧ = halo2curves::secp256k1
⟦ native ⟧ = blstrs::JubjubExtended -- defineds the native curve to be the jubjub curve
⟦ <name> ⟧ = ** ERROR: no rust type corresponding to curve variables ** 
```


## Type Signatures

The "type" of gates in ZKIR is described by a signature. Signatures
close over types with universal quantification of type or curve/field
variables, as well as qualified constraints. 

A signature itself consists of a list of inputs and outputs. The
outputs of a gate are a list of types corresponding to the type of
values flowing through its output wires. Inputs have slightly more
structure, and can optional, or grouped into tuples or
lists. 

Furthermore, each input is associated with a *mode* describing the
orign of the value. Modes informally correspond to the different
columns in PLONK-style proof systems, and are there guard against
improper mixing of different types of values. The output(s) of a gate
are always in-circuit variables. Hence we don't annotate them with a
modality; they have the `wire` modality by default.

```
signature := ∀ <name> <kind> <signature> 
          |  <qualified>
	  
kind      := type | curve | field 
		  
qualified := <constraint> => <qualified> 
          |  [<input>] ->> [<type>]
		  
constraint := Assign(<type>)
           |  Assert(<type>) 
		   |  Eq(<type>) 
		   |  Arith(<type>) 

input := <mode>:<basetype> 
       | (<input>,<input>) 
	   | <input>∗ 
	   | <input>?
	   
mode := const 
	 |  wire 
	 |  pub 
	 |  priv
```

For example, we can write the following signatures corresponding to
operations exposed by the proof system's API:

`assign : ∀ (T:type) . Assign(T) ⇒ { priv:T } ↠ { T }`

`assert_equal : ∀ (T:type) . Assert(T) ⇒ { wire:T, wire:T } ↠ { }`

`add_constant : ∀ (T:type) . Arith(T) ⇒ { wire:T, const:T } ↠ { T }`

`ec_add : ∀ (C:curve) . { wire:Point(C), wire:Point(C) } ↠ { Point(C) }` 

		
### Mapping inputs to types in the Proof system 

The proof system maintains type wrappers to distinguish between
private inptus, constants, and in-circuit variables. Inputs are mapped
onto rust types as follows:

```
⟦_⟧ : input -> Rust type 
⟦ priv:T                ⟧ = Value<⟦T⟧::Element>
⟦ pub:T                 ⟧ = Value<⟦T⟧::Element> 
⟦ wire:T                ⟧ = ⟦T⟧ 
⟦ const:T               ⟧ = ⟦T⟧::Element 
⟦ (<input_1>,<input_2>) ⟧ = (⟦input_1⟧,⟦input_2⟧) 
⟦ <input>*              ⟧ = &[ ⟦ input ⟧ ]
⟦ <input>?              ⟧ = Option<⟦ input ⟧> 
```

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
variables. Judgments of the form `Δ ⊢ Σ`, `Δ ⊢ T`, etc... prove
that a signature `Σ` or type `T` is well-scoped with respect to type
environment `Δ`. Types are additionally associated with a kind, where
a judgment of the form `Δ ⊢ T : k` proves that `T` has is well-scoped
under context `Δ` and has kind `k`.

A _closed_ signature is a signature that is well-scoped under the
empty environment: `∅ ⊢ Σ`. Similarly, a closed type is a type that is
well-scoped under the empty environment: `∅ ⊢ T`. 


**Variable quantification**

A universally quantified signature is well-scoped if the
quantification's body is well-scoped with respect to the surrounding
type environment extended with the quantified variable `α`:

```
Δ,α:k ⊢ Σ 
─────────────
Δ ⊢ ∀(α:k).Σ 
```

**Constraint Qualification** 

A qualified type `C => ρ` is well-scoped, if both `C` and `ρ` are
well-scoped. 

```
Δ ⊢ C 
Δ ⊢ ρ 
──────────
Δ ⊢ C => ρ
```

**Gate signature** 

A gate type is well-scoped if all its inputs and outputs well-scoped: 

```
1 <= x <= n , 1 <= y <= m 
Δ ⊢ I_ix 
Δ ⊢ T_oy 
───────────────────────────────────────────────────
Δ ⊢ [ I_i1 , ... , I_in ] ->> [ T_o1 , ... , T_om ]
```

**Inputs** 

Inputs are well-scoped if all types referenced in the intput are
well-scoped:


```
m ∈ { const , wire , pub, priv } 
Δ ⊢ T 
────────────────────────────────
Δ ⊢ m:T 
```

```
Δ ⊢ I_1 
Δ ⊢ I_2
───────────────
Δ ⊢ (I_1 , I_2)
```

```
Δ ⊢ I 
──────
Δ ⊢ I* 
```

```
Δ ⊢ I 
──────
Δ ⊢ I? 
```


**Types** 

Base types, that do not refer to a type, field, or curve variable, 
are trivially well-scoped.

```
B ∉ {ELEMENT , POINT , VECTOR, TVAR}
────────────────────────────────────
Δ ⊢ B
```

Types that refer to one or more variables are well-formed if their
variables are bound in `Δ`, to the right kind depending on where the
variable occurs.

For example, a type variable reference `α` is well-scoped if `T` is a
member of `Δ` and has kind `type`.

```
T:type ∈ Δ 
──────────
Δ ⊢ T 
```

Similarly, field and curve variables are well-formed if they are
associated with their respective kind in `Δ`.

**Constraints** 

Constraints are well-formed if their type parameters are well-formed, e.g.: 

```
Δ ⊢ T 
────────────
Δ ⊢ Arith(T)
```

## Type System

**Typing Contexts**

Typing depends on the following contextual information:

* **𝓖**: A set of available gates and their signatures.
* **𝓟**: A set of predicate witnesses.
* **Π**: A set of private inputs and their types.
* **Ψ**: A set of public inputs and their types.
* **K**: A mapping from types to a set of available constants.

The contexts themselves must be well-formed. A context is well-formed
if all signatures and types it contains are well-scoped under an empty
type environment `∅`.

For gates, this means for any gate `g` with signature `Σ` in `𝓖`, its
signature must be closed and well-formed:

`∀ (g : Σ ∈ 𝓖) . ∅ ⊢ Σ`

Similarly, the types of all private and public inputs must be closed
and well-formed:

`∀ (x : T ∈ Π) . ∅ ⊢ T`

`∀ (x : T ∈ Ψ) . ∅ ⊢ T`

The context for in-circuit variables (wires) is not a separate static
context but is represented by the memory shape `μ` within the typing
judgments. The set of available wires and their types at any point in
the circuit is given by `wires⟨μ⟩`.

The type system is defined by a set of extrinsic judgments over the
circuit's syntax. These judgments determine the well-typedness of
circuits and their components, relying on contextual information about
available gates (𝓖), predicate witnesses (𝓟), private inputs (Π),
public inputs (Ψ), and constants (K).

### Memory Shapes 

At "runtime", ZKIR programs have a memory containing values for all
visible wires. To statically track what the memory of a ZKIR circuit
looks like, we define "memory shapes", as an abstract representation
of what a Circuit's memory looks like.

We define the set of memory "shapes" as the free semiring over closed
types.

```
μ := 𝟘 
  |  𝟙 
  |  μ ⊕ μ
  |  μ ⊗ μ 
  |  ⟪ T ⟫ 
```

Where the "additive" binary operation corresponds to branching: `(μ1 ⊕
μ2)` is the memory of a program with two branches, its arguments
corresponding to the shape the memory would have if we took that
branch.

The "multiplicative" binary operation corresponds to sequencing: `(μ1
⊗ μ2)` is the memory of a program sequence, the arguments
corresponding to memory of the first and second halves of the
sequence.

The additive identiy is the memory shape of a branch we cannot
take. No program exists with memory `𝟘`.

The multiplicative identity is the memory shape of a program that
allocates no new variables. An empty sequence of instructions has
memory `𝟙`.

### Lexical scope 

The memory shape of a program corresponds to its control-flow
graph. Lexical scope can be defined a projection out of the memory,
where we ignore branches. That is, the memory shape forms a tree-like
structure, with types at the leaves. The lexical scope at any point in
a program is the inorder traversal of this tree after pruning additive
nodes. Or, in human language: at a given point in a circuit we can
refer to any previously created wire, except if we have to go *into a
branch of an earlier conditional*. Wires declared in previous `if`
blocks are out of scope, unless they are bound by one of its joins.

### Judgments for Circuits

**Circuit Typing: `μ » Ω » μ′`**

This judgment states that in a memory context `μ`, the circuit `Ω` is
well-typed and produces a new memory shape `μ′`. The final memory
shape after execution will be `μ ⊗ μ′`.

* **Rule `nil`**: An empty circuit `ε` is well-typed and produces an
  empty memory extension (`𝟙`).

    ```
    ─────────
    μ » ε » 𝟙
    ```

* **Rule `seq`**: A sequence of instructions `I; Ω` is well-typed if
  the instruction `I` produces memory `μ₁`, and the subsequent circuit
  `Ω` is well-typed in the new context `μ ⊗ μ₁`, producing memory
  `μ₂`. The total new memory produced is `μ₁ ⊗ μ₂`.

    ```
    μ » I » μ₁
    (μ ⊗ μ₁) » Ω » μ₂
    ──────────────────
    μ » I; Ω » μ₁ ⊗ μ₂
    ```

### Instruction Typing: `μ » I » μ′`

This judgment asserts that an instruction `I` is well-typed in a
memory context `μ` and produces a memory extension `μ′`.

* **Rule `branch`**: A conditional `if x then Ω₁ else Ω₂ join φ*` is
  well-typed if the condition `x` is a `bit`, both branches `Ω₁` and
  `Ω₂` are well-typed, and the join sequence `φ*` correctly merges
  their resulting memory shapes.

    ```
    x : Bit ∈ wires⟨ μ ⟩
    μ » Ω₁ » μ₁
    μ » Ω₂ » μ₂
    μ₁ | μ₂ » φ* » μ′
    ───────────────────────────────────────────────────
    μ » if x then Ω₁ else Ω₂ join φ* » ((μ₁ ⊕ μ₂) ⊗ μ′)
    ```

* **Rule `gate`**: A gate call `(x₁...xₘ) ← g(a₁...aₙ)` is well-typed
  if the gate `g`'s signature `Σ` can be instantiated for the given
  arguments, and all arguments are well-typed. The resulting memory
  shape `⟪ T∗ ⟫∗` is derived from the gate's output types.

    ```
    g : Σ ∈ 𝓖
    𝓟 ⊩ (ι∗ , T∗) ←inst⟨ Σ ⟩
    μ ⊢ aᵢ ◂ ιᵢ   (for 0 < i < len(ι∗))
    ───────────────────────────────────
    μ » (x₁...xₘ) ← g(a₁...aₙ) » ⟪ T∗ ⟫∗
    ```

### Argument Typing: `μ ⊢ a ◂ ι`

This judgment checks if an argument `a` conforms to the expected input
type `ι` within the memory context `μ`.

* **Rules `nothing` and `just` (for optional inputs `_?`)**: An
  optional argument can be `nothing`, which is always well-typed, or
  `just a`, which is well-typed if `a` is.

    ```
    ────────────────
    μ ⊢ nothing ◂ ι?

    μ ⊢ a ◂ ι
    ───────────────
    μ ⊢ just a ◂ ι?
    ```

* **Rule `pair`**: A pair of arguments `(a₁, a₂)` is well-typed if
  each argument is well-typed against its corresponding input type.

    ```
    μ ⊢ a₁ ◂ ι₁
    μ ⊢ a₂ ◂ ι₂
    ───────────────────────
    μ ⊢ (a₁, a₂) ◂ (ι₁, ι₂)
    ```

* **Rule `slice`**: A list of arguments `{a₁...aₙ}` is well-typed if
  every argument is well-typed against the list's input type.

    ```
    ∀i. μ ⊢ aᵢ ◂ ι
    ──────────────────
    μ ⊢ {a₁...aₙ} ◂ ι∗
    ```

* **Rule `constant`**: A constant `k` is well-typed if it is a known
  constant of type `T`.

    ```
    k ∈ K(T)
    ───────────────────
    μ ⊢ k ◂ const ⦂[ T ]
    ```

* **Rule `priv`**: A variable `x` is a valid private input if it is
  defined in the private input context `Π`.

    ```
    x : T ∈ Π
    ──────────────────
    μ ⊢ x ◂ priv ⦂[ T ]
    ```

* **Rule `pub`**: A variable `x` is a valid public input if it is
  defined in the public input context `Ψ`.

    ```
    x : T ∈ Ψ
    ─────────────────
    μ ⊢ x ◂ pub ⦂[ T ]
    ```

* **Rule `wire`**: A variable `x` is a valid wire input if it
  corresponds to a wire of type `T` in the current memory `μ`.

    ```
    x : T ∈ wires⟨ μ ⟩
    ──────────────────
    μ ⊢ x ◂ wire ⦂[ T ]
    ```

### Join Typing: `μ₁ | μ₂ » φ* » μ`

This judgment defines how to merge two memory shapes `μ₁` and `μ₂`
from different branches into a single shape `μ` using a sequence of
join instructions `φ*`.

* **Rule `nil`**: An empty join sequence `ε` merges two memory shapes
  into an empty memory extension `𝟙`.

    ```
    ───────────────
    μ₁ | μ₂ » ε » 𝟙
    ```

* **Rule `phi`**: A join sequence `x ← phi(x₁, x₂); φ*` is well-typed
  if a wire of type `T` exists in both branches (corresponding to `x₁`
  and `x₂`), and the rest of the sequence `φ*` is well-typed.

    ```
    x₁ : T ∈ wires⟨ μ₁ ⟩
    x₂ : T ∈ wires⟨ μ₂ ⟩
    μ₁ | μ₂ » φ* » μ′
    ───────────────────────────────────────────────
    μ₁ | μ₂ » x ← phi(x₁, x₂); φ* » (⟪ x : T ⟫ ⊗ μ′)
    ```

## Semantics

A ZKIR circuit has two distinct but interconnected semantics: a
**computational semantics** and a **relational semantics**.
Understanding both is key to seeing how ZKIR programs are executed by
a prover and verified on-chain.

### Overview

When a user initiates a call transaction, they generate a zero-knowledge
proof of the form $R(s, w)$. In this proof:
* $R$ is a relation that mathematically encodes the logic of the ZKIR
  circuit.
* $s$ is the public "statement" being proven. This includes the public
  inputs, the circuit's outputs, and a transcript of public
  operations.
* $w$ is the private "witness" that proves the statement is the result
  of a valid execution. This includes private inputs and all
  intermediate values computed inside the circuit.

The **computational semantics** defines a function that a prover uses
to execute the circuit and compute a valid witness $w$ for a given set
of inputs. The **relational semantics** defines
the relation $R$ itself, which both the prover and verifier use as the
shared definition of a valid computation.

Crucially, the relational semantics must be **faithful** to the
computational semantics. This means the relation $R(s, w)$ only holds
true if the witness $w$ is precisely what the computational semantics
would produce for the statement $s$. This property guarantees that a
prover can only generate proofs for valid executions.

*The computational and relational semantics of ZKIR are defined
formally in the accompanying Agda file. For your convenience, below is
an AI-generated explanation of the two different semantics based on
the formal definition, that might be easier to stomach.*

***

### Preliminaries: Syntax and States

Let's first define the basic components.

* **States (Memory)**: For each syntactic type `μ`, there is a set of
  states (or memories), which we denote as `S_μ`. A state `M ∈ S_μ`
  contains the values of all wires defined up to that point.
* **Programs (Circuits)**: The language consists of programs `Ω`,
  instructions `I`, and merge-functions `Φ`. A program of type `μ →
  μ'` takes an input state in `S_μ` and produces an output state in
  `S_μ'`.
* **Primitive Operations**:
    * **State Combination**: Overloading notation, we use `M₁ ⊗ M₂` to
      denote the combination of two states, corresponding to `_⊗ᴹ_` in
      the code.
    * **Argument Resolution**: For a state `M`, `args(M)` is a
      function that resolves the values of arguments (wires,
      constants, public/private inputs) from the state `M` or
      contextual information on public/private inputs. This
      corresponds to `⟦_⟧arg`.
    * **Condition Resolution**: For a state `M` and a condition `c`,
      `resolve(c, M)` returns `true` or `false`.

### Computational Semantics (The "How") 

The computational semantics defines an evaluation function, `𝒞⟦·⟧`,
which maps a program and an input state to a unique output state. It
tells you exactly what the result of running the program is.

Let `𝒞⟦P⟧ : S_μ → S_μ'` be the evaluation function for a program `P`
of type `μ → μ'`. It's defined recursively on the structure of the
program:

* **Sequence**: For a program composed of an instruction `I` followed
  by a program `Ω`:

    ```
    𝒞⟦seq(I, Ω)⟧(M) = M' ⊗ 𝒞⟦Ω⟧(M ⊗ M')
        where M' = 𝒞⟦I⟧(M)
    ```

    This means we first execute instruction `I` on the input state `M`
    to get an intermediate state `M'`. Then, we execute the rest of
    the program `Ω` with access to both the original state and the new
    intermediate state.

* **Gate**: For a gate instruction that applies a primitive function
  `f_g` (e.g., addition, XOR):

    ```
    𝒞⟦gate(g, ..., ι_*)⟧(M) = lift-mem(f_g(args(M, ι_*)))
    ```

    This means we resolve the arguments `ι_*` in the current state
    `M`, apply the gate's function `f_g` to them, and lift the
    resulting values back into a state representation.

* **Branch**: For a conditional branch on variable `x`:
    ```
    𝒞⟦branch(x, Ω₁, Ω₂, φ)⟧(M) = (M₁ ⊕ M₂) ⊗ 𝒞⟦φ⟧(M_choice)
    ```
    where:
    ```
    M₁ = 𝒞⟦Ω₁⟧(M)
    M₂ = 𝒞⟦Ω₂⟧(M)
    M_choice = if resolve(x, M) = true then inj₁(M₁) else inj₂(M₂)
	```
	This first executes *both* branches to get potential resulting
    states `M₁` and `M₂`. Then, based on the condition, it selects the
    correct result and uses the merge-function `φ` to combine the
    divergent execution paths.

### Relational Semantics (The "What") 

The relational semantics defines a logical relation, `ℛ⟦·⟧`, which
specifies the valid input/output pairs for a program. It doesn't
compute an output but rather *verifies* if a given output could have
been produced from a given input. We write `ℛ⟦P⟧(M_in, M_out)` to mean
the output state `M_out` is a valid result for program `P` with input
state `M_in`.

* **Sequence**: A sequence is valid if the both the head and tail
  relate their respective in- and output memories.
    ```
    ℛ⟦seq(I, Ω)⟧(M, (M₁ , M₂)) ⇔ ( ℛ⟦I⟧(M, M₁) ∧ ℛ⟦Ω⟧(M ⊗ M₁, M₂) )
    ```

* **Gate**: An input/output pair is valid for a gate if the gate's own
  logical relation `R_g` holds for the resolved arguments and the
  flattened output values.
    ```
    ℛ⟦gate(g, ...)⟧(M, M') ⇔ R_g(args(M), flatten(M'))
    ```

* **Branch**: A branch is valid if the condition is true AND the first
  branch's relation holds, OR the condition is false AND the second
  branch's relation holds. The merge function `φ` must also hold.
	```
    ℛ⟦branch(c, Ω₁, Ω₂, φ)⟧(M_in, (M₁ ⊕ M₂) ⊗ M') ⇔
      (resolve(c, M_in) = true  ∧ ℛ⟦Ω₁⟧(M_in, M₁) ∧ ℛ⟦φ⟧(inj₁(M₁), M')) ∨
      (resolve(c, M_in) = false ∧ ℛ⟦Ω₂⟧(M_in, M₂) ∧ ℛ⟦φ⟧(inj₂(M₂), M'))
    ```
	
### Off-Chain Execution 

Before using the computational semantics of circuits to generate,
users "rehearse" the contract using typescript output generated by the
compiler. This records the results of witness calls (as private
inputs) and reads/writes to the ledger (as an impact transcript) in a
*proof preimage*. 

Ignoring some details, we can say that: 

```
ProofPreimage = PublicInputs × PrivateInputs
```

An important caveat here is that the circuit's computational and
relational semantics expext public/private input values for **all**
possible branches in the circuit, not just the once we took during
off-chain execution, while the proof preimage only records values for
the branches that were actually taken. In practice, this means that we
need to "pad" the memory with dummy/default values corresponding to
the public/private inputs of the branches that we didn't take. 

In the semantics defined in this document, this would be a
preprocessing step that converts a proof preimage to public/private
input vectors with the right shape by padding with values in the right
places. 

To ensure this padding is type safe woudl require some changes to the
static semantics. For example, using co-debruin representation for
referencing private/public input variables, or effect grading.

*** 

**For reference, the proof preimage definitions in Midnight-JS and the Ledger**. 

In the off-chain runtime:

```typescript 
export interface ProofData {
  /**
   * The inputs to a circuit
   */
  input: ocrt.AlignedValue;
  /**
   * The outputs from a circuit
   */
  output: ocrt.AlignedValue;
  /**
   * The public transcript of operations
   */
  publicTranscript: ocrt.Op<ocrt.AlignedValue>[];
  /**
   * The transcript of the witness call outputs
   */
  privateTranscriptOutputs: ocrt.AlignedValue[];
}
```

Found here: https://github.com/midnightntwrk/compactc/blob/main/runtime/src/runtime.ts#L658

In the ledger: 

```rust 
pub struct ProofPreimage {
    /// The inputs to be directly handed to the IR.
    pub inputs: Vec<Fr>,
    /// A private witness vector consumed by active witness calls in the IR.
    pub private_transcript: Vec<Fr>,
    /// A public statement vector encoding statement call information in the IR.
    pub public_transcript_inputs: Vec<Fr>,
    /// A public statement vector encoding statement call results in the IR.
    pub public_transcript_outputs: Vec<Fr>,
    ...
	/// + Some crypto stuff 
	... 
}
```

Found here: https://github.com/midnightntwrk/midnight-ledger-prototype/blob/main/transient-crypto/src/proofs.rs#L618


*** 

## Gate Reference 

This is not a complete gate reference, but illustrates how ZKIR
operations map onto operations in the proof system.

For each gate, we give a definition of its signature of the form
`<name> : <signature>`. 

Crucially, the semantics of a gate **depends on its
implementation**. For polymorphic types, this semantics is type
directed: how we interpret a gate depends on how we instantiate its
polymorphic variables. For instance, a multiplication gate:

```
mul : ∀ T . Arith(T) ⇒ [T,T] ↠ [T] 
```

If we instantiate this with `T = Element(native)`, there should exist
a predicate witness `Arith(Element(native)`, which would correspond to
the trait implementation in `field/native/native_chip.rs` l880.

The relational semantics of this gate is a ternary relation over
native field elements, which is satisfiable if the first to indices
multiply to the third. The corresponding trait implementation
"implements" this relational semantics by extending the system of
polynomial equations with additional constraints that are only
satisfiable iff the in- and output variables of the operation are
related by field multiplication.

The computational semantics of this gate *computes* field
multiplication.


### Arith

_this reifies the `ArithInstructions` trait defined in
`instructions/arithmetic.rs`_

**Operations** 

* `linear_combination : ∀ T . Arith(T) ⇒ [ (const:T , wire:T)∗ , const:T ] ↠ [T]`
* `add : ∀ T . Arith(T) ⇒ [ wire:T , wire:T ] ↠ [T]`
* `sub : ∀ T . Arith(T) ⇒ [ wire:T , wire:T ] ↠ [T]`
* `mul : ∀ T . Arith(T) ⇒ [ wire:T , wire:T , (const:T)? ] ↠ [T]` 
* `div : ∀ T . Arith(T) ⇒ [ wire:T , wire:T ] ↠ [T]`
* `neg : ∀ T . Arith(T) ⇒ [ wire:T ] ↠ [T]` 
* `inv : ∀ T . Arith(T) ⇒ [ wire:T ] ↠ [T]` 
* `inv0 : ∀ T . Arith(T) ⇒ [ wire:T ] ↠ [T]` 
* `add_constant : ∀ T . Arith(T) ⇒ [ (wire:T)* , (const:T)* ] ↠ [ T* ]`
  (techically we don't support slices in output wires yet, but that's
  easy to add).
* `mul_by_constant : ∀ T . Arith(T) ⇒ [ wire:T , const:T ] ↠ [ T ]`
* `square : ∀ T . Arith(T)  ⇒ [ wire:T ] ↠ [ T ]` 
* `pow : ∀ T . Arith(T) ⇒ [ wire:T , const:BigUint ] ↠ [T]`
* `add_and_mul : ∀ T . Arith(T) ⇒ [ (const:T,wire:T) , (cons:T,wire:T) , (const:T,wire:T) , const:T , const:T ] ↠ [ T ]`

**Instances** 

The proof system supplies instances of the `Arith` interface for
native and emulated field elements: This means we would have the
following predicate witnesses corresponding to trait implementations
in the proof system:

* `Arith(Element(native))`
* `Arith(Element(bls12-381.scalar))` (= native) 
* `Arith(Element(bls12-381.base))` 
* `Arith(Element(secp256k1.base))`
* `Arith(Element(jubjub.base))` (= bls12-381.scalar = native)
* ... and more? ... 

**Semantics** 

The relational semantics of the above operations is dependent on the
instantiation, and is defined by the constraints that are added by the
corresponding operation of the instantiation. The computational
semantics should compute a result as described by the added
constraints.

## Documentation 

ZKIR may in the future become a user-facing component that users may
leverage to construct transactions while circumventing compact and/or
midnight JS.

In this case, we should properly document the following (TODO: check): 

Down the line this means we should produce proper user-facing
documentation of the following elements:

* Syntax
* Well-formedness (i.e., typing rules) 
* Intended semantics
  - computational behavior: ZKIR programs encode a function, the
    computational semantics describes how this function computes.
  - relational semantics: ZKIR programs define an NP-relation which
    for which we generate a zero-knowledge proof when submitting a
    call transaction
  - The relational semantics should be faithful to the computational
    semantics.
* Which components use ZKIR and how they depend on it: 
  * Proof server
  * Ledger
  * Compiler 
* Representation formats. 
  * Binary
  * JSON   

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

(TODO: what meta-data ) 
