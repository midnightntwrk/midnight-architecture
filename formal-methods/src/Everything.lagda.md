# Formal Specification of Midnight Smart Contracts 

This module documents ongoing efforts to formalize Midnight's smart
contracts. 

```agda 
module Everything where
```

## Compact Language

The following modules contain a WIP formalization of Compact, based on the
language reference.

### Types

The following modules respectively define the syntax of kinds, well-kinded
types, and subtype witnesses. 

```agda
open import Language.Type.Kind     -- Kind syntax
open import Language.Type.Base     -- Well-kinded types
open import Language.Type.Subtype  -- Subtyping
```

### Substitution and Renaming

The following modules define renaming and substitution for types. These are
necessary when specifying Compact's static semantics, because e.g. the calls to
generic circuits require instantiations of its type paramters, which afterwards
should be substituted in the return type and argument types. 

```agda 
open import Language.Type.Renaming
open import Language.Type.Substitution
```

### Contexts 

The following module defines the contextual information for typing terms in
Compact. Currently, it contains four things:

1. The field `𝒰` contains all declarations of user-defined types, i.e., structs
   and enums,  

2. The field `𝒲` contains all witnesses that are in scope, 

3. The field `Ω` contains the signature of all circuits in scope, and 

4. The field `Λ` contains information about the ledger state, such as
   user-defined fields using the `ledger` keyword, operations available for
   ledger types, and kernel operations. 

```agda
open import Language.Type.Context 
```

### Well-Typedness 

The following modules define well-typedness of compact terms. Something to point
out is the use of modal possibility to express subtyping constraints. That is,
we use the following shallow embedding of modal possibility: 

`◇ P T = ∃ λ T′ → P T′ × T′ ≲ T`

Informally, using the possibility modality weakens a predicate `P` from holding
for some exact `T` to any subtype of `T`. Instantiating `P` with a judgment
gives us `Γ ⊢ T` v.s. `◇ (Γ ⊢_) T`, which respectively stand for "a term with
type `T`" and "a term with a subtype of `T`".

We use this to express well-typedness of constructs where sub-terms may
automatically be casted to a supertype. For example, in the statement `return
E`, the expression `E` may have any type that is a sub-type of the type returned
by the current circuit definition. 

```agda
open import Language.Syntax.Expression
open import Language.Syntax.Statement
open import Language.Syntax.Module
```

### Semantics

```agda
open import Language.Type.Semantics
```

## Impact VM 

The following modules contain a (partial) formalizaiton of the Impact VM, based
on it's
[documentation](https://github.com/input-output-hk/midnight-architecture/tree/main/apis-and-common-types/onchain-runtime). 

```agda 
open import Runtime.Type
open import Runtime.Stack
open import Runtime.Path
open import Runtime.Cost 
open import Runtime.Instruction
open import Runtime.Semantics 
open import Runtime.Sequence
```

## Experiments 

### Mutable references 

The following demonstrates how adding first-class circuits to Compact could
inadvertently make the language Turing comple by encoding general recursion with
Landin's knot (back-patching). Even when disallowing dynamic allocation of
ledger fields.

```agda
open import Experiment.Ref
```

The following file contains a (wip) experiment where we stratify the store,
enforcing a linear structure on the store that disallows store cells containing
closures to contain references that (indirectly) refer to the closure
itself. Terms typed w.r.t. a stratified store are strongly normalizing. 

```agda
open import Experiment.PredicativeRef 
```

### Compiling to circuits

The following file contains a proof-of-concept for how to compile expressions to
(typed) circuits, and contains a proof that circuits encode the intended
semantics. 

```agda 
open import Experiment.Circuit
```
