
<!--
```agda
{-# OPTIONS --overlapping-instances --safe #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution
open import Language.Type.Context 

open import Language.Syntax.Expression 

open import Util.Logic
open import Util.Ternary

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_ ; _+_ ; _*_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All hiding (map) renaming (lookup to resolve)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.Fin using (Fin)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_ ; Satisfiable)

module Language.Syntax.Statement where
```
--> 

<!--
```agda
infix 4 ⟨_∣_⟩⊢stmt_⊣_
mutual
```
--> 

<!--
```agda 
  data ⟨_∣_⟩⊢stmt∗_⊣_ (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) : (Γ′ : Variables Ξ Δ) → Set where
```
-->

# Statements

This file defines well-formedness of statements in Compact. 


## Reflexive Transitive Closure / Sequences of Statements 

A judgment of the form `⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ′` defines a well-formed sequence
of statements with respect to a context `𝓒`, free variables `Γ`, return type
`T`, and updated variable context `Γ′`. Here, `T` is (an upper bound of) the
type of expressions returned by any `return` statements in the seqence. It
should be the case that `Γ′ >= Γ`, where `Γ′` contains any new binders declared
in the sequence.


The first way to construct a sequence of statements is the empty sequence. An
empty sequence of statements is well-formed w.r.t. any return type, and its
_output context_ is just `Γ` without any added new binders.

```agda 
    [s∗-empty]  : ---------------------
                  ⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ
```

Alternatively, we can prepend a statement `S` to a sequence of statements `S∗`,
in which case the _output context_ `Γ₁` of the statement `S` should match the
_input context_ of the sequence `S∗`. Any `return` statements in both the head
and the tail of the sequence are required to return the same type `T`.

```agda 
    [s∗-step]   : ( S   : ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ₁ )
                → ( S∗  : ⟨ 𝓒 ∣ Γ₁ ⟩⊢stmt∗ T ⊣ Γ₂ )
                  --------------------------------
                → ⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ₂ 
```

## Statements 

<!--

```agda 
  data ⟨_∣_⟩⊢stmt_⊣_ (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) : (Γ′ : Variables Ξ Δ) → Set where

    `block   : (S∗ : ⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ′)
               -----------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ  

    `for     : ( n : ℕ)
             → ( S  : ⟨ 𝓒 ∣ UInteger[<= # n ] ∷ Γ ⟩⊢stmt T ⊣ Γ′ )
               -------------------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ

    `foreach : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ #n , T′ ] )
             → ( S  : ⟨ 𝓒 ∣ T′ ∷ Γ ⟩⊢stmt T ⊣ Γ′ )
               -----------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ 

    `return  : ( E : ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr T )
               --------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ

    `returnv : T ≡ Void
               --------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ 

    `if      : ( E  : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
             → ( S₁ : ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ₁ )
               ------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ

    `ifelse  : ( E  : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
             → ( S₁ : ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ₁ )
             → ( S₂ : ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ₂ )
               -------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ

    `expr    : ( E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T′ )
               -------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ

    `const   : ( E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T′ )
               -------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ T′ ∷ Γ

    `assert  : ( E    : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
             → ( msg : String )
               ---------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ
  
```
--> 
