{-# OPTIONS --overlapping-instances #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution

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

infix 4 ⟨_∣_⟩⊢stmt_⊣_

mutual
  -- Reflexive transitive closure (sequence) of statements 
  data ⟨_∣_⟩⊢stmt∗_⊣_ (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) : (Γ′ : Variables Ξ Δ) → Set where
    
    ε        : ⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ

    _·_      : ( S₁ : ⟨ 𝓒 ∣ Γ ⟩⊢stmt T ⊣ Γ₁ )
             → ( S₂ : ⟨ 𝓒 ∣ Γ₁ ⟩⊢stmt∗ T ⊣ Γ₂ )
               --------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢stmt∗ T ⊣ Γ₂ 

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
  
