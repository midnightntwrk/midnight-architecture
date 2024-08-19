open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution 

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All hiding (map) renaming (lookup to resolve)
open import Data.Product hiding (map)
open import Data.Sum 

module Language.Syntax.Expression where

-- Assume we have a way to calculate the length of a string literal, in terms of
-- the number of bytes of its UTF-8 encoding
postulate
  strlen : String → ℕ
  
mutual

  data ⟨_∣_∣_⟩⊢expr_ (𝓦 : Witnesses Ξ Δ) (Ω : Circuits Ξ Δ) (Γ : Context Ξ Δ) : (T : ⟨ Ξ ∣ Δ ⟩⊢ty k) → Set where

    ------------------
    ---  Literals  ---
    ------------------

    `bool :    (x : Bool)
               -------------------
               → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr  Boolean

    `num     : (n : ℕ)
               --------------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr UInteger[<= # n ]

    `str     : (s : String)
               ----------------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr Bytes[ # strlen s ]  

    `pad     : (s : String)
             → (n : ℕ)
             → strlen s ≤ n
               -------------------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr Bytes[ # n ] 


    -------------------
    ---  Variables  ---
    -------------------

    `var     : T ∈ Γ
               --------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr T


    ------------------------
    ---  Default values  ---
    ------------------------

    `default : (T/L : ⟨ Ξ ∣ Δ ⟩⊢ty ★ ⊎ ⟨ Ξ ∣ Δ ⟩⊢ld)
               ------------------------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr T 


    -----------------------------------
    ---  Circuit and witness calls  ---
    -----------------------------------

    -- TODO: this rule look slightly scary, can we identify abstractions to make it a little bit friendlier? 
    `call    : {Δ′    : List Kind}
               {T∗    : List (∃ λ k → ⟨ Ξ ∣ Δ′ ++ Δ ⟩⊢ty k)}
             → (x     : callable Δ′ T∗ T ∈′ 𝓦 or Ω)
             → (targs : All (⟨ Ξ ∣ Δ ⟩⊢ty_) Δ′)
             → (args  : All (λ (k , T₁) → ∃ λ (T₂ : ⟨ Ξ ∣ Δ ⟩⊢ty k) → (⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr T₂) × T₂ ⊑ [ T₁ ∥ resolve targs ]) T∗)
               -----------------------------------------------------------------------------------------------------------------
             → ⟨ 𝓦 ∣ Ω ∣ Γ ⟩⊢expr T

    
