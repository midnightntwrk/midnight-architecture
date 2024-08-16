open import Language.Type 
open import Language.Subtype

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional

module Language.Syntax.Expression where

-- Assume we have a way to calculate the length of a string literal, in terms of
-- the number of bytes of its UTF-8 encoding
postulate
  strlen : String → ℕ
  

data _⊢ᵉ_ (Γ : Context Δ) : (T : Type Δ) → Set where

  `bool : (x : Bool)
          ------------
        → Γ ⊢ᵉ Boolean

  `num  : (n : ℕ)
          --------------------
        → Γ ⊢ᵉ UInteger[<= n ]

  `str  : (s : String)
          ----------------------
        → Γ ⊢ᵉ Bytes[ strlen s ]  

  `pad  : (s : String)
        → (n : ℕ)
        → strlen s ≤ n
          ---------------
        → Γ ⊢ᵉ Bytes[ n ] 

  `var  : T ∈ Γ
          ------
        → Γ ⊢ᵉ T

  `add  : Γ ⊢ᵉ T₁
        → Γ ⊢ᵉ T₂
        → T ≈max[ T₁ , T₂ ]
          -----------------
        → Γ ⊢ᵉ T

  

  
  
