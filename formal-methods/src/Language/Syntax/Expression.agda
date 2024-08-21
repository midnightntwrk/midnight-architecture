{-# OPTIONS --overlapping-instances #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution

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

module Language.Syntax.Expression where

-- Assume we have a way to calculate the length of a string literal, in terms of
-- the number of bytes of its UTF-8 encoding
postulate
  strlen : String → ℕ

Elem : List (⟨ Ξ ∣ Δ ⟩⊢ty ★)  → ⟨ Ξ ∣ Δ ⟩⊢ty ★ → Set 
Elem T∗ T = T ∈ T∗

data Cmp : Set where
  le ge leq geq : Cmp 

mutual 

  Substitutionᴱ : (σ : Substitutionᵀ Ξ Δ₁ Δ₂) → (𝓒 : Context Ξ Δ₂) → (Γ₁ : Variables Ξ Δ₁) (Γ₂ : Variables Ξ Δ₂) → Set
  Substitutionᴱ σ 𝓒 Γ₁ Γ₂ = ∀[ Elem Γ₁ ⇒ substituteᵀ σ ⊢ ◇ ⟨ 𝓒 ∣ Γ₂ ⟩⊢expr ]

  infix 4 ⟨_∣_⟩⊢expr
  data ⟨_∣_⟩⊢expr (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) : (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → Set where

    ------------------
    ---  Literals  ---
    ------------------

    `bool    : ( x : Bool )
               -----------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean

    `num     : ( n : ℕ )
               ---------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr UInteger[<= # n ]

    `str     : ( s : String )
               -----------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Bytes[ # strlen s ]  

    `pad     : ( s : String )
             → ( n : ℕ )
             → strlen s ≤ n
               ----------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Bytes[ # n ] 


    -------------------
    ---  Variables  ---
    -------------------

    `var     : T ∈ Γ
               -----------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr T


    ------------------------
    ---  Default values  ---
    ------------------------

    `default : ( T/L : ⟨ Ξ ∣ Δ ⟩⊢ty ★ ⊎ ⟨ Ξ ∣ Δ ⟩⊢ld )
               --------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr T 


    -----------------------------------
    ---  Circuit and witness calls  ---
    -----------------------------------
    
    `call    : ( fun  : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
             → ( σ    : Substitutionᵀ Ξ (κ .Δᶜ) Δ )
             → ( args : Substitutionᴱ ⌞ σ ⌟ 𝓒 (κ .T∗) Γ)
               ------------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ (κ .Tᴿ))


    ---------------------------------
    ---  Structrure construction  ---
    ---------------------------------
    
    `new     : ( d    : struct Δ′ ∈ Ξ )
             → ( σ    : Substitutionᵀ Ξ Δ′ Δ )
             → ( args : Substitutionᴱ ⌞ σ ⌟ 𝓒 (resolve (𝓒 .𝒰) d) Γ)
               -----------------------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr (Struct d σ)


    -----------------------------
    ---  Vector construction  ---
    -----------------------------

    -- NOTE: currently it's only required that T is an upper bound of the types
    -- of the elements in the Vector, not necessarily the least upper bound
    `vec     : ( n : ℕ )
             → ( Fin n → ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr T )
               --------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ # n , T ] 


    --------------------
    ---  Sequencing  ---
    --------------------
    
    `seq     : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
             → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
               ---------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ 


    ----------------------------
    ---  Ledger expressions  ---
    ----------------------------
  
    `kernel   : ( op   : κ ∈ 𝓒 .Λ .kernel )
              → ( σ    : Substitutionᵀ Ξ (κ .Δᶜ) Δ )
              → ( args : Substitutionᴱ ⌞ σ ⌟ 𝓒 (κ .T∗) Γ )
                ------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ (κ .Tᴿ))

    `lmemb    : ( mem  : L ∈ 𝓒 .Λ .members )
                ----------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (· L)

    `lcall    : ( E    : ⟨ 𝓒 ∣ Γ ⟩⊢expr (· L) )
              → ( op   : κ ∈ 𝓒 .Λ .operations L ) 
              → ( σ    : Substitutionᵀ Ξ (κ .Δᶜ) Δ )
              → ( args : Substitutionᴱ ⌞ σ ⌟ 𝓒 (κ .T∗) Γ )
                ------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ (κ .Tᴿ))


    -------------------------------
    ---  Member/element access  ---
    -------------------------------

    `vecelem  : ( E : ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ # n , T ] )
              → ( n : Fin n )
                -----------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T 

    `field    : ( d     : struct Δ′ ∈ Ξ )
              → ( σ     : Substitutionᵀ Ξ Δ′ Δ)
              → ( E     : ⟨ 𝓒 ∣ Γ ⟩⊢expr (Struct d σ) )
              → ( mem   : T ∈ (resolve (𝓒 .𝒰) d) )
                ---------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ T)


    ---------------------------------------
    ---  Arithmetic/Boolean operations  ---
    ---------------------------------------
    
    `neg      : ( E : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
                -------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean

    `add      : ( E₁   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
              → ( E₂   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
              → ⦃ _ : Numeric T₁ ⦄
              → ⦃ _ : Numeric T₂ ⦄
                --------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (T₁ ⋈⟨ _+_ ⟩ T₂)

    `sub      : ( E₁   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
              → ( E₂   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
              → ⦃ _ : Numeric T₁ ⦄
              → ⦃ _ : Numeric T₂ ⦄
                ----------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (T₁ ⋈⟨ const ⟩ T₂)

    `mul      : ( E₁   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
              → ( E₂   : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
              → ⦃ _ : Numeric T₁ ⦄
              → ⦃ _ : Numeric T₂ ⦄
                --------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (T₁ ⋈⟨ _*_ ⟩ T₂)

    `equals   : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
              → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
              → (T₁ ≲ T₂) ⊎ (T₂ ≲ T₁)
                --------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean

    `nequals  : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
              → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
              → (T₁ ≲ T₂) ⊎ (T₂ ≲ T₁)
                ---------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean 

    -- NOTE: can operands also be typed by uint w/ fixed precision? 
    `compare  : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr UInteger[<= #n ] )
              → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr UInteger[<= #m ] )
              → ( op : Cmp)
                -----------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean

    `or       : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
              → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T )
              → Boolean ≲ T
                ------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T

    `and      : ( E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
              → ( E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T )
              → Boolean ≲ T
                -------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T 

    `ite      : ( E   : ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean )
                ( E₁  : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
                ( E₂  : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
                ( sub : T₁ ≲ T₂ ⊎ T₂ ≲ T₁ )
                --------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (⊎[ const T₂ , const T₁ ] sub) 


    -------------------------
    ---  Map expressions  ---
    -------------------------

    `map      : ( fun   : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
              → ( σ     : Substitutionᵀ Ξ (κ .Δᶜ) Δ )  
              → ( args  : Substitutionᴱ ⌞ σ ⌟ 𝓒 (map Vector[ # n ,_] (κ .T∗)) Γ )
                -----------------------------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ # n , substituteᵀ ⌞ σ ⌟ (κ .Tᴿ)  ]

    `fold     : ( fun   : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
              → ( _     : κ .T∗ ≡ κ .Tᴿ ∷ Γ′ )
              → ( σ     : Substitutionᵀ Ξ (κ .Δᶜ) Δ )
              → ( init  : ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ (κ .Tᴿ)) )
              → ( args  : Substitutionᴱ ⌞ σ ⌟ 𝓒 (map Vector[ # n ,_] Γ′) Γ )
                ------------------------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substituteᵀ ⌞ σ ⌟ (κ .Tᴿ)) 


    ---------------
    ---  Casts  ---
    ---------------

    `cast     : (_  : Castable T₁ T₂)
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁
                ---------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂
    
