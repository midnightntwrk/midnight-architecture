{-# OPTIONS --overlapping-instances --safe #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution
open import Language.Type.Context

open import Util.Logic
open import Util.Ternary

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_ ; _+_ ; _*_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All hiding (map) renaming (lookup to resolve)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.Fin using (Fin)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_ ; Satisfiable)

module Language.Syntax.Expression where

-- Assume we have a way to calculate the length of a string literal, in terms of
-- the number of bytes of its UTF-8 encoding
strlen : String → ℕ
strlen _ = 0 

Elem : List (⟨ Ξ ∣ Δ ⟩⊢ty ★) → ⟨ Ξ ∣ Δ ⟩⊢ty ★ → Set 
Elem T∗ T = T ∈ T∗

data Cmp : Set where
  lt gt leq geq : Cmp 

mutual 

  Substitutionᴱ : (σ : Substitution Δ₁ Δ₂) → (F : ⟨ Ξ ∣ Δ₂ ⟩⊢ty ★ → ⟨ Ξ ∣ Δ₂ ⟩⊢ty ★) → (𝓒 : Context Ξ Δ₂) → (Γ₁ : Variables Ξ Δ₁) (Γ₂ : Variables Ξ Δ₂) → Set
  Substitutionᴱ σ F 𝓒 Γ₁ Γ₂ = ∀[ Elem Γ₁ ⇒ substitute σ ⊢ ◇ (F ⊢ ⟨ 𝓒 ∣ Γ₂ ⟩⊢expr) {- ⟨ 𝓒 ∣ Γ₂ ⟩⊢expr -} ]

  infix 4 ⟨_∣_⟩⊢expr
  data ⟨_∣_⟩⊢expr (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) : (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → Set where

    ------------------
    ---  Literals  ---
    ------------------

    `bool    : ( x : Bool )
               ----------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Boolean  

    `num     : ( n : ℕ )
               --------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr UInteger[<= # n ]

    `str     : ( s : String )
               ----------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Bytes[ # strlen s ]  

    `pad     : ( s : String )
             → ( n : ℕ )
             → strlen s ≤ n
               ---------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr Bytes[ # n ] 


    -------------------
    ---  Variables  ---
    -------------------

    `var     : T ∈ Γ
               ----------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr T


    ------------------------
    ---  Default values  ---
    ------------------------

    `default : ( T : ⟨ Ξ ∣ Δ ⟩⊢ty ★ )
               ----------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr T


    -----------------------------------
    ---  Circuit and witness calls  ---
    -----------------------------------
    
    `call    : ( fun  : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
             → ( σ    : Substitution (κ .Δᶜ) Δ )
             → ( args : Substitutionᴱ ⌞ σ ⌟ id 𝓒 (κ .T∗) Γ)
               ------------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ (κ .Tᴿ))


    ---------------------------------
    ---  Structrure construction  ---
    ---------------------------------
    
    `new     : ( d    : struct Δ′ ∈ Ξ )
             → ( σ    : Substitution Δ′ Δ )
             → ( args : Substitutionᴱ ⌞ σ ⌟ id 𝓒 (resolve (𝓒 .𝒰) d) Γ)
               -----------------------------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr (Struct d σ)


    -------------------------
    --- Enum Construction ---
    -------------------------

    `enum    : ( d : enum ∈ Ξ )
             → ( _ : Fin (resolve (𝓒 .𝒰) d))
               ------------------------------
             → ⟨ 𝓒 ∣ Γ ⟩⊢expr (Enum d) 

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
              → ( σ    : Substitution (κ .Δᶜ) Δ )
              → ( args : Substitutionᴱ ⌞ σ ⌟ id 𝓒 (κ .T∗) Γ )
                ------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ (κ .Tᴿ))

    `lmemb    : ( mem  : L ∈ 𝓒 .Λ .members )
                ----------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (· L)

    `lcall    : ( E    : ⟨ 𝓒 ∣ Γ ⟩⊢expr (· L) )
              → ( op   : κ ∈ 𝓒 .Λ .operations L ) 
              → ( σ    : Substitution (κ .Δᶜ) Δ )
              → ( args : Substitutionᴱ ⌞ σ ⌟ id 𝓒 (κ .T∗) Γ )
                ------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ (κ .Tᴿ))


    -------------------------------
    ---  Member/element access  ---
    -------------------------------

    `vecelem  : ( E : ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ # n , T ] )
              → ( n : Fin n )
                -----------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T 

    `field    : ( d     : struct Δ′ ∈ Ξ )
              → ( σ     : Substitution Δ′ Δ)
              → ( E     : ⟨ 𝓒 ∣ Γ ⟩⊢expr (Struct d σ) )
              → ( mem   : T ∈ resolve (𝓒 .𝒰) d )
                ---------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ T)


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
                --------------------------
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
                ( E₁  : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ )
                ( E₂  : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ )
                ( sub : T₁ ≲ T₂ ⊎ T₂ ≲ T₁ )
                --------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (⊎[ const T₂ , const T₁ ] sub) 


    -------------------------
    ---  Map expressions  ---
    -------------------------

    -- NOTE: the typing rules below allow to map/fold over a sequence of _zero_
    -- vectors. Semantically, this is perfectly fine, if we assume a semantics
    -- where map/fold operates on zipped vectors, where a vector of `Void`s
    -- would act as a unit.
    --
    -- (1) For `map`, mapping a 0-argument function over 0 vectors evaluates to
    --     replicating the function's value replicated however many times is
    --     required by the length of the resulting vector.
    --
    -- (2) For `fold`, folding a 1-argument function over some initial value and
    --     0 vectors evaluates to the function applied to the initial value.
    --
    -- This is, of course, a deviation from the typing as described in the
    -- language ref, since there it's required to have at least one vector
    -- argument. 

    `map      : ( fun   : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
              → ( σ     : Substitution (κ .Δᶜ) Δ )  
              → ( args  : Substitutionᴱ ⌞ σ ⌟ Vector[ # n ,_] 𝓒 (κ .T∗) Γ )
                -----------------------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr Vector[ # n , substitute ⌞ σ ⌟ (κ .Tᴿ)  ]

    `fold     : ( fun   : callable Δ′ (T′ ∷ Γ′) T′ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
              → ( σ     : Substitution Δ′ Δ )
              → ( init  : ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ T′) )
              → ( args  : Substitutionᴱ ⌞ σ ⌟ Vector[ # n ,_] 𝓒 Γ′ Γ )
                -------------------------------------------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ T′) 

    ---------------
    ---  Casts  ---
    ---------------

    `cast     : (_  : Castable T₁ T₂)
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁
                ---------------------
              → ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂
