open import Data.Integer
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Unit

open import Relation.Binary.PropositionalEquality

module Runtime.Type where

-- Could change this to model overflows 
int64 = ℤ 

mutual 
  -- "Aligned values" that can be cast from and to 64 bit integers (represented
  -- here as natural numbers)
  data Typeᴬ : Set where 
    bool int digest : Typeᴬ  
    type : Type → Typeᴬ

  data Type : Set where
    null : Type
    cell : Typeᴬ → Type  
  
    dict   : Typeᴬ → Type → Type
    array  : Type → Type
    bmtree : Type → Type

⋆ = cell

infixr 10 _∣_ 
data TypeConstraint : Set where
  dict array bmtree cell null : TypeConstraint
  _∣_ : (C₁ C₂ : TypeConstraint) → TypeConstraint 

infix 9 _∈_
_∈_ : (τ : Type) → TypeConstraint → Set
τ ∈ dict   = ∃₂ λ t τ′ → τ ≡ dict t τ′
τ ∈ array  = ∃ λ τ′ → τ ≡ array τ′
τ ∈ bmtree = ∃ λ τ′ → τ ≡ bmtree τ′
τ ∈ cell   = ∃ λ t → τ ≡ cell t
τ ∈ null   = τ ≡ null
τ ∈ C₁ ∣ C₂ = τ ∈ C₁ ⊎ τ ∈ C₂

⟦_⟧ᴬ : Typeᴬ → Set
⟦ bool     ⟧ᴬ = Bool
⟦ type τ   ⟧ᴬ = ⊤ 
⟦ int      ⟧ᴬ = ℤ
⟦ digest   ⟧ᴬ = ℤ

⟦_⟧ᵀ : Type → Set
⟦ null       ⟧ᵀ = ⊤
⟦ cell t     ⟧ᵀ = ⟦ t ⟧ᴬ
⟦ dict x t   ⟧ᵀ = ⊤ -- TODO
⟦ array t    ⟧ᵀ = ⊤ -- TODO
⟦ bmtree t   ⟧ᵀ = ⊤ -- TODO

variable t u t₁ t₂ t₃ u₁ u₂ u₃ t′ u′ : Typeᴬ
         τ τ₁ τ₂ τ₃ τ′ : Type 

-- Defines the type of keys in the union of arrays and dictionaries
_~key_ : ∀ τ → τ ∈ array ∣ dict → Type
.(array τ)    ~key inj₁ (τ       , refl) = ⋆ int
.(dict τ₁ τ₂) ~key inj₂ (τ₁ , τ₂ , refl) = ⋆ τ₁

-- Defines the type of values in the union of arrays and dictionaries 
_~val_ : ∀ τ → τ ∈ array ∣ dict → Type 
.(array τ)    ~val (inj₁ (τ       , refl)) = τ
.(dict τ₁ τ₂) ~val (inj₂ (τ₁ , τ₂ , refl)) = τ₂


record Value (t : Type) : Set where
  constructor extend
  field reflect : ⟦ t ⟧ᵀ 

open Value


postulate
  toℤ   : ⟦ t ⟧ᴬ → ℤ
  get : (px : τ ∈ array ∣ dict) → ⟦ τ ⟧ᵀ → ⟦ τ ~key px ⟧ᵀ → ⟦ τ ~val px ⟧ᵀ
