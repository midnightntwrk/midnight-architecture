{-# OPTIONS --safe #-} 

open import Data.Nat 
open import Data.Product 

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Language.Type.Kind where

data Kind : Set where
  ♯ ★ : Kind

variable k₁ k₂ k₃ k k′ : Kind 

record Size′ : Set₁ where
  field
    size : ℕ 

open Size′ public 

-- Sets with dedicable equality and default values
--
-- Orestis: name is misleading
record Set+ : Set₁ where
  field
    carrier   : Set
    decidable : DecidableEquality carrier
    default   : carrier

open Set+ public 

⟦_⟧ᴷ : Kind → Set₁
⟦ ♯ ⟧ᴷ = Size′
⟦ ★ ⟧ᴷ = Set+
