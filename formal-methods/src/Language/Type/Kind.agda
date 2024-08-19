open import Data.Nat 

module Language.Type.Kind where

data Kind : Set where
  ♯ ★ : Kind

variable k₁ k₂ k₃ k k′ : Kind 

record Size′ : Set₁ where
  field
    size : ℕ 

⟦_⟧ᴷ : Kind → Set₁
⟦ ♯ ⟧ᴷ = Size′
⟦ ★ ⟧ᴷ = Set
