open import Runtime.Type

open import Data.List
open import Data.List.Relation.Unary.All

module Runtime.Stack where

StackTy = List Type

variable Ψ Ψ₁ Ψ₂ Ψ₃ Ψ′ : StackTy
         Φ Φ₁ Φ₂ Φ₃ Φ′ : StackTy 

data Stack : StackTy → Set where
  ε   : Stack []
  _,_ : Value τ → Stack Ψ → Stack (τ ∷ Ψ)

-- Constraints over stack types 
infix 9 _∈∗_ 
_∈∗_ : (Ψ : StackTy) → TypeConstraint → Set
Ψ ∈∗ C = All (_∈ C) Ψ

pop : Stack (τ ∷ Ψ) → Stack Ψ
pop (v , σ) = σ

top : Stack (τ ∷ Ψ) → Value τ
top (v , σ) = v
