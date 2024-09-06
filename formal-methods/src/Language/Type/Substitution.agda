{-# OPTIONS --safe #-} 

open import Language.Type.Base
open import Language.Type.Renaming 
open import Language.Type.Kind 

open import Data.Empty
open import Data.Sum hiding (map ) renaming ([_,_] to ⊎[_,_])
open import Data.Product 
open import Data.List
open import Data.List.Membership.Propositional 
open import Data.List.Membership.Propositional.Properties 
open import Data.List.Relation.Unary.Any hiding (map)

open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_) 
open import Relation.Binary.PropositionalEquality

open import Function

module Language.Type.Substitution where

-- The types that support substitution are the -∈- relative monads, where
-- substitutions and the substitution operation correspond to (relative) Kleisli
-- morphisms and Kleisli extension respectively. 
record Substitute {a} {A : Set a} (M : List A → (A → Set)) : Set a where

  field
    substitute : ∀ {xs ys} → ∀[ (_∈ xs) ⇒ M ys ] → ∀[ M xs ⇒ M ys ]

  Substitution : (xs ys : List A) → Set _ 
  Substitution xs ys = ∀[ (_∈ xs) ⇒ M ys ]

open Substitute ⦃...⦄ public 

mutual 

  instance subst-ty : Substitute (λ Δ k → ⟨ Ξ ∣ Δ ⟩⊢ty k)
  subst-ty .substitute σ (· L)            = · subst-ld σ L
  subst-ty .substitute σ (# n)            = # n
  subst-ty .substitute σ Boolean          = Boolean
  subst-ty .substitute σ UInteger[<= T ]  = UInteger[<= substitute σ T ]
  subst-ty .substitute σ UInteger[ T ]    = UInteger[ substitute σ T ]
  subst-ty .substitute σ Field            = Field
  subst-ty .substitute σ Void             = Void
  subst-ty .substitute σ Bytes[ T ]       = Bytes[ substitute σ T ]
  subst-ty .substitute σ Vector[ #n , T ] = Vector[ substitute σ #n , substitute σ T ]
  subst-ty .substitute σ Opaque[ s ]      = Opaque[ s ]
  subst-ty .substitute σ (Enum d)         = Enum d
  subst-ty .substitute σ (Struct d T∗)    = Struct d (substitute σ ∘ T∗)
  subst-ty .substitute σ (Var α)          = σ α

  subst-ld : Substitution Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₁ ⟩⊢ld → ⟨ Ξ ∣ Δ₂ ⟩⊢ld 
  subst-ld σ Counter           = Counter
  subst-ld σ (Cell T)          = Cell (substitute σ T)
  subst-ld σ (SetT T)          = SetT (substitute σ T)
  subst-ld σ (Map Tᴷ (inj₁ L)) = Map (substitute σ Tᴷ) (inj₁ (subst-ld σ L))
  subst-ld σ (Map Tᴷ (inj₂ T)) = Map (substitute σ Tᴷ) (inj₂ (substitute σ T))
  subst-ld σ (ListT T)         = ListT (substitute σ T)
  subst-ld σ (MerkleTree #n T) = MerkleTree (substitute σ #n) (substitute σ T)
  subst-ld σ (HistoricMerkleTree #n T)
    = HistoricMerkleTree (substitute σ #n) (substitute σ T)


-- Composes substitutions
compose-subst : Substitution Δ₂ Δ₃ → Substitution ⦃ subst-ty {Ξ} ⦄ Δ₁ Δ₂ → Substitution Δ₁ Δ₃
compose-subst σ₁ σ₂ = substitute σ₁ ∘ σ₂

⌞_⌟  : Substitution ⦃ subst-ty {Ξ} ⦄ Δ₁ Δ₂ → Substitution (Δ₁ ++ Δ₂) Δ₂
⌞ σ ⌟ = ⊎[ σ , Var ] ∘ ∈-++⁻ _
