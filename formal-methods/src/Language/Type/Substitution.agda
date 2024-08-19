open import Language.Type.Base
open import Language.Type.Renaming 
open import Language.Type.Kind 

open import Data.Empty
open import Data.Sum hiding (map)
open import Data.List
open import Data.List.Membership.Propositional 
open import Data.List.Membership.Propositional.Properties 
open import Data.List.Relation.Unary.Any hiding (map)


open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_) 
open import Relation.Binary.PropositionalEquality

open import Function

module Language.Type.Substitution where

Substitutionᵀ : (Ξ : DeclContext) (Δ₁ Δ₂ : TypeContext) → Set
Substitutionᵀ Ξ Δ₁ Δ₂ = ∀[ (_∈ Δ₁) ⇒ ⟨ Ξ ∣ Δ₂ ⟩⊢ty_ ]
 
mutual
  substituteᴸ : Substitutionᵀ Ξ Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₁ ⟩⊢ld → ⟨ Ξ ∣ Δ₂ ⟩⊢ld
  
  substituteᴸ σ Counter                   = Counter
  substituteᴸ σ (Cell T)                  = Cell (substituteᵀ σ T)
  substituteᴸ σ (SetT T)                  = SetT (substituteᴸ σ T)
  substituteᴸ σ (Map Tᴷ Tⱽ)               = Map (substituteᵀ σ Tᴷ) (substituteᴸ σ Tⱽ)
  substituteᴸ σ (ListT T)                 = ListT (substituteᴸ σ T)
  substituteᴸ σ (MerkleTree #n T)         = MerkleTree (substituteᵀ σ #n) (substituteᴸ σ T)
  substituteᴸ σ (HistoricMerkleTree #n T) =
    HistoricMerkleTree (substituteᵀ σ #n) (substituteᴸ σ T)

  substituteᵀ : Substitutionᵀ Ξ Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₁ ⟩⊢ty k → ⟨ Ξ ∣ Δ₂ ⟩⊢ty k
  substituteᵀ σ (· L)                     = · substituteᴸ σ L 
  substituteᵀ σ (# n)                     = # n
  substituteᵀ σ Boolean                   = Boolean
  substituteᵀ σ UInteger[<= T ]           = UInteger[<= substituteᵀ σ T ]
  substituteᵀ σ UInteger[ T ]             = UInteger[ substituteᵀ σ T ]
  substituteᵀ σ Field                     = Field
  substituteᵀ σ Void                      = Void
  substituteᵀ σ Bytes[ T ]                = Bytes[ substituteᵀ σ T ]
  substituteᵀ σ Vector[ #n , T ]          = Vector[ substituteᵀ σ #n , substituteᵀ σ T ]
  substituteᵀ σ Opaque[ s ]               = Opaque[ s ]
  substituteᵀ σ (Enum d)                  = Enum d
  substituteᵀ σ (Struct d targs)          = Struct d (substituteᵀ σ ∘ targs)
  substituteᵀ σ (Var α) = σ α


-- Composes substit
compose-subst : Substitutionᵀ Ξ Δ₂ Δ₃ → Substitutionᵀ Ξ Δ₁ Δ₂ → Substitutionᵀ Ξ Δ₁ Δ₃
compose-subst σ₁ σ₂ = substituteᵀ σ₁ ∘ σ₂


-- prefix substitution
[_∥_] : ⟨ Ξ ∣ Δ₁ ++ Δ₂ ⟩⊢ty k → Substitutionᵀ Ξ Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₂ ⟩⊢ty k
[ T ∥ σ ] = substituteᵀ ([ σ , Var ] ∘ ∈-++⁻ _) T
