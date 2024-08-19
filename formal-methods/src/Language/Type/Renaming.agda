open import Language.Type.Base
open import Language.Type.Kind 

open import Relation.Unary using (IUniversal; _⇒_) 

open import Data.List
open import Data.List.Membership.Propositional

open import Function

module Language.Type.Renaming where

Renamingᵀ : (Δ₁ Δ₂ : TypeContext) → Set
Renamingᵀ Δ₁ Δ₂ = ∀[ (_∈ Δ₁) ⇒ (_∈ Δ₂) ]

mutual 
  renameᴸ : Renamingᵀ Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₁ ⟩⊢ld → ⟨ Ξ ∣ Δ₂ ⟩⊢ld 
  renameᴸ ρ (Cell T)                  = Cell (renameᵀ ρ T)
  renameᴸ ρ (SetT T)                  = SetT (renameᴸ ρ T)
  renameᴸ ρ (Map Tᴷ Tⱽ)               = Map (renameᵀ ρ Tᴷ) (renameᴸ ρ Tⱽ)
  renameᴸ ρ (ListT T)                 = ListT (renameᴸ ρ T)
  renameᴸ ρ (MerkleTree #n T)         = MerkleTree (renameᵀ ρ #n) (renameᴸ ρ T)
  renameᴸ ρ (HistoricMerkleTree #n T) = HistoricMerkleTree (renameᵀ ρ #n) (renameᴸ ρ T)
  renameᴸ ρ Counter                   = Counter

  renameᵀ : Renamingᵀ Δ₁ Δ₂ → ⟨ Ξ ∣ Δ₁ ⟩⊢ty k → ⟨ Ξ ∣ Δ₂ ⟩⊢ty k 
  renameᵀ ρ (· L)            = · renameᴸ ρ L
  renameᵀ ρ (# n)            = # n
  renameᵀ ρ Boolean          = Boolean
  renameᵀ ρ UInteger[<= T ]  = UInteger[<= renameᵀ ρ T ]
  renameᵀ ρ UInteger[ T ]    = UInteger[ renameᵀ ρ T ]
  renameᵀ ρ Field            = Field
  renameᵀ ρ Void             = Void 
  renameᵀ ρ Bytes[ T ]       = Bytes[ renameᵀ ρ T ]
  renameᵀ ρ Vector[ #n , T ] = Vector[ renameᵀ ρ #n , renameᵀ ρ T ]
  renameᵀ ρ Opaque[ s ]      = Opaque[ s ]
  renameᵀ ρ (Enum α)         = Enum α
  renameᵀ ρ (Struct α targs) = Struct α (renameᵀ ρ ∘ targs)
  renameᵀ ρ (Var α)          = Var (ρ α)
