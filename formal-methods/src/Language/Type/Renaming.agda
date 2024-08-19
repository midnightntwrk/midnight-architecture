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
  renameᵀ : Renamingᵀ Δ₁ Δ₂ → Δ₁ ⊢-ty k → Δ₂ ⊢-ty k 
  renameᵀ ρ (# n)                     = # n
  renameᵀ ρ Boolean                   = Boolean
  renameᵀ ρ UInteger[<= T ]           = UInteger[<= renameᵀ ρ T ]
  renameᵀ ρ UInteger[ T ]             = UInteger[ renameᵀ ρ T ]
  renameᵀ ρ Field                     = Field
  renameᵀ ρ Void                      = Void 
  renameᵀ ρ Bytes[ T ]                = Bytes[ renameᵀ ρ T ]
  renameᵀ ρ Vector[ #n , T ]          = Vector[ renameᵀ ρ #n , renameᵀ ρ T ]
  renameᵀ ρ Opaque[ s ]               = Opaque[ s ]
  renameᵀ ρ (Enum α)                  = Enum (ρ α)
  renameᵀ ρ (Struct α targs)          = Struct (ρ α) (renameᵀ ρ ∘ targs)
  renameᵀ ρ Counter                   = Counter
  renameᵀ ρ (Cell T px)               = Cell (renameᵀ ρ T) (rename-compactT ρ px)
  renameᵀ ρ (SetT T)                  = SetT (renameᵀ ρ T)
  renameᵀ ρ (Map Tᴷ Tⱽ)               = Map (renameᵀ ρ Tᴷ) (renameᵀ ρ Tⱽ)
  renameᵀ ρ (ListT T)                 = ListT (renameᵀ ρ T)
  renameᵀ ρ (MerkleTree #n T)         = MerkleTree (renameᵀ ρ #n) (renameᵀ ρ T)
  renameᵀ ρ (HistoricMerkleTree #n T) = HistoricMerkleTree (renameᵀ ρ #n) (renameᵀ ρ T)
  renameᵀ ρ (Var x)                   = Var (ρ x)

  rename-compactT : (ρ : Renamingᵀ Δ₁ Δ₂) → CompactType T → CompactType (renameᵀ ρ T)
  rename-compactT ρ isBoolean          = isBoolean
  rename-compactT ρ isUInteger₁        = isUInteger₁
  rename-compactT ρ isUInteger₂        = isUInteger₂
  rename-compactT ρ isField            = isField
  rename-compactT ρ isVoid             = isVoid
  rename-compactT ρ isBytes            = isBytes
  rename-compactT ρ isVector           = isVector
  rename-compactT ρ isOpaque           = isOpaque
  rename-compactT ρ (isEnum x)         = isEnum (ρ x)
  rename-compactT ρ (isStruct x targs) = isStruct (ρ x) (renameᵀ ρ ∘ targs)
