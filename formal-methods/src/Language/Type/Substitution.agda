open import Language.Type.Base
open import Language.Type.Renaming 
open import Language.Type.Kind 

open import Data.List
open import Data.List.Membership.Propositional 

open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_) 

open import Function

module Language.Type.Substitution where

record Substitutionᵀ (Δ₁ Δ₂ : TypeContext) : Set where  
  field
    apply    : ∀[ tvar ⊢ (_∈ Δ₁) ⇒ (Δ₂ ⊢-ty_) ]  
    ρ-enum   : enum ∈ Δ₁ → enum ∈ Δ₂
    ρ-struct : ∀ {ks} → struct ks ∈ Δ₁ → struct ks ∈ Δ₂ 
   
open Substitutionᵀ

mutual 
  substituteᵀ : Substitutionᵀ Δ₁ Δ₂ → Δ₁ ⊢-ty k → Δ₂ ⊢-ty k
  substituteᵀ σ (# n)                     = # n
  substituteᵀ σ Boolean                   = Boolean
  substituteᵀ σ UInteger[<= T ]           = UInteger[<= substituteᵀ σ T ]
  substituteᵀ σ UInteger[ T ]             = UInteger[ substituteᵀ σ T ]
  substituteᵀ σ Field                     = Field
  substituteᵀ σ Void                      = Void
  substituteᵀ σ Bytes[ T ]                = Bytes[ substituteᵀ σ T ]
  substituteᵀ σ Vector[ #n , T ]          = Vector[ substituteᵀ σ #n , substituteᵀ σ T ]
  substituteᵀ σ Opaque[ s ]               = Opaque[ s ]
  substituteᵀ σ (Enum α)                  = Enum (σ .ρ-enum α)
  substituteᵀ σ (Struct α targs)          = Struct (σ .ρ-struct α) (substituteᵀ σ ∘ targs)
  substituteᵀ σ Counter                   = Counter
  substituteᵀ σ (Cell T px)               = Cell (substituteᵀ σ T) (subst-compactT σ px)
  substituteᵀ σ (SetT T)                  = SetT (substituteᵀ σ T)
  substituteᵀ σ (Map Tᴷ Tⱽ)               = Map (substituteᵀ σ Tᴷ) (substituteᵀ σ Tⱽ)
  substituteᵀ σ (ListT T)                 = ListT (substituteᵀ σ T)
  substituteᵀ σ (MerkleTree #n T)         = MerkleTree (substituteᵀ σ #n) (substituteᵀ σ T)
  substituteᵀ σ (HistoricMerkleTree #n T) =
    HistoricMerkleTree (substituteᵀ σ #n) (substituteᵀ σ T)
  substituteᵀ σ (Var α) = σ .apply α

  subst-compactT : (σ : Substitutionᵀ Δ₁ Δ₂) → CompactType T → CompactType (substituteᵀ σ T)
  subst-compactT σ isBoolean      = isBoolean
  subst-compactT σ isUInteger₁    = isUInteger₁
  subst-compactT σ isUInteger₂    = isUInteger₂
  subst-compactT σ isField        = isField
  subst-compactT σ isVoid         = isVoid
  subst-compactT σ isBytes        = isBytes
  subst-compactT σ isVector       = isVector
  subst-compactT σ isOpaque       = isOpaque
  subst-compactT σ (isEnum _)     = isEnum _
  subst-compactT σ (isStruct _ _) = isStruct _ _
