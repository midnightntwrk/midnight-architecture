open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Context

open import Relation.Unary using (IUniversal; _⇒_) 

open import Data.List
open import Data.Unit
open import Data.Product hiding (map)
open import Data.List.Membership.Propositional
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.List.Membership.Propositional.Properties

open import Function

module Language.Type.Renaming where

Renaming : ∀ {a} → {A : Set a} → (Δ₁ Δ₂ : List A) → Set a
Renaming xs ys = ∀[ (_∈ xs) ⇒ (_∈ ys) ]

record Rename {a} {A : Set a} (F : List A → Set) : Set a where
  field
    rename : ∀ {xs ys} → Renaming xs ys → F xs → F ys 

open Rename ⦃...⦄ public

mutual
  instance renameΔ-ld : Rename ⟨ Ξ ∣_⟩⊢ld 
  renameΔ-ld .rename ρ (Cell T)                  = Cell (rename ρ T)
  renameΔ-ld .rename ρ (SetT T)                  = SetT (rename ρ T)
  renameΔ-ld .rename ρ (Map Tᴷ (inj₁ L))         = Map (rename ρ Tᴷ) (inj₁ (rename ρ L))
  renameΔ-ld .rename ρ (Map Tᴷ (inj₂ T))         = Map (rename ρ Tᴷ) (inj₂ (rename ρ T))
  renameΔ-ld .rename ρ (ListT T)                 = ListT (rename ρ T)
  renameΔ-ld .rename ρ (MerkleTree #n T)         = MerkleTree (rename ρ #n) (rename ρ T)
  renameΔ-ld .rename ρ (HistoricMerkleTree #n T) = HistoricMerkleTree (rename ρ #n) (rename ρ T)
  renameΔ-ld .rename ρ Counter                   = Counter

  instance renameΔ-ty : Rename (⟨ Ξ ∣_⟩⊢ty k)
  renameΔ-ty .rename ρ (· L)            = · rename ρ L
  renameΔ-ty .rename ρ (# n)            = # n
  renameΔ-ty .rename ρ Boolean          = Boolean
  renameΔ-ty .rename ρ UInteger[<= T ]  = UInteger[<= rename ρ T ]
  renameΔ-ty .rename ρ UInteger[ T ]    = UInteger[ rename ρ T ]
  renameΔ-ty .rename ρ Field            = Field
  renameΔ-ty .rename ρ Void             = Void 
  renameΔ-ty .rename ρ Bytes[ T ]       = Bytes[ rename ρ T ]
  renameΔ-ty .rename ρ Vector[ #n , T ] = Vector[ rename ρ #n , rename ρ T ]
  renameΔ-ty .rename ρ Opaque[ s ]      = Opaque[ s ]
  renameΔ-ty .rename ρ (Enum α)         = Enum α
  renameΔ-ty .rename ρ (Struct α σ)     = Struct α (rename ρ ∘ σ)
  renameΔ-ty .rename ρ (Var α)          = Var (ρ α)


mutual
  instance renameΞ-ld : Rename ⟨_∣ Δ ⟩⊢ld
  renameΞ-ld .rename ρ Counter                   = Counter
  renameΞ-ld .rename ρ (Cell T)                  = Cell (rename ρ T)
  renameΞ-ld .rename ρ (SetT T)                  = SetT (rename ρ T)
  renameΞ-ld .rename ρ (Map Tᴷ (inj₁ L))         = Map (rename ρ Tᴷ) (inj₁ (rename ρ L))
  renameΞ-ld .rename ρ (Map Tᴷ (inj₂ T))         = Map (rename ρ Tᴷ) (inj₂ (rename ρ T))
  renameΞ-ld .rename ρ (ListT T)                 = ListT (rename ρ T)
  renameΞ-ld .rename ρ (MerkleTree #n T)         = MerkleTree (rename ρ #n) (rename ρ T)
  renameΞ-ld .rename ρ (HistoricMerkleTree #n T) = HistoricMerkleTree (rename ρ #n) (rename ρ T)

  instance renameΞ-ty : Rename (⟨_∣ Δ ⟩⊢ty k)
  renameΞ-ty .rename ρ (· L)            = · rename ρ L
  renameΞ-ty .rename ρ (# n)            = # n
  renameΞ-ty .rename ρ Boolean          = Boolean
  renameΞ-ty .rename ρ UInteger[<= #n ] = UInteger[<= rename ρ #n ]
  renameΞ-ty .rename ρ UInteger[ #n ]   = UInteger[ rename ρ #n ]
  renameΞ-ty .rename ρ Field            = Field
  renameΞ-ty .rename ρ Void             = Void
  renameΞ-ty .rename ρ Bytes[ T ]       = Bytes[ rename ρ T ]
  renameΞ-ty .rename ρ Vector[ #n , T ] = Vector[ rename ρ #n , rename ρ T ]
  renameΞ-ty .rename ρ Opaque[ s ]      = Opaque[ s ]
  renameΞ-ty .rename ρ (Enum α)         = Enum (ρ α)
  renameΞ-ty .rename ρ (Struct α σ)     = Struct (ρ α) (rename ρ ∘ σ)
  renameΞ-ty .rename ρ (Var α)          = Var α


instance renameΔ-callable : Rename (Callable Ξ)
renameΔ-callable .rename ρ κ
  = callable (κ .Δᶜ) (map (rename ρ′) (κ .T∗)) (rename ρ′ (κ  .Tᴿ))
  where ρ′ : Renaming _ _
        ρ′ = (⊎[ ∈-++⁺ˡ , ∈-++⁺ʳ _ ∘ ρ ] ∘ ∈-++⁻ (κ .Δᶜ))

instance renameΞ-callable : Rename (flip Callable Δ)
renameΞ-callable .rename ρ κ
  = callable (κ .Δᶜ) (map (rename ρ) (κ .T∗)) (rename ρ (κ .Tᴿ)) 

instance renameΔ-var : Rename (Variables Ξ)
renameΔ-var .rename ρ = map (rename ρ) 

instance renameΞ-var : Rename (flip Variables Δ)
renameΞ-var .rename ρ = map (rename ρ) 

instance renameΔ-cir : Rename (Circuits Ξ)
renameΔ-cir .rename ρ = map (rename ρ)

instance renameΞ-cir : Rename (flip Circuits Δ)
renameΞ-cir .rename ρ = map (rename ρ)

instance renameΔ-wit : Rename (Witnesses Ξ)
renameΔ-wit .rename ρ = map (rename ρ)

instance renameΞ-wit : Rename (flip Witnesses Δ)
renameΞ-wit .rename ρ = map (rename ρ) 

instance renameΔ-lstate : Rename (LedgerState Ξ)
renameΔ-lstate .rename ρ Λ .members    = map (rename ρ) (Λ .members)
renameΔ-lstate .rename ρ Λ .kernel     = Λ .kernel  
renameΔ-lstate .rename ρ Λ .operations = Λ .operations

instance renameΞ-lstate : Rename (flip LedgerState Δ)
renameΞ-lstate .rename ρ Λ .members    = map (rename ρ) (Λ .members) 
renameΞ-lstate .rename ρ Λ .kernel     = Λ .kernel
renameΞ-lstate .rename ρ Λ .operations = Λ .operations 

instance renameΔ-utypes : Rename (Usertypes Ξ)
renameΔ-utypes {[]}           .rename      ρ tt       = tt
renameΔ-utypes {enum ∷ _}     .rename {xs} ρ (n , 𝒰)  = n , rename ρ 𝒰
renameΔ-utypes {struct _ ∷ _} .rename {xs} ρ (T∗ , 𝒰) =
  map (rename (⊎[ ∈-++⁺ˡ , ∈-++⁺ʳ _ ∘ ρ ] ∘ ∈-++⁻ _)) T∗ , rename ρ 𝒰

instance renameΔ-ctx : Rename (Context Ξ)
renameΔ-ctx .rename ρ 𝓒 .𝒰 = rename ρ (𝓒 .𝒰) 
renameΔ-ctx .rename ρ 𝓒 .𝒲 = rename ρ (𝓒 .𝒲)
renameΔ-ctx .rename ρ 𝓒 .Ω = rename ρ (𝓒 .Ω)
renameΔ-ctx .rename ρ 𝓒 .Λ = rename ρ (𝓒 .Λ) 
