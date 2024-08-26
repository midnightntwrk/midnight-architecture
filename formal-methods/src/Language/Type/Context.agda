open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.List.Membership.Propositional

open import Language.Type.Base 
open import Language.Type.Kind 

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (IUniversal ; _⇒_)

open import Function 

module Language.Type.Context where

-- Signatures of callable identifiers in the context 
record Callable (Ξ : DeclContext) (Δ : TypeContext) : Set where
  constructor callable 
  field
    Δᶜ      : List Kind 
    T∗      : List (⟨ Ξ ∣ Δᶜ ++ Δ ⟩⊢ty ★)
    Tᴿ      : ⟨ Ξ ∣ Δᶜ ++ Δ ⟩⊢ty ★ 

open Callable public

variable κ κ₁ κ₂ κ₃ κ′ : Callable Ξ Δ
         𝓌 𝓌₁ 𝓌₂ 𝓌₃ 𝓌′ : Callable Ξ Δ 

Variables : DeclContext → TypeContext → Set
Variables Ξ Δ = List ( ⟨ Ξ ∣ Δ ⟩⊢ty ★ )

Circuits : DeclContext → TypeContext → Set
Circuits Ξ Δ = List (Callable Ξ Δ)

Witnesses : DeclContext → TypeContext → Set
Witnesses Ξ Δ = List (Callable Ξ Δ)

record LedgerState (Ξ : DeclContext) (Δ : TypeContext) : Set where
  field
    members    : List ⟨ Ξ ∣ Δ ⟩⊢ld
    kernel     : ∀ {Ξ′} {Δ′} → List (Callable Ξ′ Δ′)
    operations : ∀ {Ξ′} {Δ′} → ⟨ Ξ′ ∣ Δ′ ⟩⊢ld → List (Callable Ξ′ Δ′) 

open LedgerState public 

-- Example: defines the "read" operation for cells. 
cread : ⟨ Ξ′ ∣ Δ′ ⟩⊢ld → List (Callable Ξ′ Δ′)
cread (Cell T) = [ callable _ [] T ]
cread _        = [] 

Usertype : Decl → DeclContext → TypeContext → Set
Usertype enum Ξ Δ = ℕ
Usertype (struct Δ′) Ξ Δ = Variables Ξ (Δ′ ++ Δ)

Usertypes : DeclContext → TypeContext → Set
Usertypes []           Δ = ⊤
Usertypes (d ∷ Ξ)      Δ = Usertype d Ξ Δ × Usertypes Ξ Δ

_∈′_or_ : Callable Ξ Δ → (_ _ : List (Callable Ξ Δ)) → Set
κ ∈′ x or y = κ ∈ x ⊎ κ ∈ y

record Context (Ξ : DeclContext) (Δ : TypeContext) : Set where
  constructor _∣_∣_∣_ 
  field
    𝒰 : Usertypes Ξ Δ
    𝒲 : Witnesses Ξ Δ
    Ω : Circuits Ξ Δ
    Λ : LedgerState Ξ Δ
    
open Context public 

variable Γ₁ Γ₂ Γ₃ Γ′ : Variables Ξ Δ 
         𝒰₁ 𝒰₂ 𝒰₃ 𝒰′ : Usertypes Ξ Δ 
         𝒲₁ 𝒲₂ 𝒲₃ 𝒲′ : Witnesses Ξ Δ 
         Ω₁ Ω₂ Ω₃ Ω′ : Circuits Ξ Δ
         Λ₁ Λ₂ Λ₃ Λ′ : LedgerState Ξ Δ 

