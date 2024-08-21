open import Data.Nat using (ℕ ; _≤_ ; _^_ ; z≤n)
open import Data.String using (String)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product hiding (map)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe ; maybe ; just)
open import Data.Sum 

open import Data.List using (List; []; _∷_; _++_ ; map)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All ; lookup ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using ()

open import Relation.Nullary.Negation
open import Relation.Unary using (Satisfiable)
open import Relation.Binary using (Reflexive ; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_) 

open import Level renaming (suc to sℓ)
open import Function
open import Function.Bundles

open import Language.Type.Kind 

module Language.Type.Base where

data Decl : Set where
  enum   : Decl
  struct : (Ts : List Kind) → Decl

TypeContext = List Kind 
DeclContext = List Decl

variable Ξ Ξ₁ Ξ₂ Ξ₃ Ξ′ : DeclContext 
         Δ Δ₁ Δ₂ Δ₃ Δ′ : TypeContext 
         n n₁ n₂ n₃ n′ : ℕ
         s s₁ s₂ s₃ s′ : String 

mutual

  data ⟨_∣_⟩⊢ld (Ξ : DeclContext) (Δ : TypeContext) : Set where 

    Counter            : ⟨ Ξ ∣ Δ ⟩⊢ld 

    Cell               : (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                         ---------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 

    SetT               : (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ld)
                         -------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
    
    Map                : (Tᴷ : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                       → (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ld)
                         --------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
                        
    ListT              : (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ld)
                         -------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld
                       
    MerkleTree         : (depth : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                       → (Tⱽ    : ⟨ Ξ ∣ Δ ⟩⊢ld)
                         ------------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
                       
    HistoricMerkleTree : (depth : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                       → (Tⱽ    : ⟨ Ξ ∣ Δ ⟩⊢ld)
                         ------------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld   

  infix 7  #_
  data ⟨_∣_⟩⊢ty_ (Ξ : DeclContext) (Δ : TypeContext) : Kind → Set where

    ·_            : (L : ⟨ Ξ ∣ Δ ⟩⊢ld)
                    ------------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★ 

    #_            : (n : ℕ)
                    --------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ♯ 

    Boolean       : ⟨ Ξ ∣ Δ ⟩⊢ty ★
    
    UInteger[<=_] : (n : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                    --------------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★
    
    UInteger[_]   : (n : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                    --------------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★ 
    
    Field         : ⟨ Ξ ∣ Δ ⟩⊢ty ★
    
    Void          : ⟨ Ξ ∣ Δ ⟩⊢ty ★
    
    Bytes[_]      : (n : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                    --------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★
    
    Vector[_,_]   : (n : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                  → (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                    --------------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★ 

    Opaque[_]     : (s : String)
                    ------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★ 
    
    Enum          : (d : enum ∈ Ξ)
                    --------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★
                  
    Struct        : {Δ′    : List Kind}
                  → (d     : struct Δ′ ∈ Ξ)
                  → (targs : ∀ {k} → (x : k ∈ Δ′) → ⟨ Ξ ∣ Δ ⟩⊢ty k)
                    -----------------------------------------------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty ★
                  
    Var           : k ∈ Δ 
                    -----------
                  → ⟨ Ξ ∣ Δ ⟩⊢ty k 

  variable T₁ T₂ T₃ T T′      : ⟨ Ξ ∣ Δ ⟩⊢ty ★
           L₁ L₂ L₃ L L′      : ⟨ Ξ ∣ Δ ⟩⊢ld 
           #n #m #k           : ⟨ Ξ ∣ Δ ⟩⊢ty ♯  


  -- Existential closure of well-formed types 
  ⟨_∣_⟩⊢ty· : DeclContext → TypeContext → Set
  ⟨ Ξ ∣ Δ ⟩⊢ty· = ∃⟨ ⟨ Ξ ∣ Δ ⟩⊢ty_ ⟩
-- How about unsigned integers w/ fixed precision? 
data Numeric {Ξ} {Δ} : (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → Set where
  isUinteger : Numeric (UInteger[<= # n ])
  isFIeld    : Numeric Field 

-- Joins two numeric types 
_⋈⟨_⟩_ : (T₁ : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → (_∙_ : ℕ → ℕ → ℕ) → (T₂ : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → ⦃ Numeric T₁ ⦄ → ⦃ Numeric T₂ ⦄ →  ⟨ Ξ ∣ Δ ⟩⊢ty ★
UInteger[<= # n ] ⋈⟨ _∙_ ⟩ UInteger[<= # m ] = UInteger[<= # (n ∙ m) ]
UInteger[<= _   ] ⋈⟨ _∙_ ⟩ Field             = Field
Field             ⋈⟨ _∙_ ⟩ UInteger[<= _ ]   = Field
Field             ⋈⟨ _∙_ ⟩ Field             = Field
 
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
    kernel     : List (Callable Ξ Δ)
    operations : ⟨ Ξ ∣ Δ ⟩⊢ld → List (Callable Ξ Δ) 

open LedgerState public 

UserTypes : DeclContext → TypeContext → Set
UserTypes Ξ Δ = All (λ where 
    enum        → ℕ
    (struct Δ′) → List ( ⟨ Ξ ∣ Δ′ ++ Δ ⟩⊢ty ★)
  ) Ξ 

_∈′_or_ : Callable Ξ Δ → (_ _ : List (Callable Ξ Δ)) → Set
κ ∈′ x or y = κ ∈ x ⊎ κ ∈ y


record Context (Ξ : DeclContext) (Δ : TypeContext) : Set where
  constructor _∣_∣_∣_ 
  field
    𝒰 : UserTypes Ξ Δ
    𝒲 : Witnesses Ξ Δ
    Ω : Circuits Ξ Δ
    Λ : LedgerState Ξ Δ 

variable Γ₁ Γ₂ Γ₃ Γ′ : Variables Ξ Δ 
         𝒰₁ 𝒰₂ 𝒰₃ 𝒰′ : UserTypes Ξ Δ
         𝒲₁ 𝒲₂ 𝒲₃ 𝒲′ : Witnesses Ξ Δ 
         Ω₁ Ω₂ Ω₃ Ω′ : Circuits Ξ Δ
         Λ₁ Λ₂ Λ₃ Λ′ : LedgerState Ξ Δ 

open Context public 
