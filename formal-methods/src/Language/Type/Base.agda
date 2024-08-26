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

    SetT               : (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                         ---------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
    
    Map                : (Tᴷ : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                       → (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ld ⊎ (⟨ Ξ ∣ Δ ⟩⊢ty ★)) 
                         -------------------------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
                        
    ListT              : (Tⱽ : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                         ---------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld
                       
    MerkleTree         : (depth : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                       → (Tⱽ    : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
                         ------------------------
                       → ⟨ Ξ ∣ Δ ⟩⊢ld 
                       
    HistoricMerkleTree : (depth : ⟨ Ξ ∣ Δ ⟩⊢ty ♯)
                       → (Tⱽ    : ⟨ Ξ ∣ Δ ⟩⊢ty ★)
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
                  
    Struct        : {Δ′ : List Kind}
                  → (d  : struct Δ′ ∈ Ξ)
                  → (T∗ : ∀ {k} → (x : k ∈ Δ′) → ⟨ Ξ ∣ Δ ⟩⊢ty k)
                    -------------------------------------------
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

data Castable {Ξ} {Δ} : (T₁ T₂ : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → Set where
  field→field : Castable Field Field
  uint→field  : Castable (UInteger[<= #n ]) Field
  --- TODO: and more 

