open import Data.Nat using (ℕ ; _≤_ ; _^_ ; z≤n)
open import Data.String using (String)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product hiding (map)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe ; maybe ; just)

open import Data.List using (List; []; _∷_; _++_ ; map)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All ; lookup ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using ()

open import Relation.Nullary.Negation
open import Relation.Unary using ()
open import Relation.Binary using (Reflexive ; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_) 

open import Level renaming (suc to sℓ)
open import Function
open import Function.Bundles

open import Language.Type.Kind 

module Language.Type.Base where

data TCEntry : Set where
  tvar   : (k : Kind) → TCEntry
  enum   : TCEntry
  struct : (Ts : List Kind) → TCEntry

TypeContext = List TCEntry 

variable Δ Δ₁ Δ₂ Δ₃ Δ′ : TypeContext 
         n n₁ n₂ n₃ n′ : ℕ
         s s₁ s₂ s₃ s′ : String 

mutual
  infix 7  #_
  data _⊢-ty_ (Δ : TypeContext) : Kind → Set where

    #_            : (n : ℕ)
                    --------
                  → Δ ⊢-ty ♯ 

    Boolean       : Δ ⊢-ty ★
    
    UInteger[<=_] : (n : Δ ⊢-ty ♯)
                    --------------
                  → Δ ⊢-ty ★
    
    UInteger[_]   : (n : Δ ⊢-ty ♯)
                    --------------
                  → Δ ⊢-ty ★ 
    
    Field         : Δ ⊢-ty ★
    
    Void          : Δ ⊢-ty ★
    
    Bytes[_]      : (n : Δ ⊢-ty ♯)
                    --------------
                  → Δ ⊢-ty ★
    
    Vector[_,_]   : (n : Δ ⊢-ty ♯) → (T : Δ ⊢-ty ★)
                    -------------------------------
                  → Δ ⊢-ty ★ 

    Opaque[_]     : (s : String)
                    ------------
                  → Δ ⊢-ty ★ 
    
    Enum          : (α : enum ∈ Δ)
                    --------------
                  → Δ ⊢-ty ★
                  
    Struct        : {ks    : List Kind}
                  → (α     : struct ks ∈ Δ)
                  → (targs : ∀ {k} → (x : k ∈ ks) → Δ ⊢-ty k)
                    -----------------------------------------
                  → Δ ⊢-ty ★

    -- Ledger types 
    Counter            : Δ ⊢-ty ★  

    Cell               : (Tⱽ : Δ ⊢-ty ★)
                       → (px : CompactType Tⱽ)
                         ---------------------
                       → Δ ⊢-ty ★ 

    SetT               : (Tⱽ : Δ ⊢-ty ★)
                         ---------------
                       → Δ ⊢-ty ★ 
    
    Map                : (Tᴷ Tⱽ : Δ ⊢-ty ★)
                         ------------------
                       → Δ ⊢-ty ★ 
                        
    ListT              : (Tⱽ : Δ ⊢-ty ★)
                         ---------------
                       → Δ ⊢-ty ★
                       
    MerkleTree         : (depth : Δ ⊢-ty ♯)
                       → (Tⱽ    : Δ ⊢-ty ★)
                         ----------------
                       → Δ ⊢-ty ★ 
                       
    HistoricMerkleTree : (depth : Δ ⊢-ty ♯)
                       → (Tⱽ    : Δ ⊢-ty ★)
                         ----------------
                       → Δ ⊢-ty ★   

    -- Type variables can be ledger types and compact types? 
    Var           : tvar k ∈ Δ → Δ ⊢-ty k 

  variable T₁ T₂ T₃ T T′      : Δ ⊢-ty ★   
           Ts Ts₁ Ts₂ Ts₃ Ts′ : List (Δ ⊢-ty ★)
           #n #m #k           : Δ ⊢-ty ♯  

  -- A predicate proving that `T` is a Compact type 
  data CompactType {Δ} : (T : Δ ⊢-ty ★) → Set where
    isBoolean   : CompactType Boolean
    isUInteger₁ : CompactType UInteger[<= #n ] 
    isUInteger₂ : CompactType UInteger[ #n ]
    isField     : CompactType Field 
    isVoid      : CompactType Void
    isBytes     : CompactType Bytes[ #n ]
    isVector    : CompactType Vector[ #n , T ]
    isOpaque    : CompactType Opaque[ s ]
    isEnum      : ∀ x → CompactType (Enum x)
    isStruct    :   {ks   : List Kind}
                  → (x    : struct ks ∈ _)
                  → (args : {k : Kind} → k ∈ ks → Δ ⊢-ty k)
                  → CompactType (Struct x args) 

-- The ledger types are all those that are not compact types (?)
LedgerType : (T : Δ ⊢-ty ★) → Set
LedgerType T = ¬ CompactType T


-- Entries in a type context 
data Entry (Δ : TypeContext) : Set where

  var     : Δ ⊢-ty ★
            --------
          → Entry Δ

  circuit : (ks      : List Kind)
          → (T∗      : List (∃ λ k → (map tvar ks ++ Δ) ⊢-ty k)) 
          → (returns : Δ ⊢-ty ★)
            -----------------------------------------------------
          → Entry Δ  


Context : TypeContext → Set
Context Δ = List (Entry Δ)

variable Γ₁ Γ₂ Γ₃ Γ Γ′ : Context Δ 

