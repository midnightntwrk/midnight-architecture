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

open import Language.Kind 

module Language.Type where

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

-- ⟦_⟧entry : (e : TCEntry) → {!!} 
-- ⟦ tvar ♯    ⟧entry = {!!}
-- ⟦ tvar ★    ⟧entry = {!!}
-- ⟦ enum      ⟧entry = {!!}
-- ⟦ struct Ts ⟧entry = {!!}


-- -- ⟦ enum     ⟧entry = Lift _ ℕ
-- -- ⟦ struct n ⟧entry = (Fin n → Set) → List Set


-- -- ⟦_⟧ctx = All ⟦_⟧entry

-- -- Byte = Vec Bool 8

-- -- Tuple : List Set → Set
-- -- Tuple []       = ⊤
-- -- Tuple (A ∷ xs) = A × Tuple xs

-- -- data Tag (tag : String) : Set where
-- --    mkTag : Tag tag 


-- -- -- -- Just assume implementations of some of the ledger types for now. Later, we
-- -- -- -- can replace these with actual implementations.
-- -- -- --
-- -- -- -- It's not unlikely that these implementations would require e.g. decidable
-- -- -- -- equality or other properties of types. There's a couple of optiones: 
-- -- -- --
-- -- -- -- (1) We could define these implementations mutually with the semantics of
-- -- -- --     types and decidable equality. Decidable equality should of course also be
-- -- -- --     available for these implementations, since structures can be nested!
-- -- -- --
-- -- -- --       mutual
-- -- -- --         ⟦_⟧   : Type → Set
-- -- -- --         deceq : Type → Dec ⟦ T ⟧
-- -- -- --
-- -- -- -- (2) We add decidable equality as an instance argument, and construct it
-- -- -- --     on-demand for each type when constructing values in the semantics of a
-- -- -- --     type T. This would look something like the following
-- -- -- --
-- -- -- --       ⟦ SetT T ⟧ = ⦃ _ : DecEq ⟦ T ⟧ ⦄ → SetI ⟦ T ⟧  
-- -- -- --
-- -- -- --     But of course, this would require us to implement decidable equality for
-- -- -- --     Pi types akin to the one above ...
-- -- -- --
-- -- -- --  (3) We could also make decidable equality part of the semantics itself,
-- -- -- --      effectively saying that the semantics of types is sets with dedicable
-- -- -- --      equality.
-- -- -- --
-- -- -- --        ⟦-⟧ : Type → Σ Set DecEq 
-- -- -- --
-- -- -- --      This seems like the most favorable option, as it makes decidable
-- -- -- --      equality for element types available when referring to the
-- -- -- --      implementation of container types, by strengthening the induction
-- -- -- --      hypothesis, while preventing the impossible tangle of dependencies we
-- -- -- --      get when giving types a set semantics and defining decidable equality
-- -- -- --      mutually. 
-- -- -- -- 
-- -- -- module Types (SetI                : Set → Set)
-- -- --              (MapI                : Set → Set → Set)
-- -- --              (MerkleTreeI         : ℕ → Set → Set)
-- -- --              (HistoricMerkleTreeI : ℕ → Set → Set) where 
  

-- -- --   ⟦_⟧T : Type Δ → ⟦ Δ ⟧ctx → Set 
-- -- --   ⟦ Boolean                ⟧T δ = Bool
-- -- --   ⟦ UInteger[<= n ]        ⟧T δ = ∃ λ n′ → n′ ≤ n
-- -- --   ⟦ UInteger[ n ]          ⟧T δ = ∃ λ n′ → n′ ≤ 2 ^ n
-- -- --   ⟦ Field                  ⟧T δ = ℕ
-- -- --   ⟦ Void                   ⟧T δ = ⊤
-- -- --   ⟦ Bytes[ n ]             ⟧T δ = Vec Byte n
-- -- --   ⟦ Vector[ n , T ]        ⟧T δ = Vec (⟦ T ⟧T δ) n
-- -- --   ⟦ Opaque[ s ]            ⟧T δ = Tag s
-- -- --   ⟦ Var x                  ⟧T δ = lookup δ x
-- -- --   ⟦ Enum x                 ⟧T δ = Fin (lookup δ x .lower)
-- -- --   ⟦ Struct x xs            ⟧T δ = Tuple (lookup δ x (flip ⟦_⟧T δ ∘ xs))
-- -- --   ⟦ Counter                ⟧T δ = ℕ
-- -- --   ⟦ Cell T _               ⟧T δ = ⟦ T ⟧T δ
-- -- --   ⟦ SetT T                 ⟧T δ = SetI (⟦ T ⟧T δ)
-- -- --   ⟦ Map T₁ T₂              ⟧T δ = MapI (⟦ T₁ ⟧T δ) (⟦ T₂ ⟧T δ)
-- -- --   ⟦ ListT T                ⟧T δ = List (⟦ T ⟧T δ)
-- -- --   ⟦ MerkleTree d T         ⟧T δ = MerkleTreeI d (⟦ T ⟧T δ)
-- -- --   ⟦ HistoricMerkleTree d T ⟧T δ = HistoricMerkleTreeI d (⟦ T ⟧T δ)
