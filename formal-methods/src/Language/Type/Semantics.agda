open import Language.Type.Base
open import Language.Type.Kind

open import Data.Nat using (ℕ ; _≤_; _^_) renaming (_≟_ to _≟ℕ_)
open import Data.List
open import Data.List.Relation.Unary.All  renaming (lookup to resolve)
open import Data.Product
open import Data.Bool using (Bool ; true ; false) renaming (_≟_ to _≟Bool_)
open import Data.Unit
open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Data.List.Membership.Propositional
open import Data.Vec renaming (replicate to vreplicate)

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function

module Language.Type.Semantics where


-- Just assume implementations of some of the ledger types for now. Later, we
-- can replace these with actual implementations.
--
-- It's not unlikely that these implementations would require e.g. decidable
-- equality or other properties of types. There's a couple of optiones: 
--
-- (1) We could define these implementations mutually with the semantics of
--     types and decidable equality. Decidable equality should of course also be
--     available for these implementations, since structures can be nested!
--
--       mutual
--         ⟦_⟧   : Type → Set
--         deceq : Type → Dec ⟦ T ⟧
--
-- (2) We add decidable equality as an instance argument, and construct it
--     on-demand for each type when constructing values in the semantics of a
--     type T. This would look something like the following
--
--       ⟦ SetT T ⟧ = ⦃ _ : DecEq ⟦ T ⟧ ⦄ → SetI ⟦ T ⟧  
--
--     But of course, this would require us to implement decidable equality for
--     Pi types akin to the one above ...
--
--  (3) We could also make decidable equality part of the semantics itself,
--      effectively saying that the semantics of types is sets with dedicable
--      equality.
--
--        ⟦-⟧ : Type → Σ Set DecEq 
--
--      This seems like the most favorable option, as it makes decidable
--      equality for element types available when referring to the
--      implementation of container types, by strengthening the induction
--      hypothesis, while preventing the impossible tangle of dependencies we
--      get when giving types a set semantics and defining decidable equality
--      mutually. 
-- 
module Types (SetI                : Set → Set)
             (MapI                : Set → Set → Set)
             (MerkleTreeI         : ℕ → Set → Set)
             (HistoricMerkleTreeI : ℕ → Set → Set) where 


  ⟦_⟧decl : Decl → Set₁
  ⟦ enum     ⟧decl = ⟦ ★ ⟧ᴷ 
  ⟦ struct Δ ⟧decl = (∀ {k} → k ∈ Δ → ⟦ k ⟧ᴷ) → ⟦ ★ ⟧ᴷ 

  ⟦_⟧dctx : DeclContext → Set₁
  ⟦ Ξ ⟧dctx = All ⟦_⟧decl Ξ

  ⟦_⟧tctx : TypeContext → Set₁
  ⟦ Δ ⟧tctx = All ⟦_⟧ᴷ Δ

  dec-≤ℕ : DecidableEquality (Σ ℕ λ n′ → n′ ≤ n)
  dec-≤ℕ (ℕ.zero , _≤_.z≤n) (ℕ.zero , _≤_.z≤n) = yes refl
  dec-≤ℕ (ℕ.zero , px) (ℕ.suc m , qx) = no λ() 
  dec-≤ℕ (ℕ.suc n , px) (ℕ.zero , qx) = no λ()
  dec-≤ℕ (ℕ.suc n , _≤_.s≤s px) (ℕ.suc m , _≤_.s≤s qx) with dec-≤ℕ (n , px) (m , qx) 
  ... | no ¬px   = no λ where refl → ¬px refl
  ... | yes refl = yes refl

  data Tag (s : String) : Set where
    mkTag : Tag s

  getTag : Tag s → String
  getTag {s} _ = s 

  _≟Tag_ : DecidableEquality (Tag s) 
  mkTag ≟Tag mkTag = yes refl

  Byte = Vec Bool 8

  -- All zeros
  zbyte : Byte
  zbyte = vreplicate _ false

  decvec : {A : Set} → DecidableEquality A → DecidableEquality (Vec A n)
  decvec = {!!} 

  mutual

    {- Defines the semantics of Ledger types -} 
    ⟦_⟧ᴸ : ⟨ Ξ ∣ Δ ⟩⊢ld → ⟦ Ξ ⟧dctx → ⟦ Δ ⟧tctx → ⟦ ★ ⟧ᴷ
    
    ⟦ Counter                    ⟧ᴸ ξ δ
      = {!!}

    ⟦ Cell Tⱽ                    ⟧ᴸ ξ δ
      = {!!}

    ⟦ SetT L                     ⟧ᴸ ξ δ
      = {!!}

    ⟦ Map Tᴷ L                   ⟧ᴸ ξ δ
      = {!!}

    ⟦ ListT L                    ⟧ᴸ ξ δ
      = {!!}

    ⟦ MerkleTree depth L         ⟧ᴸ ξ δ
      = {!!}

    ⟦ HistoricMerkleTree depth L ⟧ᴸ ξ δ
      = {!!}

    
    {- Defines the semantics of Compact types -} 
    ⟦_⟧ᵀ : ⟨ Ξ ∣ Δ ⟩⊢ty k → ⟦ Ξ ⟧dctx → ⟦ Δ ⟧tctx → ⟦ k ⟧ᴷ

    ⟦ · L              ⟧ᵀ ξ δ
      = ⟦ L ⟧ᴸ ξ δ

    ⟦ # n              ⟧ᵀ ξ δ
      = record { size = n }

    ⟦ Boolean          ⟧ᵀ ξ δ = record
      { carrier   = Bool
      ; decidable = _≟Bool_
      ; default   = false
      }

    ⟦ UInteger[<= #n ] ⟧ᵀ ξ δ = record
      { carrier   = Σ ℕ (λ n → n ≤ ⟦ #n ⟧ᵀ ξ δ .size)
      ; decidable = dec-≤ℕ
      ; default   = (0 , _≤_.z≤n)
      }

    ⟦ UInteger[ #n ]   ⟧ᵀ ξ δ = record
      { carrier   = Σ ℕ (λ n → n ≤ 2 ^ ⟦ #n ⟧ᵀ ξ δ .size)
      ; decidable = dec-≤ℕ
      ; default   = (0 , _≤_.z≤n)
      }

    ⟦ Field            ⟧ᵀ ξ δ = record
      { carrier   = ℕ
      ; decidable = _≟ℕ_
      ; default   = 0
      } 

    ⟦ Void             ⟧ᵀ ξ δ = record
      { carrier   = ⊤
      ; decidable = λ _ _ → yes refl
      ; default   = tt
      } 

    ⟦ Bytes[ #n ]      ⟧ᵀ ξ δ = record
      { carrier   = Vec Byte (⟦ #n ⟧ᵀ ξ δ .size)
      ; decidable = decvec (decvec _≟Bool_)
      ; default   = vreplicate _ zbyte
      }
      
    ⟦ Vector[ #n , T ] ⟧ᵀ ξ δ = record
      { carrier   = Vec (⟦ T ⟧ᵀ ξ δ .carrier) (⟦ #n ⟧ᵀ ξ δ .size)
      ; decidable = decvec (⟦ T ⟧ᵀ ξ δ .decidable)
      ; default   = vreplicate _ (⟦ T ⟧ᵀ ξ δ .default)
      }

    ⟦ Opaque[ s ]      ⟧ᵀ ξ δ = record
      { carrier   = Tag s
      ; decidable = _≟Tag_
      ; default   = mkTag
      }
    
    ⟦ Enum d           ⟧ᵀ ξ δ
      = resolve ξ d
      
    ⟦ Struct d T∗      ⟧ᵀ ξ δ
    
      = resolve ξ d λ x → ⟦ T∗ x ⟧ᵀ ξ δ

    ⟦ Var α            ⟧ᵀ ξ δ
      = resolve δ α
