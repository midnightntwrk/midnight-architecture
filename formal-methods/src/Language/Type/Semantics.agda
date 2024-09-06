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
open import Data.Sum renaming ([_,_] to ⊎[_,_])
open import Data.Maybe using (Maybe ; just ; nothing; maybe′)

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Util.Ternary

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
module Types (SetI                : Set+ → Set+)
             (MapI                : Set+ → Set+ → Set+)
             (MerkleTreeI         : ℕ → Set+ → Set+)
             (HistoricMerkleTreeI : ℕ → Set+ → Set+) where 

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
  decvec dec [] [] = yes refl
  decvec dec (x ∷ xs) (y ∷ ys) with dec x y | decvec dec xs ys
  ... | no ¬p    | no ¬q    = no λ where refl → ¬p refl
  ... | no ¬p    | yes q    = no λ where refl → ¬p refl  
  ... | yes p    | no ¬q    = no λ where refl → ¬q refl 
  ... | yes refl | yes refl = yes refl

  declist : {A : Set} → DecidableEquality A → DecidableEquality (List A)
  declist dec []      []        = yes refl
  declist dec []      (_ ∷ _)   = no λ()
  declist dec (_ ∷ _) []        = no λ()
  declist dec (x ∷ xs) (y ∷ ys) with dec x y | declist dec xs ys
  ... | no ¬p    | no ¬q    = no λ where refl → ¬p refl
  ... | no ¬p    | yes q    = no λ where refl → ¬p refl  
  ... | yes p    | no ¬q    = no λ where refl → ¬q refl 
  ... | yes refl | yes refl = yes refl

  mutual

    {- Defines the semantics of Ledger types -} 
    ⟦_⟧ᴸ : ⟨ Ξ ∣ Δ ⟩⊢ld → ⟦ Ξ ⟧dctx → ⟦ Δ ⟧tctx → ⟦ ★ ⟧ᴷ
    
    ⟦ Counter                    ⟧ᴸ ξ δ = record
      { carrier   = ℕ
      ; decidable = _≟ℕ_
      ; default   = 0
      }

    ⟦ Cell Tⱽ                    ⟧ᴸ ξ δ
      = ⟦ Tⱽ ⟧ᵀ ξ δ

    ⟦ SetT T                     ⟧ᴸ ξ δ = SetI (⟦ T ⟧ᵀ ξ δ)

    ⟦ Map Tⱽ (inj₁ L) ⟧ᴸ ξ δ
      = MapI (⟦ Tⱽ ⟧ᵀ ξ δ) (⟦ L ⟧ᴸ ξ δ)
    ⟦ Map Tⱽ (inj₂ T) ⟧ᴸ ξ δ
      = MapI (⟦ Tⱽ ⟧ᵀ ξ δ) (⟦ T ⟧ᵀ ξ δ)

    ⟦ ListT T                    ⟧ᴸ ξ δ = record
      { carrier   = List (⟦ T ⟧ᵀ ξ δ .carrier)
      ; decidable = declist (⟦ T ⟧ᵀ ξ δ .decidable)
      ; default   = []
      }

    ⟦ MerkleTree depth T         ⟧ᴸ ξ δ
      = MerkleTreeI (⟦ depth ⟧ᵀ ξ δ .size) (⟦ T ⟧ᵀ ξ δ)

    ⟦ HistoricMerkleTree depth T ⟧ᴸ ξ δ
      = HistoricMerkleTreeI (⟦ depth ⟧ᵀ ξ δ .size) (⟦ T ⟧ᵀ ξ δ)


    {- Defines the semantics of Compact types -} 
    ⟦_⟧ᵀ : ⟨ Ξ ∣ Δ ⟩⊢ty k → ⟦ Ξ ⟧dctx → ⟦ Δ ⟧tctx → ⟦ k ⟧ᴷ

    ⟦ · L              ⟧ᵀ ξ δ  
      = ⟦ L ⟧ᴸ ξ δ -- This defines a pass-by-value semantics. Should be pass-by-reference!? 

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



-- Characterizes that `A` is a subset of `B`. Subsets are witnessed by a pair of
-- functions that go back and forth, and a proof that these form a
-- section/retraction pair.
--
-- As a consequence, `up` is injective, and `down` surjective 
record _⊆_ (A B : Set) : Set where
  field
    up      : A → B
    down    : B → Maybe A 
    inverse : ∀ x → down (up x) ≡ just x 

open _⊆_

instance ≲-set : HasRel₂ Set _
HasRel₂._≲_ ≲-set = _⊆_

⊆-refl : Reflexive _⊆_
⊆-refl .up      = λ x → x 
⊆-refl .down    = just 
⊆-refl .inverse = λ _ → refl 

⊆-trans : Transitive _⊆_
⊆-trans px qx .up      = λ x → qx .up (px .up x)
⊆-trans px qx .down    = λ x → maybe′ (px .down) nothing (qx .down x)
⊆-trans px qx .inverse = λ x →
  begin
     maybe′ (px .down) nothing (qx .down (qx .up (px .up x)))
  ≡⟨ cong (maybe′ (px .down) nothing) (qx .inverse (px .up x)) ⟩
    maybe′ (px .down) nothing (just (px .up x))
  ≡⟨⟩
    px .down (px .up x) 
  ≡⟨ px .inverse x ⟩ 
    just x
  ∎
  where open ≡-Reasoning

open import Relation.Unary hiding (_⊆_)
open import Function



{- TODO: prove the semantic inclusions below -} 
postulate 
  ⊆-uint  : n₁ ≤ n₂ → (∃ λ n′ → n′ ≤ n₁) ⊆ ∃ λ n′ → n′ ≤ n₂
  ⊆-field : (∃ λ n′ → n′ ≤ n) ⊆ ℕ
  -- If `B` has default values we can "pad" the vector with. 
  ⊆-vec   : {A B : Set} → n₁ ≤ n₂ → A ⊆ B → Vec A n₁ ⊆ Vec B n₂ 


-- module _ (SetI                : Set → Set)
--          (MapI                : Set → Set → Set)
--          (MerkleTreeI         : ℕ → Set → Set)
--          (HistoricMerkleTreeI : ℕ → Set → Set) where 

--   open Types SetI MapI MerkleTreeI HistoricMerkleTreeI 

--   ⟦_⟧⊑ : T₁ ⊑ T₂ → ∀ {δ} → ⟦ T₁ ⟧T δ ⊆ ⟦ T₂ ⟧T δ
--   ⟦ ⊑-refl      ⟧⊑ = ⊆-refl
--   ⟦ ⊑-trans x y ⟧⊑ = ⊆-trans ⟦ x ⟧⊑ ⟦ y ⟧⊑
--   ⟦ ⊑-uint px   ⟧⊑ = ⊆-uint px
--   ⟦ ⊑-field     ⟧⊑ = ⊆-field
--   ⟦ ⊑-vec px s  ⟧⊑ = ⊆-vec px ⟦ s ⟧⊑

--   ↑ : T₁ ⊑ T₂ → ∀[ ⟦ T₁ ⟧T ⇒ ⟦ T₂ ⟧T ]
--   ↑ s = ⟦ s ⟧⊑ .up 
  
--   ↓ : T₁ ⊑ T₂ → ∀[ ⟦ T₂ ⟧T ⇒ Maybe ∘ ⟦ T₁ ⟧T ]
--   ↓ s = ⟦ s ⟧⊑ .down 

-- -- Proves that `T` is equal to the maximum of `T₁` and `T₂` 
-- record _≈max[_,_] (T T₁ T₂ : Type Δ) : Set where
--   field
--     value   : T ≡ T₁ ⊎ T ≡ T₂
--     subtype : ⊎[ (λ where refl → T₂ ⊑ T₁) , (λ where refl → T₁ ⊑ T₂) ] value  

-- open _≈max[_,_]

