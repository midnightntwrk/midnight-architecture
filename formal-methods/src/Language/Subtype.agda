open import Data.Nat 
open import Data.Nat.Properties 

open import Data.Vec 

open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.Product
open import Data.Sum using (_⊎_) renaming ([_,_] to ⊎[_,_]) 

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Language.Kind
open import Language.Type  

module Language.Subtype where 

infix 5 _⊑_
data _⊑_ {Δ} : {k : Kind} → (T₁ T₂ : Δ ⊢-ty k) → Set where  

  ⊑-refl    : ∀ {k} → Reflexive (_⊑_ {k = k})

  ⊑-trans   : ∀ {k} → Transitive (_⊑_ {k = k}) 

  ⊑-size    : n₁ ≤ n₂
              -----------
            → # n₁ ⊑ # n₂ 

  ⊑-uint    : #m ⊑ #m 
              -----------------------------------
            → UInteger[<= #n ] ⊑ UInteger[<= #m ]

  ⊑-field   : UInteger[<= #n ] ⊑ Field  

  ⊑-vec     : #n ⊑ #m
            → T₁ ⊑ T₂
              -------------------------------------
            → Vector[ #n , T₁ ] ⊑ Vector[ #m , T₂ ]


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

