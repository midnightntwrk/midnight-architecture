open import Data.Nat 
open import Data.Nat.Properties 

open import Data.Vec 

open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.Product
open import Data.Sum using (_⊎_) renaming ([_,_] to ⊎[_,_]) 

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Language.Type.Kind
open import Language.Type.Base


open import Util.Ternary

module Language.Type.Subtype where 

infix 5 _⊑_
data _⊑_ {Ξ} {Δ} : ∀ {k} → (T₁ T₂ : ⟨ Ξ ∣ Δ ⟩⊢ty k) → Set where  

  ⊑-refl    : Reflexive (_⊑_ {k = k})

  ⊑-trans   : Transitive (_⊑_ {k = k})  

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

instance ≲-type : HasRel₂ (⟨ Ξ ∣ Δ ⟩⊢ty k) _
HasRel₂._≲_ ≲-type = _⊑_
