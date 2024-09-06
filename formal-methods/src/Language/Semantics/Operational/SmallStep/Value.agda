{-# OPTIONS --overlapping-instances --safe #-} 

open import Language.Type.Base
open import Language.Type.Subtype
open import Language.Type.Kind 
open import Language.Syntax.Expression
open import Language.Type.Context

open import Util.Logic
open import Util.Ternary

open import Data.Fin using (Fin ; suc ; zero)
open import Data.Sum 
open import Data.Bool hiding (T)

module Language.Semantics.Operational.SmallStep.Value {Ξ} {Δ} {𝓒} {Γ} where

data Value : (T : ⟨ Ξ ∣ Δ ⟩⊢ty ★) → (E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T) → Set where  

  defv  : Value T (`default T)

  boolv : ∀ x → Value Boolean (`bool x)

  uintv : Value (UInteger[<= # n ]) (`num n)

  strv  : ∀ s → Value (Bytes[ # strlen s ]) (`str s) 

  vecv  : (xs : Fin n → ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr T) → Value Vector[ # n , T ] (`vec n xs)

  enumv : ∀ {d} → (x : Fin _) → Value (Enum d)  (`enum d x)


-- TODO: how would we compute this? 
_⟨_⟩≟ᵇ_ : ∀ {V₁ V₂} → Value T₁ V₁ → (T₁ ≲ T₂ ⊎ T₂ ≲ T₁) → Value T₂ V₂ → Bool
v₁ ⟨ st ⟩≟ᵇ v₂ = true 
  
