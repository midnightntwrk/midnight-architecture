{-# OPTIONS --overlapping-instances #-}

open import Language.Type.Base
open import Language.Type.Context
open import Language.Type.Kind
open import Language.Type.Subtype
open import Language.Type.Renaming

open import Language.Syntax.Expression

open import Util.Logic
open import Util.Ternary

open import Data.List
open import Data.Nat 
open import Data.Bool

module Language.Semantics.Operational.SmallStep.Default where


default-expr : {𝓒 : Context Ξ Δ} → (T : ⟨ Ξ ∣ [] ⟩⊢ty ★) → ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr (rename (λ()) T) 
default-expr (· L)             = {!!}
default-expr Boolean           = ◇⟨ ⊑-refl ⟩ (`bool false)
default-expr UInteger[<= # n ] = ◇⟨ ⊑-uint₁ (⊑-size z≤n) ⟩ (`num 0)
default-expr UInteger[ # n ]   = ◇⟨ {!⊑-uint₂ ?!} ⟩ (`num 0)
default-expr Field             = ◇⟨ ⊑-refl ⟩ `cast uint→field (`num 0)
default-expr Void              = {!!}
default-expr Bytes[ # n ]      = ◇⟨ ⊑-bytes (⊑-size z≤n) ⟩ (`str "")
default-expr Vector[ # n , T ] = ◇⟨ ⊑-refl ⟩ `vec n λ i → default-expr T
default-expr Opaque[ s ] = {!!}
default-expr (Enum d) = {!!}
default-expr (Struct d T∗)     = ◇⟨ ⊑-refl ⟩ `new {!!} {!!} {!!}
default-expr (Var ())


{-

What should be the default value of

* Generic struct
* Field
* 
* 





-} 
