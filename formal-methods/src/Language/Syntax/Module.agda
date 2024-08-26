{-# OPTIONS --overlapping-instances #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution

open import Language.Syntax.Expression 

open import Util.Logic
open import Util.Ternary

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_ ; _+_ ; _*_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map) renaming (lookup to resolve) 
open import Data.List.Relation.Unary.All hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.Fin using (Fin)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_ ; Satisfiable)

module Language.Syntax.Module where


-- 
-- _𝒰∷_ : ∀ {d} → (u : Usertype d Ξ Δ) → Context Ξ Δ → Context (d ∷ Ξ) Δ
-- (u 𝒰∷ 𝓒) .𝒰 = u , (𝓒 .𝒰)
-- (u 𝒰∷ 𝓒) .𝒲 = {!rename ? ?!}
-- (u 𝒰∷ 𝓒) .Ω  = {!\!}
-- (u 𝒰∷ 𝓒) .Λ  = {!!} 
-- 
-- 
-- _Ω∷_ : Callable Ξ Δ → Context Ξ Δ → Context Ξ Δ
-- (κ Ω∷ 𝓒) .𝒰 = 𝓒 .𝒰
-- (κ Ω∷ 𝓒) .𝒲 = 𝓒 .𝒲
-- (κ Ω∷ 𝓒) .Ω  = κ ∷ 𝓒 .Ω 
-- (κ Ω∷ 𝓒) .Λ  = 𝓒 .Λ
-- 
-- 
-- Q: name binding in modules, is mutual recursion between circuits allowed? 

data ⟨_∣_⟩⊢mod⊣⟨_∣_⟩ {Ξ} {Δ} (𝓒 : Context Ξ Δ) (Γ : Variables Ξ Δ) : (𝓒′ : Context) → Set where


  -- -- Q: can definitions from other modules be re-exported using the "export" keyword? 
  -- `export  : (exports : List (T ∈ Γ))
  --            ----------------------------------
  --          → ⟨ 𝓒 ∣ Γ ⟩⊢mod⊣⟨ ? ∣ ? ⟩

  -- `circuit : (Δ′ : TypeContext)
  --          → {!!}
  --            ---------------------------
  --          → ⟨ 𝓒 ∣ Γ ⟩⊢mod⊣⟨ [] ∣ {!!} ∷ Γ ⟩
