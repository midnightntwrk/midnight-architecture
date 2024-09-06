

{-# OPTIONS --overlapping-instances --safe #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Subtype 
open import Language.Type.Renaming
open import Language.Type.Substitution
open import Language.Type.Context

open import Language.Syntax.Expression
open import Language.Syntax.Statement

open import Util.Logic
open import Util.Ternary

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; _≤_ ; _+_ ; _*_)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (map) renaming (lookup to resolve) 
open import Data.List.Relation.Unary.All renaming (map to map-all)
open import Data.Product hiding (map)
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.Fin using (Fin)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_ ; Satisfiable)

module Language.Syntax.Module where

_𝒰∷_ : ∀ {d} → (u : Usertype Ξ Δ d) → Context Ξ Δ → Context (d ∷ Ξ) Δ
(u 𝒰∷ 𝓒) .𝒰 = rename there u ∷ map-all (rename there) (𝓒 .𝒰)
(u 𝒰∷ 𝓒) .𝒲 = rename there (𝓒 .𝒲)
(u 𝒰∷ 𝓒) .Ω  = rename there (𝓒 .Ω)
(u 𝒰∷ 𝓒) .Λ  = rename there (𝓒 .Λ) 

_Ω∷_ : Callable Ξ Δ → Context Ξ Δ → Context Ξ Δ
(κ Ω∷ 𝓒) .𝒰 = 𝓒 .𝒰
(κ Ω∷ 𝓒) .𝒲 = 𝓒 .𝒲
(κ Ω∷ 𝓒) .Ω  = κ ∷ 𝓒 .Ω 
(κ Ω∷ 𝓒) .Λ  = 𝓒 .Λ

Export : Context Ξ Δ → Set
Export {Ξ} 𝓒 = ∃⟨ _∈ 𝓒 .Ω ⟩ ⊎ ∃⟨ _∈ Ξ ⟩

-- Q: name binding in modules, is mutual recursion between circuits allowed? 

data ⟨_⟩⊢mod⊣⟨_∣_⟩ (𝓒 : Context Ξ Δ)
     : ( 𝓒′      : Context Ξ′ Δ )
     → ( exports : List (Export 𝓒′) ) → Set where

  `export  : ( exports : List (Export 𝓒) )
             -----------------------------
           → ⟨ 𝓒 ⟩⊢mod⊣⟨ 𝓒 ∣ exports ⟩

  `circuit : ( Δ′   : TypeContext )
           → ( T∗   : List (⟨ Ξ ∣ Δ′ ++ Δ ⟩⊢ty ★) )
           → ( Tᴿ   : ⟨ Ξ ∣ Δ′ ++ Δ ⟩⊢ty ★ )
           → ( body : ∃[ Γ′ ] ⟨ rename (∈-++⁺ʳ _) 𝓒 ∣ [] ⟩⊢stmt∗ Tᴿ ⊣ Γ′ )
             -------------------------------------------------------------
           → ⟨ 𝓒 ⟩⊢mod⊣⟨ callable Δ′ T∗ Tᴿ Ω∷ 𝓒 ∣ [] ⟩

  `enum    : ( n : ℕ )
             -------------------------
           → ⟨ 𝓒 ⟩⊢mod⊣⟨ n 𝒰∷ 𝓒 ∣ [] ⟩

  `struct  : ( Δ′ : TypeContext)
           → ( T∗ : List (⟨ Ξ ∣ Δ′ ++ Δ ⟩⊢ty ★) )
             ------------------------------------
           → ⟨ 𝓒 ⟩⊢mod⊣⟨ T∗ 𝒰∷ 𝓒 ∣ [] ⟩ 

mutual 
  data ⟨_⟩⊢mod∗⊣⟨_∣_⟩ (𝓒 : Context Ξ Δ) : (𝓒′ : Context Ξ′ Δ) → List (Export 𝓒′) → Set where
  
    ε   : ⟨ 𝓒 ⟩⊢mod∗⊣⟨ 𝓒 ∣ [] ⟩  

    _·_ : ∀ { xs : List (Export 𝓒₁) }
          → { ys : List (Export 𝓒₂) }
          → ( decl  : ⟨ 𝓒 ⟩⊢mod⊣⟨ 𝓒₁ ∣ xs ⟩ )
          → ( decls : ⟨ 𝓒₁ ⟩⊢mod∗⊣⟨ 𝓒₂ ∣ ys ⟩ )
            ------------------------------------------------------
          → ⟨ 𝓒 ⟩⊢mod∗⊣⟨ 𝓒₂ ∣ map (update-export decls) xs ++ ys ⟩ 

  update-export : ∀ {ys} → (decls : ⟨ 𝓒₁ ⟩⊢mod∗⊣⟨ 𝓒₂ ∣ ys ⟩) → (xs : Export 𝓒₁) → Export 𝓒₂
  update-export ε                                e = e
  update-export (`export _              · decls) e = update-export decls e
  update-export (`circuit Δ′ T∗ Tᴿ body · decls) e = update-export decls (inj₁ ((callable Δ′ T∗ Tᴿ) , here refl))
  update-export (`enum n                · decls) e = update-export decls (inj₂ (enum , here refl))
  update-export (`struct Δ′ T∗          · decls) e = update-export decls (inj₂ ((struct Δ′) , here refl))
  
