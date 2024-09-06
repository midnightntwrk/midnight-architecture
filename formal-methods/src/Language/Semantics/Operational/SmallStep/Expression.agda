{-# OPTIONS --safe --overlapping-instances #-} 

open import Language.Type.Base
open import Language.Type.Kind
open import Language.Type.Context
open import Language.Type.Subtype
open import Language.Type.Substitution
open import Language.Type.Renaming

open import Util.Ternary
open import Util.Logic

open import Language.Syntax.Expression
open import Language.Semantics.Operational.SmallStep.Value

open import Data.Bool using (true ; false ; Bool ; not)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Nat
open import Data.Sum hiding (map) renaming ([_,_] to ⊎[_,_])
open import Data.List
open import Data.Product 

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All hiding (map) renaming (lookup to resolve)
open import Data.List.Relation.Unary.Any hiding (map) 

open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (IUniversal ; _⇒_ ; _⊢_) 

open import Function 

module Language.Semantics.Operational.SmallStep.Expression where

_-′_ : (n m : ℕ) → ℕ
n     -′ zero  = n
zero  -′ m     = zero
suc n -′ suc m = n -′ m

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-suc : ∀ {n m} → n ≤ m → n ≤ suc m
≤-suc z≤n      = z≤n
≤-suc (s≤s px) = s≤s (≤-suc px)

n-m≤n : ∀ n m → n -′ m ≤ n
n-m≤n zero    zero    = z≤n
n-m≤n zero    (suc m) = z≤n
n-m≤n n       zero    = ≤-refl _ 
n-m≤n (suc n) (suc m) = ≤-suc (n-m≤n n m)

⊎-≲₁ : (sub : (T₁ ≲ T₂) ⊎ (T₂ ≲ T₁)) → T₁ ⊑ ⊎[ const T₂ , const T₁ ] sub
⊎-≲₁ = ⊎[ id , const ⊑-refl ]

⊎-≲₂ : (sub : (T₁ ≲ T₂) ⊎ (T₂ ≲ T₁)) → T₂ ⊑ ⊎[ const T₂ , const T₁ ] sub
⊎-≲₂ = ⊎[ const ⊑-refl , id ]

data _[_]─→_ {𝓒 : Context Ξ Δ} {Γ} :
  ∀ {T₁ T₂ : ⟨ Ξ ∣ Δ ⟩⊢ty ★}
  → (M  : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁)
  → T₂ ≲ T₁
  → (N : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂) → Set where 

  ─→-vecelem : ∀ {n} 
               → (fs : Fin n → ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr T)
               → (i  : Fin n)
                 ---------------------------------------------
               → `vecelem (`vec n fs) i [ fs i .ι ]─→ fs i .px

  ─→-field   : ∀ {d}
               → {σ    : Substitution Δ′ Δ}
               → (args : Substitutionᴱ ⌞ σ ⌟ id 𝓒 (resolve (𝓒 .𝒰) d) Γ)
               → (mem  :  T₁ ∈ resolve (𝓒 .𝒰) d)
                 -------------------------------------------------------------
               → `field d σ (`new d σ args) mem [ args mem .ι ]─→ args mem .px 

  ─→-neg       : ∀ {x}
                 → `neg (`bool x)  [ ⊑-refl ]─→  `bool (not x)
                 
  ─→-add       : ∀ {n m}
                   ------------------------------------------------
                 → `add (`num n) (`num m) [ ⊑-refl ]─→ `num (n + m)
                 
  ─→-sub       : ∀ {n m}
                   -----------------------------------------------------------------------
                 → `sub (`num n) (`num m) [ ⊑-uint₁ (⊑-size (n-m≤n n m)) ]─→ `num (n -′ m)
                 
  ─→-mul       : ∀ {n m}
                   -------------------------------------------------
                 → `mul (`num n) (`num m) [ ⊑-refl ]─→  `num (n * m) 

  ─→-eq        :   (E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁)
                 → (E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂) 
                 → (st : T₁ ≲ T₂ ⊎ T₂ ≲ T₁)
                 → (v₁ : Value T₁ E₁)
                 → (v₂ : Value T₂ E₂)
                   ----------------------------------------------------
                 → `equals E₁ E₂ st [ ⊑-refl ]─→ `bool (v₁ ⟨ st ⟩≟ᵇ v₂) 

  ─→-or-t      : ∀ {sub} {E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T}
                   ---------------------------------------------
                 → `or (`bool true) E sub   [ sub ]─→ `bool true

  ─→-or-f      : ∀ {sub} {E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T}
                   ---------------------------------------
                 → `or (`bool false) E sub  [ ⊑-refl ]─→ E


  ─→-and-t     : ∀ {sub} {E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T}
                   --------------------------------------
                 → `and (`bool true) E sub [ ⊑-refl ]─→ E 

  ─→-and-f     : ∀ {sub} {E : ⟨ 𝓒 ∣ Γ ⟩⊢expr T}
                   ----------------------------------------------
                 → `and (`bool false) E sub [ sub ]─→ `bool false  

  ─→-le        : ∀ {n m}
               → `compare (`num n) (`num m) lt  [ ⊑-refl ]─→ `bool (n <ᵇ m)

  ─→-ge        : ∀ {n m}
               → `compare (`num n) (`num m) gt  [ ⊑-refl ]─→ `bool (m <ᵇ n)

  ─→-leq       : ∀ {n m}
               → `compare (`num n) (`num m) leq [ ⊑-refl ]─→ `bool (n ≤ᵇ m)

  ─→-geq       : ∀ {n m}
               → `compare (`num n) (`num m) geq [ ⊑-refl ]─→ `bool (m ≤ᵇ n)

  ─→-ite-t     : ∀ {sub : T₁ ≲ T₂ ⊎ T₂ ≲ T₁}
                 → {E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ }
                 → {E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ }
                   ----------------------------------------------
                 → `ite (`bool true) E₁ E₂ sub [ ⊎-≲₁ sub ]─→ E₁
  
  ─→-ite-f     : ∀ {sub : T₁ ≲ T₂ ⊎ T₂ ≲ T₁}
                 → {E₁ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₁ }
                 → {E₂ : ⟨ 𝓒 ∣ Γ ⟩⊢expr T₂ }
                   ----------------------------------------------
                 → `ite (`bool false) E₁ E₂ sub [ ⊎-≲₂ sub ]─→ E₂


  -- Map expressions are evaluated as follows:
  --
  --    map f xs₁ … xsᵢ  ─→  [ f(xs₁[0], … , xsᵢ[0]) , … , f(xs₁[n], … xsᵢ[n]) ]
  -- 
  -- That is, we define a new vector constants whose elements are given by
  -- applying `f` to corresponding elements of the vector we're mapping
  -- over. This is not unlike how the product of morphisms is computed in
  -- Cartesian categories:
  --
  --   f × g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩
  --
  ─→-map       : ∀ ( fun  : κ ∈′ 𝓒 .𝒲 or 𝓒 .Ω)
                 → ( σ    : Substitution (κ .Δᶜ) Δ)
                 → ( args : Substitutionᴱ ⌞ σ ⌟ Vector[ # n ,_] 𝓒 (κ .T∗) Γ )
                   ----------------------------------------------------------
                 → `map fun σ args
                     [ ⊑-refl ]─→
                   `vec n λ i →
                     ◇⟨ ⊑-refl ⟩
                       `call fun σ λ a → ◇⟨ (args a .ι) ⟩ (`vecelem (args a .px) i)


  -- Fold evaluates as follows, if the input vectors have length 0
  --
  --   fold f z xs₁ … xsₙ ─→ z  
  --
  ─→-fold-z    : ( fun   : callable Δ′ (T′ ∷ Γ′) T′ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
               → ( σ     : Substitution Δ′ Δ )
               → ( init  : ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ T′) )
               → ( args  : Substitutionᴱ ⌞ σ ⌟ Vector[ # 0 ,_] 𝓒 Γ′ Γ )
                 ------------------------------------------------------
               → `fold fun σ init args [ init .ι ]─→ init .px  


  -- Fold evaluates as follows, if the input vectors have length n > 0
  --
  --   fold f z xs₁ … xsᵢ ─→ fold f f(z,xs₁[0], … , xsᵢ[0]) [ xs₁[1] , … , xs₁[n-1] ] … [ xsᵢ[1] , … , xsᵢ[n-1] ]
  -- 
  ─→-fold-step : ( fun   : callable Δ′ (T′ ∷ Γ′) T′ ∈′ 𝓒 .𝒲 or 𝓒 .Ω )
               → ( σ     : Substitution Δ′ Δ )
               → ( init  : ◇ ⟨ 𝓒 ∣ Γ ⟩⊢expr (substitute ⌞ σ ⌟ T′) )
               → ( args  : Substitutionᴱ ⌞ σ ⌟ Vector[ # (suc n) ,_] 𝓒 Γ′ Γ )
                 ------------------------------------------------------------
               → `fold fun σ init args
                   [ ⊑-refl ]─→
                 `fold fun σ
                    ( ◇⟨ ⊑-refl ⟩ `call fun σ
                      ( λ where (here refl) → init
                                (there a)   → ◇⟨ args a .ι ⟩ `vecelem (args a .px) zero 
                      )
                    ) ( λ a → ◇⟨ args a .ι ⟩ `vec n (λ i → ◇⟨ ⊑-refl ⟩ `vecelem (args a .px) (suc i)))  
