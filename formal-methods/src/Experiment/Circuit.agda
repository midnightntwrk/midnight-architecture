open import Data.Nat
open import Data.Bool 
open import Data.Product 
open import Data.List hiding (and ; or)
open import Data.Empty 
open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

module Experiment.Circuit where

variable i i′ i₁ i₂ o o′ o₁ o₂ : Set 

data Gate : (i o : Set) → Set₁ where
  and or  : Gate (Bool × Bool) Bool 
  neg     : Gate Bool Bool
  add mul : Gate (ℕ × ℕ) ℕ
  leq geq : Gate (ℕ × ℕ) Bool
  δ       : Gate i (i × i) 

⟦_⟧ᴳ : Gate i o → i → o
⟦ and ⟧ᴳ (x , y) = x ∧ y
⟦ or  ⟧ᴳ (x , y) = x ∨ y
⟦ neg ⟧ᴳ x       = not x
⟦ add ⟧ᴳ (x , y) = x + y
⟦ mul ⟧ᴳ (x , y) = x * y
⟦ leq ⟧ᴳ (x , y) = x ≤ᵇ y
⟦ geq ⟧ᴳ (x , y) = y ≤ᵇ x
⟦ δ   ⟧ᴳ x       = x , x 

variable Γ : List Set  

infixr 8 _⨟_
infixr 9 _⊗_

data Circuit : (i : Set) → (o : Set) → Set₁ where
  id  : Circuit i i
  ↑_  : Gate i o → Circuit i o
  _⨟_ : Circuit i o → Circuit o o′ → Circuit i o′
  _⊗_ : Circuit i₁ o₁ → Circuit i₂ o₂ → Circuit (i₁ × i₂) (o₁ × o₂)
  π₁  : Circuit (i₁ × i₂) i₁
  π₂  : Circuit (i₁ × i₂) i₂

⟦_⟧ᶜ : Circuit i o → i → o
⟦ id      ⟧ᶜ x       = x
⟦ ↑ g     ⟧ᶜ x       = ⟦ g ⟧ᴳ x
⟦ ω₁ ⨟ ω₂ ⟧ᶜ x       = ⟦ ω₂ ⟧ᶜ (⟦ ω₁ ⟧ᶜ x)
⟦ ω₁ ⊗ ω₂ ⟧ᶜ (x , y) = ⟦ ω₁ ⟧ᶜ x , ⟦ ω₂ ⟧ᶜ y
⟦ π₁      ⟧ᶜ (x , _) = x
⟦ π₂      ⟧ᶜ (_ , y) = y

variable s t : Set 

data Expr (Γ : List Set) : Set → Set₁ where
  `and `or  : Expr Γ Bool → Expr Γ Bool → Expr Γ Bool
  `neg      : Expr Γ Bool → Expr Γ Bool
  `add `mul : Expr Γ ℕ → Expr Γ ℕ → Expr Γ ℕ
  `leq `geq : Expr Γ ℕ → Expr Γ ℕ → Expr Γ Bool 
  `var      : t ∈ Γ → Expr Γ t

∙⟨_⟩ : List Set → Set
∙⟨ []    ⟩ = ⊤
∙⟨ i ∷ Γ ⟩ = i × ∙⟨ Γ ⟩

resolveᶜ : o ∈ Γ → Circuit ∙⟨ Γ ⟩ o
resolveᶜ (here refl) = π₁
resolveᶜ (there x)   = π₂ ⨟ resolveᶜ x

compile : Expr Γ o → Circuit ∙⟨ Γ ⟩ o 
compile (`and e₁ e₂) = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ and 
compile (`or e₁ e₂)  = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ or
compile (`neg e)     = compile e ⨟ ↑ neg 
compile (`var x)     = resolveᶜ x
compile (`add e₁ e₂) = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ add
compile (`mul e₁ e₂) = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ mul
compile (`leq e₁ e₂) = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ leq
compile (`geq e₁ e₂) = ↑ δ ⨟ compile e₁ ⊗ compile e₂ ⨟ ↑ geq

resolve : o ∈ Γ → ∙⟨ Γ ⟩ → o
resolve (here refl) (v , _)  = v
resolve (there x)   (_ , nv) = resolve x nv

eval : Expr Γ o → ∙⟨ Γ ⟩ → o
eval (`and e₁ e₂) nv = eval e₁ nv ∧ eval e₂ nv
eval (`or e₁ e₂)  nv = eval e₁ nv ∨ eval e₂ nv
eval (`neg e)     nv = not (eval e nv)
eval (`add e₁ e₂) nv = eval e₁ nv + eval e₂ nv
eval (`mul e₁ e₂) nv = eval e₁ nv * eval e₂ nv
eval (`leq e₁ e₂) nv = eval e₁ nv ≤ᵇ eval e₂ nv
eval (`geq e₁ e₂) nv = eval e₂ nv ≤ᵇ eval e₁ nv
eval (`var x)     nv = resolve x nv

commutes : (e : Expr Γ t) (nv : ∙⟨ Γ ⟩) → eval e nv ≡ ⟦ compile e ⟧ᶜ nv 
commutes (`and e₁ e₂)       nv       = cong₂ _∧_ (commutes e₁ nv) (commutes e₂ nv)
commutes (`or e₁ e₂)        nv       = cong₂ _∨_ (commutes e₁ nv) (commutes e₂ nv)
commutes (`neg e)           nv       = cong not (commutes e nv)
commutes (`add e₁ e₂)       nv       = cong₂ _+_ (commutes e₁ nv) (commutes e₂ nv)
commutes (`mul e₁ e₂)       nv       = cong₂ _*_ (commutes e₁ nv) (commutes e₂ nv)
commutes (`leq e₁ e₂)       nv       = cong₂ _≤ᵇ_ (commutes e₁ nv) (commutes e₂ nv)
commutes (`geq e₁ e₂)       nv       = cong₂ _≤ᵇ_ (commutes e₂ nv) (commutes e₁ nv)
commutes (`var (here refl))  _       = refl
commutes (`var (there x))   (_ , nv) = commutes (`var x) nv

