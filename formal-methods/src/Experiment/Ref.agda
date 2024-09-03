open import Data.Unit 
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All ; lookup ; _∷_ ; [] ; _[_]≔_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Product 

open import Relation.Binary.PropositionalEquality 

open import Function

module Experiment.Ref where

data Type : Set where
  unit : Type
  ref  : Type → Type
  fun  : (s t : Type) → Type 

variable s t : Type

Ctx = List Type
Sto = List Type

variable Γ : Ctx

-- Assume a fixed "shape" of the ledger.
--
-- For the purpose 
Ledger : Sto
Ledger = fun unit unit ∷ [] 

data Term (Γ : Ctx) : (t : Type) → Set where
  u      : Term Γ unit
  var    : t ∈ Γ → Term Γ t   
  abs    : Term (s ∷ Γ) t → Term Γ (fun s t)
  app    : Term Γ (fun s t) → Term Γ s → Term Γ t
  deref  : Term Γ (ref t) → Term Γ t  
  access : t ∈ Ledger → Term Γ (ref t)
  write  : Term Γ (ref t) → Term Γ t → Term Γ unit
  letin  : Term Γ s → Term (s ∷ Γ) t → Term Γ t 

module _ where 

  mutual
    record Closure (s t : Type) : Set where
      inductive
      constructor ⟨_,_⟩
      field
        {Γ′} : Ctx 
        γ′   : All ⟦_⟧ᵀ Γ′
        M′   : Term (s ∷ Γ′) t  

    ⟦_⟧ᵀ : Type → Set
    ⟦ unit    ⟧ᵀ = ⊤
    ⟦ ref t   ⟧ᵀ = t ∈ Ledger 
    ⟦ fun s t ⟧ᵀ = Closure s t 

Store = All ⟦_⟧ᵀ Ledger 

M : Set → Set
M A = Store → A × Store

variable A B : Set 

return : A → M A
return x s = x , s

_>>=_ : M A → (A → M B) → M B
(f >>= g) = uncurry g ∘ f

get : M Store
get s = s , s

put : Store → M ⊤
put s _ = tt , s

{-# TERMINATING #-} -- not really?
⟦_⟧ : Term Γ t → All ⟦_⟧ᵀ Γ → M ⟦ t ⟧ᵀ
⟦ u         ⟧ γ = return tt
⟦ var x     ⟧ γ = return (lookup γ x) 
⟦ abs M     ⟧ γ = return ⟨ γ , M ⟩
⟦ app M N   ⟧ γ = do
  ⟨ γ′ , M′ ⟩ ← ⟦ M ⟧ γ
  v           ← ⟦ N ⟧ γ 
  ⟦ M′ ⟧ (v ∷ γ′)  
⟦ deref M   ⟧ γ = do
  s ← get
  x ← ⟦ M ⟧ γ
  return (lookup s x) 
⟦ access x  ⟧ γ = return x 
⟦ write M N ⟧ γ = do
  x ← ⟦ M ⟧ γ
  v ← ⟦ N ⟧ γ
  s ← get
  put (s [ x ]≔ v)
⟦ letin M N ⟧ γ = do
  v ← ⟦ M ⟧ γ
  ⟦ N ⟧ (v ∷ γ)

postulate UNINITIALIZED : ∀ {A : Set} → A

l : Store 
l = UNINITIALIZED ∷ [] 

term₁ : Term [] unit
term₁ = app (abs (var (here refl))) u 

eval₁ : ⟦ term₁ ⟧ [] l .proj₁ ≡ tt
eval₁ = refl

term₂ : Term [] unit
term₂ = app (abs (app (var (here refl)) u)) (abs (var (here refl))) 

eval₂ : ⟦ term₂ ⟧ [] l .proj₁ ≡ tt
eval₂ = refl

term₃ : Term [] unit
term₃ =
  letin
    (write (access (here refl)) (abs (var (here refl))))
    (app (deref (access (here refl))) u) 

eval₃ : ⟦ term₃ ⟧ [] l .proj₁ ≡ tt
eval₃ = refl

-- l = { f : unit → unit } 
--
-- g : u → u = λ x → l.f x         
-- write l.f g               // now `g` invokes itself!
-- !g u                      // unfolds into infinite applications of `g`
-- 
bottom : Term [] unit
bottom =
  letin
    (write (access (here refl)) (abs (app (deref (access (here refl))) u)))
    (app (deref (access (here refl))) u)

{-

ledger {
  f: Cell[Circuit[Boolean,Boolean]]
}

circuit foo(): Boolean {
  f.write(circuit { x => f.read().call(x) });
  f.read().call(true);  
}

-} 

postulate
  -- diverges 
  eval₄ : ⟦ bottom ⟧ [] l .proj₁ ≡ tt
