open import Data.Unit 
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All ; lookup ; _∷_ ; [] ; _[_]≔_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Product 

open import Relation.Binary.PropositionalEquality 
open import Relation.Unary hiding (_∈_)

open import Function

module Experiment.PredicativeRef where

Level = ℕ

variable ℓ ℓ₁ ℓ₂ ℓ′ : Level

data _≼_ n : (m : ℕ) → Set where 
  ≼-≡ : n ≼ n
  ≼-s : ∀ m → n ≼ m → n ≼ (suc m)

≼-suc : ∀ n m → suc n ≼ m → n ≼ m
≼-suc n .(suc n) ≼-≡ = ≼-s n ≼-≡
≼-suc n .(suc m) (≼-s m px) = ≼-s m (≼-suc n m px)

≼-refl : ∀ {n} → n ≼ n
≼-refl = ≼-≡

≼-trans : ∀ {n m k} → n ≼ m → m ≼ k → n ≼ k
≼-trans ≼-≡ px₂ = px₂
≼-trans (≼-s m px₁) px₂ = ≼-trans px₁ (≼-suc _ _ px₂)

data Type : Level → Set where
  unit : Type ℓ
  ref  : Type ℓ → Type ℓ
  fun  : (px : ℓ′ ≼ ℓ) → (s : Type ℓ′) → (t : Type ℓ) → Type (suc ℓ) 

variable s t : Type ℓ


◇ : (Level → Set) → (Level → Set)
◇ P ℓ = ∃[ ℓ′ ] (P ℓ′ × ℓ′ ≼ ℓ)

record Ctx ℓ : Set where
  inductive
  pattern 
  constructor ⟪_,_⟫ 
  field
    current : List (Type ℓ)
    next    : ∀ ℓ′ → ℓ ≡ suc ℓ′ → Ctx ℓ′ 

open Ctx

∅ᶜ : Ctx ℓ
∅ᶜ {zero} = ⟪ [] , (λ _ ()) ⟫
∅ᶜ {suc ℓ} = ⟪ [] , (λ where _ refl → ∅ᶜ) ⟫
-- 
-- data Loc : ∀ ℓ → Set where
--   ε   : Loc 0
--   _∙_ : List (Type (suc ℓ)) → Loc ℓ → Loc (suc ℓ)
-- 

Loc : Level → Set
Loc = Ctx 

variable Γ : Ctx ℓ 
         Λ Λ₁ Λ₂ Λ₃ Λ′ : Loc ℓ


data _▹_∈′_ : ∀ ℓ → ◇ Type ℓ → Ctx ℓ → Set where

  ∈-current : t ∈ Γ .current
              --------------------
            → ℓ ▹ ℓ , t , ≼-≡ ∈′ Γ

  ∈-next    : ∀ {px}
              → ℓ ▹ ℓ′ , t , px ∈′ Γ .next ℓ refl
                ----------------------------------
              → suc ℓ ▹ ℓ′ , (t , (≼-s ℓ px)) ∈′ Γ 


insert : ◇ Type ℓ → Ctx ℓ → Ctx ℓ
insert (_ , t , ≼-≡)      Γ = ⟪ t ∷ Γ .current , Γ .next ⟫
insert (_ , t , ≼-s m px) Γ =
  ⟪ Γ .current
  , (λ where _ refl → insert (_ , t , px) (Γ .next _ refl))
  ⟫

extend : ∀[ List ∘ ◇ Type ⇒ Ctx ⇒ Ctx ]
extend []        Γ = Γ
extend (◇t ∷ xs) Γ = extend xs (insert ◇t Γ)

↑ : ℓ₁ ≼ ℓ₂ → Type ℓ₁ → Type ℓ₂
↑ px         unit          = unit
↑ px         (ref t)       = ref (↑ px t)
↑ ≼-≡        (fun px′ s t) = fun px′ s t
↑ (≼-s m px) (fun px′ s t) = fun (≼-trans (≼-s _ px′) px) s (↑ (≼-suc _ _ px) t)


⇈ : ℓ₁ ≼ ℓ₂ → Ctx ℓ₁ → Ctx ℓ₂
⇈ ≼-≡ Γ = Γ
⇈ (≼-s _ px) Γ = ⟪ [] , (λ where _ refl → ⇈ px Γ) ⟫

↑ˢ : Type ℓ → Type (suc ℓ) 
↑ˢ = ↑ (≼-s _ ≼-≡)

⇈ˢ : Ctx ℓ → Ctx (suc ℓ)
⇈ˢ = ⇈ (≼-s _ ≼-≡)

⇊ : Ctx (suc ℓ) → Ctx ℓ
⇊ Γ = Γ .next _ refl 

_⊑_ : Loc ℓ → Loc ℓ → Set
Λ₁ ⊑ Λ₂ = ∃[ xs ] Λ₂ ≡ extend xs Λ₁ 

⊑-refl : Λ ⊑ Λ 
⊑-refl = [] , refl

postulate ⊑-trans : Λ₁ ⊑ Λ₂ → Λ₂ ⊑ Λ₃ → Λ₁ ⊑ Λ₃

record Monotone (P : Loc ℓ → Set) : Set where
  field
    weaken : Λ₁ ⊑ Λ₂ → P Λ₁ → P Λ₂

open Monotone ⦃...⦄

◆ : (Loc ℓ → Set) → Loc ℓ → Set
◆ P Λ = ∃[ Λ′ ] (P Λ′ × Λ ⊑ Λ′) 

restrict : (px : ℓ ≼ ℓ′) → Loc ℓ′ → Loc ℓ
restrict ≼-≡ Λ        = Λ
restrict (≼-s m px) Λ = restrict px (Λ .next _ refl)

mutual 
  Store : Loc ℓ → Set
  Store {zero}  Λ = All (λ t → ⟦ t ⟧ᵀ Λ) (Λ .current)
  Store {suc ℓ} Λ = All (λ t → ⟦ t ⟧ᵀ Λ) (Λ .current) × Store (Λ .next ℓ refl)

  M : (Loc ℓ → Set) → Loc ℓ → Set
  M P = Store ⇒ ◆ (P ∩ Store)

  ⟦_⟧ᵀ : Type ℓ → Loc ℓ → Set
  ⟦ unit       ⟧ᵀ   = U
  ⟦ ref t      ⟧ᵀ Λ = _ ▹ _ , t , ≼-≡ ∈′ Λ 
  ⟦ fun px s t ⟧ᵀ Λ = ⟦ ↑ px s ⟧ᵀ (Λ .next _ refl) → M ⟦ t ⟧ᵀ (Λ .next _ refl)  

≼-≡-eq : ∀ (t : Type ℓ) → t ≡ ↑ ≼-≡ t
≼-≡-eq unit      = refl
≼-≡-eq (ref t)   = cong ref (≼-≡-eq t)
≼-≡-eq (fun px s t) = refl

record _⇿_ (A B : Set) : Set where 
  field
    to    : A → B
    from  : B → A

open _⇿_


return : ∀ {P : Loc ℓ → Set} → ∀[ P ⇒ M P ]
return px Σ = _ , (px , Σ) , ⊑-refl 

_⋆ : ∀ {P Q : Loc ℓ → Set} → ∀[ P ⇒ M Q ] → ∀[ M P ⇒ M Q ]
(f ⋆) m Σ with m Σ
... | _ , (px , Σ′) , sub = let (ℓ , (qx , Σ′′) , sub′) = f px Σ′ in ℓ , ((qx , Σ′′) , ⊑-trans sub sub′)

_>>=_ : ∀ {P Q : Loc ℓ → Set} {Λ} → M P Λ → ∀[ P ⇒ M Q ] →  M Q Λ 
(m >>= f) = (f ⋆) m

_>>_ : ∀ {P Q : Loc ℓ → Set} {Λ} → M P Λ → ∀[ M Q ] → M Q Λ
m >> n = m >>= λ _ → n

data _▹_⊢_ : ∀ ℓ → (Γ : Ctx ℓ) (t : Type ℓ) → Set where
 
  u      :   ------------
             ℓ ▹ Γ ⊢ unit
  
  var    : ∀ {px}
           → ℓ ▹ ℓ′ , t , px ∈′ Γ 
             ----------------------
           → ℓ′ ▹ restrict px Γ ⊢ t

  abs    : ∀ {s : Type ℓ′} 
           → (px : ℓ′ ≼ ℓ) 
           → ℓ ▹ insert (ℓ′ , s , px) (Γ .next ℓ refl) ⊢ t
             ---------------------------------------------
           → suc ℓ ▹ Γ ⊢ fun px s t
   
  app    : ∀ (px : ℓ′ ≼ ℓ) 
           → suc ℓ ▹ Γ ⊢ fun px s t → ℓ′ ▹ restrict px (Γ .next ℓ refl) ⊢ s
             --------------------------------------------------------------
           → suc ℓ ▹ Γ ⊢ ↑ˢ t

  ref    :   ℓ ▹ Γ ⊢ t
             -------------
           → ℓ ▹ Γ ⊢ ref t

  deref  :   ℓ ▹ Γ ⊢ ref t
             -------------
           → ℓ ▹ Γ ⊢ t  

  update : ∀ {t : Type ℓ}
           → ℓ ▹ Γ ⊢ ref t
           → ℓ ▹ Γ ⊢ t
             -------------
           → ℓ ▹ Γ ⊢ unit   
     
  letin  :    ℓ ▹ Γ ⊢ s
           →  ℓ ▹ ⟪ s ∷ Γ .current , Γ .next ⟫  ⊢ t
              -------------------------------------
           →  ℓ ▹ Γ ⊢ t 

data Env : ∀ ℓ → (Γ : Ctx ℓ) → Loc ℓ → Set where
  ground : All (λ t → ⟦ t ⟧ᵀ Λ) (Γ .current) → Env 0 Γ Λ 
  level  : All (λ t → ⟦ t ⟧ᵀ Λ) (Γ .current) → Env ℓ (Γ .next _ refl) (Λ .next _ refl) → Env (suc ℓ) Γ Λ 

extend-env : (px : ℓ′ ≼ ℓ) → ⟦ t ⟧ᵀ (restrict px Λ) → Env ℓ Γ Λ → Env ℓ (insert (ℓ′ , t , px) Γ) Λ
extend-env ≼-≡        v (ground pxs)  = ground (v ∷ pxs)
extend-env ≼-≡        v (level pxs γ) = level (v ∷ pxs) γ
extend-env (≼-s m px) v (level x γ)   = level x (extend-env px v γ)

_^_ : ∀ {P Q : Loc ℓ → Set} → ⦃ Monotone Q ⦄ → ∀[ M P ⇒ Q ⇒ M (P ∩ Q) ]
(m ^ qx) Σ with m Σ
... | Λ′ , (px , Σ′) , sub = Λ′ , ((px , weaken sub qx) , Σ′) , sub

resolve : ∀ {px : ℓ′ ≼ ℓ } → ℓ ▹ _ , t , px ∈′ Γ → ∀[ Env ℓ′ (restrict px Γ) ⇒ ⟦ t ⟧ᵀ ]
resolve {px = ≼-≡}      (∈-current x) (ground pxs)  = lookup pxs x
resolve {px = ≼-≡}      (∈-current x) (level pxs _) = lookup pxs x
resolve {px = ≼-s m px} (∈-next x) γ                = resolve x γ

trim : (px : ℓ′ ≼ ℓ) → Env ℓ Γ Λ → Env ℓ′ (restrict px Γ) (restrict px Λ)
trim ≼-≡ γ = γ
trim (≼-s m px) (level _ γ′) = trim px γ′

postulate instance env-monotone : Monotone (Env ℓ Γ)

⟦_⟧ : ℓ ▹ Γ ⊢ t → ∀[ Env ℓ Γ ⇒ M ⟦ t ⟧ᵀ ]

⟦ u     ⟧ γ = return tt

⟦ var x ⟧ γ = return (resolve x γ)

⟦ abs px M ⟧ (level _ γ) = return λ v → ⟦ M ⟧ (extend-env _ {!v!} γ)

⟦ app px M N ⟧ γ = do
  (v₁ , level pxs γ′) ← ⟦ M ⟧ γ ^ γ
  let foo = ⟦ N ⟧ (trim px γ′) 
  {!foo!} 

⟦ ref M ⟧ γ = {!!}

⟦ deref M ⟧ γ = {!!}

⟦ update M N ⟧ γ = {!!}

⟦ letin M N ⟧ γ = do
  (v₁ , γ′) ← ⟦ M ⟧ γ ^ γ
  ⟦ N ⟧ (extend-env ≼-refl v₁ γ′)

-- (λ x . x) u : unit 
term₁ : suc ℓ ▹ ∅ᶜ ⊢ unit
term₁ = app ≼-≡ (abs ≼-≡ (var (∈-current (here refl)))) u

-- let r = ~(λ x . x) in !r u : unit  
term₂ : suc ℓ ▹ ∅ᶜ ⊢ unit
term₂ = letin (ref (abs ≼-≡ (var (∈-current (here refl))))) (app {!!} (deref (var (∈-current (here refl)))) u)


-- let r = ~(λ x . x) in r := (λ x . {- ?? -} ) ; r u
--
-- Impossible to construct, because:
--
-- 1. when constructing a closure, in the body we can only refer to variables
--    that are typed at a lower store level than the closure itself.
--
-- 2. When updating the reference r, the closure we intend to put there has a
--    body that is typed at a lower level than r itself. 
--
-- 3. Therefore, r is out of scope in the body, and we cannot construct Landin's
--    knot.
-- 
term₃ : suc ℓ ▹ ∅ᶜ ⊢ unit
term₃ {ℓ = ℓ} = letin (ref (abs {ℓ = ℓ} {s = unit} ≼-≡ (var (∈-current (here refl))))) (letin (update (var (∈-current (here refl))) (abs ≼-≡ {!!})) (app {!!} (deref {!!}) u)) 
