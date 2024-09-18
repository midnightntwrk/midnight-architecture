{-# OPTIONS --allow-unsolved-metas --overlapping-instances #-} 

open import Data.Unit 
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Data.List hiding (lookup) renaming (map to lmap)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All ; lookup ; _∷_ ; [] ; _[_]≔_) renaming (map to amap)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Product 

open import Relation.Binary.PropositionalEquality 
open import Relation.Unary hiding (_∈_)

open import Util.Logic
open import Util.Ternary
open import Util.MonotonePredicate

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
  one : Type ℓ
  ref  : Type ℓ → Type ℓ
  fun  : (s : Type ℓ) → (t : Type ℓ) → Type (suc ℓ) 

variable s t : Type ℓ

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

Loc : Level → Set
Loc = Ctx 

variable Γ : Ctx ℓ 
         Λ Λ₁ Λ₂ Λ₃ Λ′ : Loc ℓ
instance level-rel₂ : HasRel₂ Level _
level-rel₂ = record { _≲_ = _≼_ } 



data _▹_∈′_ : ∀ ℓ → ◇ Type ℓ → Ctx ℓ → Set where

  ∈-current : t ∈ Γ .current
              -------------------
            → ℓ ▹ ◇⟨ ≼-≡ , t ⟩ ∈′ Γ

  ∈-next    : ∀ {px}
              → ℓ ▹ ◇⟨ px , t ⟩ ∈′ Γ .next ℓ refl
                ---------------------------------
              → suc ℓ ▹ ◇⟨ ≼-s ℓ px , t ⟩ ∈′ Γ 


insert : ◇ Type ℓ → Ctx ℓ → Ctx ℓ
insert ◇⟨ ≼-≡     , t ⟩ Γ = ⟪ t ∷ Γ .current , Γ .next ⟫
insert ◇⟨ ≼-s _ ι , t ⟩ Γ = ⟪ Γ .current , (λ where _ refl → insert ◇⟨ ι , t ⟩ (Γ .next _ refl)) ⟫
 
extend : ∀[ List ∘ ◇ Type ⇒ Ctx ⇒ Ctx ]
extend []        Γ = Γ
extend (◇t ∷ xs) Γ = extend xs (insert ◇t Γ)

↑ : ℓ₁ ≼ ℓ₂ → Type ℓ₁ → Type ℓ₂
↑ px         one       = one
↑ px         (ref t)   = ref (↑ px t)
↑ ≼-≡        (fun s t) = fun s t
↑ (≼-s m px) (fun s t) = fun (↑ (≼-suc _ _ px) s) (↑ (≼-suc _ _ px) t)

⇈ : ℓ₁ ≼ ℓ₂ → Ctx ℓ₁ → Ctx ℓ₂
⇈ ≼-≡ Γ = Γ
⇈ (≼-s _ px) Γ = ⟪ [] , (λ where _ refl → ⇈ px Γ) ⟫

↑ˢ : Type ℓ → Type (suc ℓ) 
↑ˢ = ↑ (≼-s _ ≼-≡)

⇈ˢ : Ctx ℓ → Ctx (suc ℓ)
⇈ˢ = ⇈ (≼-s _ ≼-≡)

⇊ : Ctx (suc ℓ) → Ctx ℓ
⇊ Γ = Γ .next _ refl 


record _⊑_ (Λ Λ′ : Loc ℓ) : Set where
  constructor ⊑⟨_,_⟩
  field
    diff : List (◇ Type ℓ)
    sep  : Λ′ ≡ extend diff Λ

open _⊑_ 


instance loc-rel₂ : HasRel₂ (Loc ℓ) _ 
HasRel₂._≲_ loc-rel₂ = _⊑_

-- ⊑-refl : Λ ⊑ Λ 
-- ⊑-refl = [] , refl

extend-++ : ∀ xs ys → extend ys (extend xs Λ) ≡ extend (xs ++ ys) Λ
extend-++ []       ys = refl
extend-++ (x ∷ xs) ys = extend-++ xs ys

loc-trans : Λ₁ ≲ Λ₂ → Λ₂ ≲ Λ₃ → Λ₁ ≲ Λ₃
loc-trans ⊑⟨ xs , refl ⟩ ⊑⟨ ys , refl ⟩ = ⊑⟨ xs ++ ys , extend-++ xs ys ⟩

restrict : (px : ℓ ≲ ℓ′) → Loc ℓ′ → Loc ℓ
restrict ≼-≡ Λ        = Λ
restrict (≼-s m px) Λ = restrict px (Λ .next _ refl)
-- 
-- fltr : List (◇ Type (suc ℓ)) → List (◇ Type ℓ)  
-- fltr []                      = []
-- fltr (◇⟨ ≼-≡     , t ⟩ ∷ xs) = fltr xs
-- fltr (◇⟨ ≼-s _ ι , t ⟩ ∷ xs) = ◇⟨ ι , t ⟩ ∷ fltr xs
-- 
-- fltr-lemma : ∀ {xs} → extend xs Λ .next ℓ refl ≡ extend (fltr xs) (Λ .next ℓ refl)
-- fltr-lemma {ℓ} {Λ} {[]}              = refl
-- fltr-lemma {ℓ} {Λ} {◇⟨ ≼-≡ , t ⟩ ∷ xs} = fltr-lemma {ℓ} {⟪ t ∷ Λ .current , Λ .next ⟫} {xs}
-- fltr-lemma {ℓ} {Λ} {◇⟨ ≼-s .ℓ ι , t ⟩ ∷ xs} rewrite (fltr-lemma {_} {Λ} {xs}) = {!!}
-- 
mutual 
  Store : Loc ℓ → Set
  Store {zero}  Λ = All (λ t → ⟦ t ⟧ᵀ Λ) (Λ .current)
  Store {suc ℓ} Λ = All (λ t → ⟦ t ⟧ᵀ Λ) (Λ .current) × Store (Λ .next ℓ refl)

  T : ∀ ℓ → (Loc ℓ → Set) → Loc ℓ → Set
  T _ P Λ = Store Λ → ∃ λ Λ′ → Store Λ′ × P Λ′ × Λ ≲ Λ′

  ⟦_⟧ᵀ : Type ℓ → Loc ℓ → Set
  ⟦ one     ⟧ᵀ    = U
  ⟦ ref t   ⟧ᵀ Λ = _ ▹ ◇⟨ ≼-refl , t ⟩ ∈′ Λ 
  ⟦ fun s t ⟧ᵀ Λ = □ (⟦ s ⟧ᵀ ⇒ T _ ⟦ t ⟧ᵀ) (Λ .next _ refl)

≼-≡-eq : ∀ (t : Type ℓ) → t ≡ ↑ ≼-≡ t
≼-≡-eq one      = refl
≼-≡-eq (ref t)   = cong ref (≼-≡-eq t)
≼-≡-eq (fun s t) = refl

record _⇿_ (A B : Set) : Set where 
  field
    to    : A → B
    from  : B → A

open _⇿_

return : ∀ {P : Loc ℓ → Set} → ∀[ P ⇒ T ℓ P ]
return px Σ = _ , Σ , px , ⊑⟨ [] , refl ⟩ 


_⋆ : ∀ {P Q : Loc ℓ → Set} → ∀[ P ⇒ T ℓ Q ] → ∀[ T ℓ P ⇒ T ℓ Q ]
(f ⋆) m Σ with m Σ
... | _ , Σ′ , px , sub = let _ , Σ′′ , qx , sub′ = f px Σ′ in _ , Σ′′ , qx , loc-trans sub sub′

_>>=_ : ∀ {P Q : Loc ℓ → Set} {Λ} → T ℓ P Λ → ∀[ P ⇒ T ℓ Q ] → T ℓ Q Λ 
(m >>= f) = (f ⋆) m

_>>_ : ∀ {P Q : Loc ℓ → Set} {Λ} → T ℓ P Λ → ∀[ T ℓ Q ] → T ℓ Q Λ
m >> n = m >>= λ _ → n

data _▹_⊢_ : ∀ ℓ → (Γ : Ctx ℓ) (t : Type ℓ) → Set where
 
  u      :   ------------
             ℓ ▹ Γ ⊢ one
  
  var    : ∀ {px}
           → ℓ ▹ ◇⟨ px , t ⟩ ∈′ Γ 
             ----------------------
           → ℓ′ ▹ restrict px Γ ⊢ t

  abs    : ∀ {s : Type ℓ′}
           → (px : ℓ′ ≲ ℓ) 
           → ℓ ▹ insert ◇⟨ px , s ⟩ (Γ .next ℓ refl) ⊢ t
             -------------------------------------------
           → suc ℓ ▹ Γ ⊢ fun (↑ px s) t
   
  app    :   suc ℓ ▹ Γ ⊢ fun s t → ℓ ▹ Γ .next _ refl ⊢ s
             --------------------------------------------
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
           → ℓ ▹ Γ ⊢ one   
     
  letin  :    ℓ ▹ Γ ⊢ s
           →  ℓ ▹ ⟪ s ∷ Γ .current , Γ .next ⟫  ⊢ t
              -------------------------------------
           →  ℓ ▹ Γ ⊢ t 

data Env : ∀ ℓ → (Γ : Ctx ℓ) → Loc ℓ → Set where
  ground : All (λ t → ⟦ t ⟧ᵀ Λ) (Γ .current) → Env 0 Γ Λ 
  level  : All (λ t → ⟦ t ⟧ᵀ Λ) (Γ .current) → Env ℓ (Γ .next _ refl) (Λ .next _ refl) → Env (suc ℓ) Γ Λ 

extend-env : (px : ℓ′ ≼ ℓ) → ⟦ t ⟧ᵀ (restrict px Λ) → Env ℓ Γ Λ → Env ℓ (insert ◇⟨ px , t ⟩ Γ) Λ
extend-env ≼-≡        v (ground pxs)  = ground (v ∷ pxs)
extend-env ≼-≡        v (level pxs γ) = level (v ∷ pxs) γ
extend-env (≼-s m px) v (level x γ)   = level x (extend-env px v γ)

_^_ : ∀ {P Q : Loc ℓ → Set} → ⦃ Monotone _ _≲_ Q ⦄ → ∀[ T ℓ P ⇒ Q ⇒ T ℓ (P ∩ Q) ]
(m ^ qx) Σ with m Σ
... | _ , Σ′ , px , sub = _ , Σ′ , (px , weaken sub qx) , sub


resolve : ∀ {px : ℓ′ ≼ ℓ } → ℓ ▹ ◇⟨ px , t ⟩ ∈′ Γ → ∀[ Env ℓ′ (restrict px Γ) ⇒ ⟦ t ⟧ᵀ ]
resolve {px = ≼-≡}      (∈-current x) (ground pxs)  = lookup pxs x
resolve {px = ≼-≡}      (∈-current x) (level pxs _) = lookup pxs x
resolve {px = ≼-s m px} (∈-next x) γ                = resolve x γ

trim : (px : ℓ′ ≼ ℓ) → Env ℓ Γ Λ → Env ℓ′ (restrict px Γ) (restrict px Λ)
trim ≼-≡        γ            = γ
trim (≼-s m px) (level _ γ′) = trim px γ′

trim-store : {Λ : Loc ℓ} → (ι : ℓ′ ≲ ℓ) → Store Λ → Store (restrict ι Λ) 
trim-store = {!!}

instance val-monotone : Monotone _ _≲_ ⟦ t ⟧ᵀ 
Monotone.weaken (val-monotone {t = one}) sub v = tt
Monotone.weaken (val-monotone {t = ref t}) sub x = {!!}
Monotone.weaken (val-monotone {t = fun t t₁}) sub f = necessary (λ ι v → (□⟨ f ⟩ loc-trans {!sub!} ι) v)

instance ◇-weaken : {P : Level → Set} → Monotone _ _≲_ (◇ P)
Monotone.weaken ◇-weaken ι′ ◇⟨ ι , px ⟩ = ◇⟨ ≼-trans ι ι′ , px ⟩

replace : (ι : ℓ′ ≲ ℓ) → Loc ℓ′ → Loc ℓ → Loc ℓ
replace ≼-≡       Λ′ Λ = Λ′
replace (≼-s m ι) Λ′ Λ = ⟪ Λ .current , (λ where _ refl → replace ι Λ′ (Λ .next _ refl)) ⟫



-- This witnesses that `extend` is a natural transformation in some sense
commute-extend : {Λ : Loc ℓ} (Λ′ : Loc ℓ′) → (ι : ℓ′ ≲ ℓ) → (xs : List (◇ Type ℓ′)) → replace ι (extend xs (restrict ι Λ)) Λ ≡ extend (lmap (Monotone.weaken ◇-weaken ι) xs) Λ
commute-extend Λ′ ≼-≡ xs = {!!}
commute-extend {Λ = Λ} Λ′ (≼-s m ι) [] =
  begin
    replace (≼-s m ι) (extend [] (restrict (≼-s m ι) Λ)) Λ
  ≡⟨⟩
    replace ((≼-s m ι)) (restrict ((≼-s m ι)) Λ) Λ
  ≡⟨ {!!} ⟩ 
    Λ 
  ≡⟨⟩
    extend [] Λ  
  ≡⟨⟩ 
    extend (lmap (Monotone.weaken ◇-weaken (≼-s m ι)) []) Λ
  ∎
  where
    open ≡-Reasoning
commute-extend {Λ = Λ} Λ′ (≼-s m ι) (x ∷ xs) = {!!}

update-store : (Λ′ : Loc ℓ′) (Λ : Loc ℓ) (ι : ℓ′ ≲ ℓ) → Store Λ′ → Store Λ → Store (replace ι Λ′ Λ)
update-store Λ′ Λ ≼-≡       ζ′ ζ        = ζ′
update-store Λ′ Λ (≼-s m ι) ζ′ (vs , ζ) = amap (weaken {!!}) vs , update-store Λ′ (Λ .next _ refl) ι ζ′ ζ

restrict-replace : ∀ (P : Loc ℓ′ → Set) Λ Λ′ → (ι : ℓ′ ≼ ℓ) → P Λ′ → P (restrict ι (replace ι Λ′ Λ)) 
restrict-replace P Λ Λ′ ≼-≡       px = px
restrict-replace P Λ Λ′ (≼-s m ι) px = restrict-replace P (Λ .next m refl) Λ′ ι px

embed : ∀ P Λ → (ι : ℓ′ ≲ ℓ) → T ℓ′ P (restrict ι Λ) → T ℓ (restrict ι ⊢ P) Λ
embed P Λ ι m ζ with m (trim-store ι ζ)
... | Λ′ , ζ′ , px , ⊑⟨ xs , refl ⟩
  = replace ι Λ′ Λ
  , update-store Λ′ Λ ι ζ′ ζ
  , restrict-replace P Λ Λ′ ι px
  , ⊑⟨ lmap (weaken ι) xs , commute-extend Λ′ ι xs ⟩


-- postulate instance env-monotone : Monotone _ _≲_ (Env ℓ Γ)

-- ⟦_⟧ : ℓ ▹ Γ ⊢ t → ∀[ Env ℓ Γ ⇒ T ℓ ⟦ t ⟧ᵀ ]

-- ⟦ u     ⟧ γ = return tt

-- ⟦ var x ⟧ γ = return (resolve x γ)

-- ⟦ abs px M ⟧ (level _ γ) = return (necessary λ ι v → ⟦ M ⟧ (extend-env {!!} {!v!} (weaken ι γ)))

-- ⟦ app M N ⟧ γ = do
--   (f , γ′) ← ⟦ M ⟧ γ ^ γ
--   v ← ((⟦ N ⟧ (trim (≼-s _ ≼-≡) γ′) ^ f) >>= λ (v , f′) → (□⟨ f′ ⟩ ([] , refl)) v) ‼
--   {!!} 

-- ⟦ ref M ⟧ γ = do
--   v ← ⟦ M ⟧ γ
--   {!!}

-- ⟦ deref M ⟧ γ = {!!}

-- ⟦ update M N ⟧ γ = {!!}

-- ⟦ letin M N ⟧ γ = do
--   (v₁ , γ′) ← ⟦ M ⟧ γ ^ γ
--   ⟦ N ⟧ (extend-env ≼-refl v₁ γ′)

-- -- -- (λ x . x) u : unit 
-- -- term₁ : suc ℓ ▹ ∅ᶜ ⊢ unit
-- -- term₁ = app ≼-≡ (abs ≼-≡ (var (∈-current (here refl)))) u

-- -- -- let r = ~(λ x . x) in !r u : unit  
-- -- term₂ : suc ℓ ▹ ∅ᶜ ⊢ unit
-- -- term₂ = letin (ref (abs ≼-≡ (var (∈-current (here refl))))) (app {!!} (deref (var (∈-current (here refl)))) u)


-- -- -- let r = ~(λ x . x) in r := (λ x . {- ?? -} ) ; r u
-- -- --
-- -- -- Impossible to construct, because:
-- -- --
-- -- -- 1. when constructing a closure, in the body we can only refer to variables
-- -- --    that are typed at a lower store level than the closure itself.
-- -- --
-- -- -- 2. When updating the reference r, the closure we intend to put there has a
-- -- --    body that is typed at a lower level than r itself. 
-- -- --
-- -- -- 3. Therefore, r is out of scope in the body, and we cannot construct Landin's
-- -- --    knot.
-- -- -- 
-- -- term₃ : suc ℓ ▹ ∅ᶜ ⊢ unit
-- -- term₃ {ℓ = ℓ} = letin (ref (abs {ℓ = ℓ} {s = unit} ≼-≡ (var (∈-current (here refl))))) (letin (update (var (∈-current (here refl))) (abs ≼-≡ {!!})) (app {!!} (deref {!!}) u)) 
