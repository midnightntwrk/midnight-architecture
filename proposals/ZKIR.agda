open import Data.Nat 
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)

open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All renaming (map to mapᴬ ; lookup to lookupᴬ) 
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Empty
open import Relation.Unary hiding (_∈_ ; _⇒_ ; ∅)
open import Data.Bool using (Bool ; true ; false; if_then_else_)
open import Data.Sum renaming ([_,_] to ⊎[_,_])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Function using (_∘_)
open import Data.Maybe 
open import Data.Vec using (Vec)

open import Prelude.InferenceRules

module ZKIR where

data Kind : Set where
  ★ 𝕗 𝕔 : Kind -- type, field, curve 

TCtx = List Kind 

data StandaloneField : Set where 

data FieldType : Set where
  base scalar : FieldType 

data Curve (Δ : TCtx) : Set where
  native-curve bls12-381 jubjub secp256k1 : Curve Δ
  cvar : 𝕔 ∈ Δ → Curve Δ

data Field (Δ : TCtx) : Set where
  native-field : Field Δ
  _·_  : Curve Δ → FieldType → Field Δ
  fvar : 𝕗 ∈ Δ → Field Δ 

data Type (Δ : TCtx) : Set where
  el  : Field Δ → Type Δ
  bit byte biguint : Type Δ
  point : Curve Δ → Type Δ
  vector : Type Δ → Type Δ
  tvar : ★ ∈ Δ → Type Δ

data Constraint (Δ : TCtx) : Set where
  Assign Assert Eq Arith : Type Δ → Constraint Δ 

data Mode : Set where
  const wire pub priv : Mode

data Input (Δ : TCtx) : Set where
  _⦂[_] : Mode → Type Δ → Input Δ
  pair  : (l r : Input Δ) → Input Δ
  &[_]  : Input Δ → Input Δ
  _⁇    : Input Δ → Input Δ

data Qualified (Δ : TCtx) : Set where
  _↠_ : List (Input Δ) → List (Type Δ) → Qualified Δ
  _⇒_ : Constraint Δ → Qualified Δ → Qualified Δ

⟦_⟧kind : Kind → TCtx → Set
⟦ ★ ⟧kind = Type
⟦ 𝕗 ⟧kind = Field
⟦ 𝕔 ⟧kind = Curve

Substitution : (Δ₁ Δ₂ : TCtx) → Set
Substitution Δ₁ Δ₂ = ∀ k → k ∈ Δ₁ → ⟦ k ⟧kind Δ₂

data Signature (Δ : TCtx) : Set where
  ∀⟨_⟩_ : (k : Kind) → Signature (k ∷ Δ) → Signature Δ
  qualified : Qualified Δ → Signature Δ 
  


data Context : Set where
  ∅   : Context
  _,_ : Type [] → Context → Context

variable
  Δ Δ₁ Δ₂ Δ₃ Δ′ : TCtx 
  T T₁ T₂ T₃ T′ : Type Δ
  ρ ρ₁ ρ₂ ρ₃ ρ′ : Qualified Δ
  Σ Σ₁ Σ₂ Σ₃ Σ′ : Signature Δ 

var : ∀ {k} → k ∈ Δ → ⟦ k ⟧kind Δ
var {k = ★} x = tvar x
var {k = 𝕗} x = fvar x
var {k = 𝕔} x = cvar x

ext-subst : ∀ {k} → Substitution Δ₁ Δ₂ → Substitution (k ∷ Δ₁) (k ∷ Δ₂)
ext-subst σ k (here refl) = var (here refl)
ext-subst σ k (there x) = {!!} -- requires renaming 

subst-curve : Substitution Δ₁ Δ₂ → Curve Δ₁ → Curve Δ₂ 
subst-curve σ native-curve = native-curve
subst-curve σ bls12-381 = bls12-381
subst-curve σ jubjub = jubjub
subst-curve σ secp256k1 = secp256k1
subst-curve σ (cvar x) = σ _ x

subst-field : Substitution Δ₁ Δ₂ → Field Δ₁ → Field Δ₂
subst-field σ native-field = native-field
subst-field σ (c · ftype) = subst-curve σ c · ftype
subst-field σ (fvar x) = σ _ x

subst-type : Substitution Δ₁ Δ₂ → Type Δ₁ → Type Δ₂
subst-type σ (el x) = el (subst-field σ x)
subst-type σ bit = bit
subst-type σ byte = byte
subst-type σ biguint = biguint
subst-type σ (point x) = point (subst-curve σ x)
subst-type σ (vector T) = vector (subst-type σ T)
subst-type σ (tvar x) = σ _ x

subst-constraint : Substitution Δ₁ Δ₂ → Constraint Δ₁ → Constraint Δ₂
subst-constraint σ (Assign T) = Assign (subst-type σ T)
subst-constraint σ (Assert T) = Assert ((subst-type σ T))
subst-constraint σ (Eq T)     = Eq ((subst-type σ T))
subst-constraint σ (Arith T)  = Arith ((subst-type σ T))

subst-input : Substitution Δ₁ Δ₂ → Input Δ₁ → Input Δ₂
subst-input σ (m ⦂[ T ]) = m ⦂[ subst-type σ T ]
subst-input σ (pair ι₁ ι₂) = pair (subst-input σ ι₁) (subst-input σ ι₂)
subst-input σ &[ ι ] = &[ subst-input σ ι ]
subst-input σ (ι ⁇) = subst-input σ ι ⁇

subst-qualified : Substitution Δ₁ Δ₂ → Qualified Δ₁ → Qualified Δ₂
subst-qualified σ (ι∗ ↠ T∗) = Data.List.map (subst-input σ) ι∗ ↠ Data.List.map (subst-type σ) T∗
subst-qualified σ (C ⇒ ρ) = subst-constraint σ C ⇒ subst-qualified σ ρ

subst-signature : Substitution Δ₁ Δ₂ → Signature Δ₁ → Signature Δ₂
subst-signature σ (∀⟨ k ⟩ Σ) = ∀⟨ k ⟩ subst-signature (ext-subst σ ) Σ
subst-signature σ (qualified ρ) = qualified (subst-qualified σ ρ)

Gates : Set
Gates = List (Signature []) 

PredicateWitnesses : Set
PredicateWitnesses = List (Constraint [])

_⊩_ : PredicateWitnesses → Constraint [] → Set 
𝓟 ⊩ C = C ∈ 𝓟 

PrivateInputs : Set
PrivateInputs = List (Type [])

PublicInputs : Set
PublicInputs = List (Type [])

Constants : Set₁
Constants = Type [] → Set 

-- The type of "memory shapes": a static representation of the
-- possible ways a program's memory could evolve during execution.
--
-- This is the free semiring over closed types. 
data Mem : Set where
  𝟘 𝟙 : Mem
  _⊗_ _⊕_ : (μ₁ μ₂ : Mem) → Mem
  ⟪_⟫ : Type [] → Mem

⟪_⟫∗ : List (Type []) → Mem
⟪ [] ⟫∗ = 𝟙
⟪ T ∷ T∗ ⟫∗ = ⟪ T ⟫ ⊗ ⟪ T∗ ⟫∗

variable
  μ μ₁ μ₂ μ₃ μ′ : Mem
  ι ι₁ ι₂ ι₃ ι′ : Input Δ
  C C₁ C₂ C₃ C′ : Constraint Δ 
  ι∗ : List (Input Δ)
  T∗ : List (Type Δ)
  

wires⟨_⟩ : Mem → List (Type [])
wires⟨ 𝟘       ⟩ = []
wires⟨ 𝟙       ⟩ = []
wires⟨ μ₁ ⊗ μ₂ ⟩ = wires⟨ μ₁ ⟩ ++ wires⟨ μ₂ ⟩ 
wires⟨ μ₁ ⊕ μ₂ ⟩ = []
wires⟨ ⟪ T ⟫   ⟩ = [ T ]

[/_] : ∀ {k} → ⟦ k ⟧kind Δ → Substitution (k ∷ Δ) Δ
[/ v ] k (here refl) = v
[/ v ] k (there x) = var x

data _⊩_←inst⟨_⟩q (P : PredicateWitnesses) : List (Input []) × List (Type []) → Qualified [] → Set where 

  base
    : ───────────────────────────────
      P ⊩ (ι∗ , T∗) ←inst⟨ ι∗ ↠ T∗ ⟩q

  discharge-constraint
    : P ⊩ (ι∗ , T∗) ←inst⟨ ρ ⟩q
    ∙ (P ⊩ C)
      ─────────────────────────────
      P ⊩ (ι∗ , T∗) ←inst⟨ C ⇒ ρ ⟩q
    


data _⊩_←inst⟨_⟩ (𝓟 : PredicateWitnesses) : List (Input []) × List (Type []) → Signature [] → Set where

  inst-universal
    : ∀ {k} {Σ}
    → (v : ⟦ k ⟧kind [])
    → 𝓟 ⊩ (ι∗ , T∗) ←inst⟨ subst-signature [/ v ] Σ ⟩
      ───────────────────────────────────────────────
      𝓟 ⊩ (ι∗ , T∗) ←inst⟨ ∀⟨ k ⟩ Σ ⟩

  inst-qualified
    : 𝓟 ⊩ (ι∗ , T∗) ←inst⟨ ρ ⟩q
      ──────────────────────────────────
      𝓟 ⊩ (ι∗ , T∗) ←inst⟨ qualified ρ ⟩  

module Typing
  (𝓖 : Gates)
  (𝓟 : PredicateWitnesses)
  (Π : PrivateInputs)
  (Ψ : PublicInputs)
  (K : Constants) where 
  
  mutual 

    data _⊢i_ (μ : Mem) : (ι : Input []) → Set where
    
      nil
        : ──────────
          μ ⊢i (ι ⁇)
        
      val
        : μ ⊢i ι
          ──────────
          μ ⊢i (ι ⁇)

      pair
        : μ ⊢i ι₁
        ∙ μ ⊢i ι₂
          ───────────────
          μ ⊢i pair ι₁ ι₂

      slice
        : List (μ ⊢i ι)
          ─────────────
          μ ⊢i &[ ι ]

      constant
        : K T
          ───────────────────
          μ ⊢i (const ⦂[ T ])

      priv
        : T ∈ Π
          ──────────────────
          μ ⊢i (priv ⦂[ T ])
  
      pub
        : T ∈ Ψ
          ─────────────────
          μ ⊢i (pub ⦂[ T ])

      wire
        : T ∈ wires⟨ μ ⟩
          ──────────────────
          μ ⊢i (wire ⦂[ T ]) 
  
  
    data _≫ᴵ_ (μ : Mem) : (μ′ : Mem) → Set where
  
      branch
        : bit ∈ wires⟨ μ ⟩
        ∙ μ ≫ᶜ μ₁
        ∙ μ ≫ᶜ μ₂
        ∙ μ₁ ∥ μ₂ ≫ μ′
          ─────────────────────
          μ ≫ᴵ ((μ₁ ⊕ μ₂) ⊗ μ′)
  
      gate
        : Σ ∈ 𝓖
        ∙ 𝓟 ⊩ (ι∗ , T∗) ←inst⟨ Σ ⟩
        ∙ All (μ ⊢i_) ι∗ 
          ───────────────────────
          μ ≫ᴵ ⟪ T∗ ⟫∗
  
  
    data _∥_≫_ (μ₁ μ₂ : Mem) : (μ : Mem) → Set where
    
      nil
        : ───────────
          μ₁ ∥ μ₂ ≫ 𝟙
  
      phi
        : T ∈ wires⟨ μ₁ ⟩
        ∙ T ∈ wires⟨ μ₂ ⟩
        ∙ μ₁ ∥ μ₂ ≫ μ′
          ──────────────────────
          μ₁ ∥ μ₂ ≫ (⟪ T ⟫ ⊗ μ′)
  
  
    data _≫ᶜ_ (μ : Mem) : (μ′ : Mem) → Set where
    
      nil
        : ───────
          μ ≫ᶜ 𝟙
  
  
      seq
        : μ ≫ᴵ μ₁
        ∙ (μ ⊗ μ₁) ≫ᶜ μ₂
          ───────────────
           μ ≫ᶜ (μ₁ ⊗ μ₂)
  

{-
  "Intuitionistic" zero-knowledge proofs, using proof irrelevance.
-} 

module ZK (X : Set) (W : Set) (R : X → W → Set) where

  record Proof (x : X) : Set₁ where
    constructor ‼_  
    field
      {w}   : W      -- Make irrelevant for pedagogical illustration
                     -- of ZK proofs. In practice annoying to work
                     -- with
      proof : R x w  


  prove : (x : X) (w : W) → R x w → Proof x
  prove _ _ p = ‼ p
  
  verify : (x : X) → Proof x → Set
  verify x (‼ proof) = ⊤ -- constructively true, once we see the proof. 

{-

The "zero knowledge" property of proofs in this setting exists as a
meta-theoretical property of Agda's erasure (and maybe parametricity).

Parametricity tells us there is no general procedure for conjuring
witnesses from nothing (though in specific cases for specific relations it may be possible).

Erasure tells us that we cannot use the witness value stored in the
proof here; it is marked as irrelevant.

Hence there is no way to get a witness matching the proof. 

-} 
module _ where 

  open ZK 

  extract : ∀ X W R → (x : X) → Proof X W R x → ∃ λ w → R x w 
  extract _ _ _ _ (‼ proof) = {!!} , proof




⟦_⟧type : Type [] → Set
⟦ el _ ⟧type = ℕ
⟦ bit ⟧type = Bool
⟦ byte ⟧type = Vec Bool 8
⟦ biguint ⟧type = ℕ
⟦ point x ⟧type = ℕ × ℕ
⟦ vector T ⟧type = List ⟦ T ⟧type

⟦_⟧input : Input [] → Set
⟦ mode ⦂[ T ] ⟧input = ⟦ T ⟧type
⟦ pair ι₁ ι₂ ⟧input = ⟦ ι₁ ⟧input × ⟦ ι₂ ⟧input
⟦ &[ ι ] ⟧input = List ⟦ ι ⟧input
⟦ ι ⁇ ⟧input = Maybe ⟦ ι ⟧input

{- Semantics of ZKIR -} 

module Semantics 
  (𝓖 : Gates)
  (𝓟 : PredicateWitnesses)

  -- All gates have a relational semantics, with positions in the
  -- logical relation corresponding to the gate's inputs and outputs.
  ( ⟦_∙_⟧gateᴿ
        : ∀ {Σ ι∗ T∗}
        → Σ ∈ 𝓖 → 𝓟 ⊩ (ι∗ , T∗) ←inst⟨ Σ ⟩
        → All ⟦_⟧input ι∗ → All ⟦_⟧type T∗ → Set )

  -- All gates have a computational semantics, with the functions in-
  -- and outputs corresponding to the inputs and outputs of the gate.
  ( ⟦_∙_⟧gateᶠ
        : ∀ {Σ ι∗ T∗}
        → Σ ∈ 𝓖 → 𝓟 ⊩ (ι∗ , T∗) ←inst⟨ Σ ⟩
        → All ⟦_⟧input ι∗ → All ⟦_⟧type T∗ ) 
  where

  data Memory : Mem → Set where
    nil : Memory 𝟙
    cell : ⟦ T ⟧type → Memory ⟪ T ⟫
    _⊗ᴹ_ : Memory μ₁ → Memory μ₂ → Memory (μ₁ ⊗ μ₂)
    _⊕ᴹ_ : Memory μ₁ → Memory μ₂ → Memory (μ₁ ⊕ μ₂) 


  project-wires : Memory μ → All ⟦_⟧type wires⟨ μ ⟩ 
  project-wires nil = []
  project-wires (cell x) = x ∷ []
  project-wires (M₁ ⊗ᴹ M₂) = ++⁺ (project-wires M₁) (project-wires M₂)
  project-wires (M₁ ⊕ᴹ M₂) = []

  resolve : T ∈ wires⟨ μ ⟩ → Memory μ → ⟦ T ⟧type 
  resolve {μ = μ} x M = Data.List.Relation.Unary.All.lookup (project-wires {μ} M) x 

  module RelationalSemantics
    {Π : PrivateInputs}
    {Ψ : PublicInputs}
    (π : All ⟦_⟧type Π)
    (ψ : All ⟦_⟧type Ψ)
    where
    
    open Typing 𝓖 𝓟 Π Ψ ⟦_⟧type

    flatten : Memory ⟪ T∗ ⟫∗ → All ⟦_⟧type T∗
    flatten {[]} nil = []
    flatten {T ∷ T∗} (cell v ⊗ᴹ M) = v ∷ flatten M

    mutual 
      ⟦_⟧ : μ ≫ᶜ μ′ → Pred (Memory (μ ⊗ μ′)) _
      ⟦ nil ⟧ = U
    
      ⟦ seq (I , Ω) ⟧ (M₁ ⊗ᴹ (M₂ ⊗ᴹ M₃))
        = ⟦ I ⟧instr (M₁ ⊗ᴹ M₂) × ⟦ Ω ⟧ ((M₁ ⊗ᴹ M₂) ⊗ᴹ M₃)

      ⟦_⟧instr : μ ≫ᴵ μ′ → Pred (Memory (μ ⊗ μ′)) _  
      ⟦ branch (c , Ω₁ , Ω₂ , φ∗) ⟧instr (M ⊗ᴹ ((M₁ ⊕ᴹ M₂) ⊗ᴹ M′))
        = ⟦ Ω₁ ⟧ (M ⊗ᴹ M₁)
        × ⟦ Ω₂ ⟧ (M ⊗ᴹ M₂)
        × ( resolve c M ≡ true  × ⟦ φ∗ ⟧φ (inj₁ M₁ , M′)
          ⊎ resolve c M ≡ false × ⟦ φ∗ ⟧φ (inj₂ M₂ , M′))
      ⟦ gate (g , inst , args) ⟧instr (M ⊗ᴹ M′) =
        let
          Rᵍ = ⟦ g ∙ inst ⟧gateᴿ
        in
          Rᵍ (mapᴬ (λ a → ⟦ a ⟧arg M) args) (flatten M′)

      ⟦_⟧arg : μ ⊢i ι → Memory μ → ⟦ ι ⟧input
      ⟦ nil ⟧arg M
        = nothing
      ⟦ val a ⟧arg M
        = just (⟦ a ⟧arg M)
      ⟦ pair (a₁ , a₂) ⟧arg M
        = ⟦ a₁ ⟧arg M , ⟦ a₂ ⟧arg M
      ⟦ slice as ⟧arg M
        = ⟦ as ⟧args M
      ⟦ constant v ⟧arg M
        = v
      ⟦ priv x ⟧arg M
        = lookupᴬ π x
      ⟦ pub x ⟧arg M
        = lookupᴬ ψ x
      ⟦ wire x ⟧arg M
        = resolve x M

      ⟦_⟧args : List (μ ⊢i ι) → Memory μ → List ⟦ ι ⟧input 
      ⟦ [] ⟧args M
        = []
      ⟦ a ∷ xs ⟧args M
        = ⟦ a ⟧arg M ∷ ⟦ xs ⟧args M

      ⟦_⟧φ : μ₁ ∥ μ₂ ≫ μ′ → Pred ((Memory μ₁ ⊎ Memory μ₂) × Memory μ′) _
      ⟦ Typing.nil ⟧φ = U
      ⟦ Typing.phi (x₁ , x₂ , φ∗) ⟧φ (M , (cell v ⊗ᴹ M′))
        = ⊎[ (_≡ v) ∘ resolve x₁
          , (_≡ v) ∘ resolve x₂
          ] M
        × ⟦ φ∗ ⟧φ (M , M′) 

  module ComputationalSemantics
    {Π : PrivateInputs}
    {Ψ : PublicInputs}
    (π : All ⟦_⟧type Π)
    (ψ : All ⟦_⟧type Ψ)
    where

    open Typing 𝓖 𝓟 Π Ψ ⟦_⟧type

    lift-mem : All ⟦_⟧type T∗ → Memory ⟪ T∗ ⟫∗
    lift-mem [] = nil
    lift-mem (px ∷ xs) = (cell px) ⊗ᴹ (lift-mem xs)

    mutual
      ⟦_⟧ : μ ≫ᶜ μ′ → Memory μ → Memory μ′
      ⟦ nil ⟧ M = nil
      ⟦ seq (I , Ω) ⟧ M
        = let
            M′ = ⟦ I ⟧instr M
          in
            M′ ⊗ᴹ ⟦ Ω ⟧ (M ⊗ᴹ M′)

      ⟦_⟧instr : μ ≫ᴵ μ′ → Memory μ → Memory μ′ 
      ⟦ branch (x , Ω₁ , Ω₂ , joins) ⟧instr M =
        let
          cond = resolve x M
          M₁ = ⟦ Ω₁ ⟧ M
          M₂ = ⟦ Ω₂ ⟧ M 
        in
          (M₁ ⊕ᴹ M₂) ⊗ᴹ ⟦ joins ⟧φ (if cond then inj₁ M₁ else inj₂ M₂) 
      ⟦ gate (g , inst , ι∗) ⟧instr M =
        let
          o∗ = ⟦ g ∙ inst ⟧gateᶠ (mapᴬ (λ a → ⟦ a ⟧arg M) ι∗)
        in
          lift-mem o∗ 

      ⟦_⟧φ : μ₁ ∥ μ₂ ≫ μ → Memory μ₁ ⊎ Memory μ₂ → Memory μ 
      ⟦ nil ⟧φ M = nil
      ⟦ phi (x , y , js) ⟧φ M
        = (⊎[ cell ∘ resolve x , cell ∘ resolve y ] M) ⊗ᴹ ⟦ js ⟧φ M

      ⟦_⟧arg : μ ⊢i ι → Memory μ → ⟦ ι ⟧input
      ⟦ nil ⟧arg M = nothing
      ⟦ val x ⟧arg M = just (⟦ x ⟧arg M)
      ⟦ pair (ι₁ , ι₂) ⟧arg M = ⟦ ι₁ ⟧arg M , ⟦ ι₂ ⟧arg M
      ⟦ slice ι ⟧arg M = ⟦ ι ⟧args M
      ⟦ constant v ⟧arg M = v
      ⟦ priv x ⟧arg M = lookupᴬ π x
      ⟦ pub x ⟧arg M = lookupᴬ ψ x
      ⟦ wire x ⟧arg M = resolve x M

      ⟦_⟧args : List (μ ⊢i ι) → Memory μ → List ⟦ ι ⟧input
      ⟦ [] ⟧args M = []
      ⟦ ι ∷ ι∗ ⟧args M = ⟦ ι ⟧arg M ∷ ⟦ ι∗ ⟧args M

  ------------------------------------------------------------------------
  -- Below is a conceptual illustration of how the various pieces of
  -- data, as well as the relational and computational semantics
  -- interact in creating ZK proofs of legal execution. 
  ------------------------------------------------------------------------

  Circuit : (Π : PrivateInputs) (Ψ : PublicInputs) → Mem → Set
  Circuit Π Ψ = Typing._≫ᶜ_ 𝓖 𝓟 Π Ψ ⟦_⟧type 𝟙
  
  module _ {Π : PrivateInputs} {Ψ : PublicInputs} (ω : Circuit Π Ψ μ) where 

    Instance Witness : Set
    Instance = All ⟦_⟧type Ψ -- 
    Witness   = All ⟦_⟧type Π × Memory μ

    -- The relational semantics of circuits defines a relation that
    -- encodes the circuit's logic. This corresponds to what we
    -- currently call the "circuit" semantics of ZKIR.
    ZK-Rel : Instance → Witness → Set
    ZK-Rel ψ (π , M) = ⟦ ω ⟧ (nil ⊗ᴹ M)
      where open RelationalSemantics π ψ

    open ZK Instance Witness ZK-Rel 

    --
    -- proving function, used to crreate ZK proofs witnessing that a
    -- certain collection of public inputs corresponds to a legal
    -- execution of a circuit.
    -- 
    prove-circuit : ∀ ψ π → Proof ψ
    -- 
    -- public + private inputs, computed during off-chain execution
    --             (JS), and stored in proof preimage.
    --                         |  |
    --                         v  v  
    prove-circuit ψ π = prove  ψ (π , ⟦ ω ⟧ nil) {!!}
    --                                 ^          ^
    --                                 |          | 
    --       I ntermediate values/memory,         |
    --    computed during the "rehearsal"         |
    --                             phase.         | 
    --                                            |
    --                                            | 
    --    Proof of the relation R, instantiated with the given private
    --    inputs, public inputs, and memory. Such a proof is
    --    synthesized by the proof server by the prover when creating
    --    a call transaction, and later verified by other participants
    --    of the network
    --
      where
        open ComputationalSemantics π ψ 



    -- Verification of "circuit proofs". This would be invoked by
    -- other participants in the network, to validate call
    -- transactions.
    verify-circuit : ∀ ψ → Proof ψ → Set
    verify-circuit ψ p = verify ψ p
