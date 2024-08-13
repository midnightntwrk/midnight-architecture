open import Data.List.Relation.Unary.All
open import Data.List hiding ([_] ; null)
open import Data.Nat hiding (_⊔_) renaming (_+_ to _ℕ+_)
open import Data.Integer hiding (_⊔_ ; ∣_∣)
open import Relation.Unary using (IUniversal ; _⇒_)
open import Data.Sum renaming ([_,_] to ⊎[_,_])
open import Data.Vec hiding ([_] ; _++_) 

open import Function
open import Data.Product
open import Data.Unit
open import Data.Product
open import Data.Bool 

open import Relation.Unary using (IUniversal ; _⇒_ ; U)

open import Level

open import ListSyntax

open import Relation.Binary.PropositionalEquality hiding ([_])

module Impact where
  
-- Could change this to simulate overflows 
int64 = ℤ 

-- "Aligned values" that can be cast from and to 64 bit integers (represented
-- here as natural numbers)
data Typeᴬ : Set where 
  bool int type digest : Typeᴬ

data Type : Set where
  null : Type
  cell : Typeᴬ → Type  

  dict   : Typeᴬ → Type → Type
  array  : Type → Type
  bmtree : Type → Type

⋆ = cell

infixr 10 _∣_ 
data TypeConstraint : Set where
  dict array bmtree cell null : TypeConstraint
  _∣_ : (C₁ C₂ : TypeConstraint) → TypeConstraint 

infix 9 _∈_
_∈_ : (τ : Type) → TypeConstraint → Set
τ ∈ dict   = ∃₂ λ t τ′ → τ ≡ dict t τ′
τ ∈ array  = ∃ λ τ′ → τ ≡ array τ′
τ ∈ bmtree = ∃ λ τ′ → τ ≡ bmtree τ′
τ ∈ cell   = ∃ λ t → τ ≡ cell t
τ ∈ null   = τ ≡ null
τ ∈ C₁ ∣ C₂ = τ ∈ C₁ ⊎ τ ∈ C₂ 


⟦_⟧ᴬ : Typeᴬ → Set
⟦ bool   ⟧ᴬ = Bool
⟦ type   ⟧ᴬ = Type
⟦ int    ⟧ᴬ = ℤ
⟦ digest ⟧ᴬ = ℤ

⟦_⟧ᵀ : Type → Set
⟦ null       ⟧ᵀ = ⊤
⟦ cell t     ⟧ᵀ = ⟦ t ⟧ᴬ
⟦ dict x t   ⟧ᵀ = {!!}
⟦ array t    ⟧ᵀ = {!!}
⟦ bmtree t   ⟧ᵀ = {!!}

variable t u t₁ t₂ t₃ u₁ u₂ u₃ t′ u′ : Typeᴬ
         τ τ₁ τ₂ τ₃ τ′ : Type 

postulate
  toℤ   : ⟦ t ⟧ᴬ → ℤ

record Value (t : Type) : Set where
  constructor extend
  field reflect : ⟦ t ⟧ᵀ 

open Value

-- Calculates the size of a type 
postulate ∣_∣ : Value τ → ℕ

StackTy = List Type

variable Ψ Ψ₁ Ψ₂ Ψ₃ Ψ′ : StackTy

Cost = ℕ

data Stack : StackTy → Set where
  ε   : Stack []
  _,_ : Value τ → Stack Ψ → Stack (τ ∷ Ψ)

+[_,_] : (Value τ → Cost) → (Stack Ψ → Cost) → Stack (τ ∷ Ψ) → Cost
+[ f , g ] (v , σ) = f v ℕ+ g σ

data PathEntry : Set where
  stack  : Type → PathEntry
  value  : Type → PathEntry 

entry-elim : ∀ {a}{A : Set a} → (Type → A) → (Type → A) → PathEntry → A
entry-elim s f (stack τ)  = s τ
entry-elim s f (value τ) = f τ

PathTy = List PathEntry   

variable Π Π₁ Π₂ Π′ : PathTy 

Path : PathTy → Set
Path = All (entry-elim U Value)

-- Converts a path type to a stack type with types for all occurrences of the
-- `stack` marker
stackty : PathTy → StackTy
stackty [] = []
stackty (stack τ ∷ Π) = τ ∷ stackty Π
stackty (value τ ∷ Π) = stackty Π

-- Converts a path type to a stack type containing all types of the path 
allty : PathTy → StackTy
allty []            = []
allty (stack τ ∷ Π) = τ ∷ allty Π
allty (value τ ∷ Π) = τ ∷ allty Π
 
-- Calculates the type of the value that a path resolves to 
resvt : Value τ → Path Π → Stack (stackty Π) → Type
resvt v [] ε = {!!}
resvt v (px ∷ π) σ = {!!}

resvc : Path Π → Stack (stackty Π) → Cost
resvc = {!!} 

resolve : (v : Value τ) → (π : Path Π) → (σ : Stack (stackty Π)) → Value (resvt v π σ)
resolve = {!!} 

variable Φ Φ₁ Φ₂ Φ₃ Φ′ : Stack Ψ → StackTy 

pop : Stack (τ ∷ Ψ) → Stack Ψ
pop (v , σ) = σ

top : Stack (τ ∷ Ψ) → Value τ
top (v , σ) = v

‵_ : Cost → Stack Ψ → Cost 
(‵ c) σ = c

variable 𝓒 𝓒₁ 𝓒₂ 𝓒₃ 𝓒′ : Stack Ψ → Cost  

-- The following inductive relationd defines *typed* opcodes for the Impact VM. 
--
-- Witnesses typed by this relation should be read as: 
-- 
-- `<STACK BEFORE>  ─⟨  <COST OF EXECUTION op>¹ ⟩─→  <STACK AFTER>²`
--
-- That is, `op : Ψ ─⟨ 𝓒 ⟩─→ Φ` means that opcode `op` transforms a stack with
-- shape `Ψ` into a stack with shape `Φ` with cost `𝓒`. 
-- 
-- We use the notation `<STACK BEFORE> κ─⟨ <COST> ⟩ <STACK AFTER>` to denote an
-- operation for which the shape of the stack after execution of the operation
-- explicitly doesn't depend on the state of the stack before.
--
--
-- FOOTNOTES
-- 
-- (1) The cost of an operation may depend on the state of the stack before `op`
--     is executed. For example, the cost of removing an element from a
--     structure depends on the size of the structure.
-- 
-- (2) The *shape* of the stack after executing op `op` may depend on the stack
--     before `op` is ececuted. We need this e.g. to type the `NEW` opcode,
--     which leaves an element on the stack whose type depends on the value of
--     the stack before the operation is executed
--
mutual
  infixr 2 _κ─⟨_⟩─→_
  _κ─⟨_⟩─→_ : (Ψ : StackTy) → (Stack Ψ → Cost) → StackTy → Set
  Ψ₁ κ─⟨ 𝓒 ⟩─→ Ψ₂ = Ψ₁ ─⟨ 𝓒 ⟩─→ λ _ → Ψ₂ 

  infixr 2 _─⟨_⟩─→_
  data _─⟨_⟩─→_ : (Ψ : StackTy) → (𝓒 : Stack Ψ → Cost) → (Stack Ψ → StackTy) → Set where

    NOOP    : (c : Cost)
              -----------------------
            → []  κ─⟨ const c ⟩─→  []
            

    LT      : ------------------------------------------
              [ ⋆ t , ⋆ t ]  κ─⟨ const 1 ⟩─→  [ ⋆ bool ]


    EQ      : ------------------------------------------
              [ ⋆ t , ⋆ t ]  κ─⟨ const 1 ⟩─→  [ ⋆ bool ]


    TYPE    : ----------------------------------
              [ τ ]  κ─⟨ const 1 ⟩─→  [ ⋆ type ]


    SIZE    : ---------------------------------
              [ τ ]  κ─⟨ const 1 ⟩─→  [ ⋆ int ]


    NEW     : ---------------------------------------------------
              [ ⋆ type ] ─⟨ const 1 ⟩─→  λ σ → [ top σ .reflect ]


    AND     : ------------------------------------------------
              [ ⋆ bool , ⋆ bool ]  κ─⟨ const 1 ⟩─→  [ ⋆ bool ]


    OR      : ------------------------------------------------
              [ ⋆ bool , ⋆ bool ]  κ─⟨ const 1 ⟩─→  [ ⋆ bool ]


    NEG     : ---------------------------------------
              [ ⋆ bool ]  κ─⟨ const 1 ⟩─→  [ ⋆ bool ]


    LOG     : --------------------------
              [ τ ]  κ─⟨ const 1 ⟩─→  []


    ROOT    : -------------------------------------------
              [ bmtree τ ]  κ─⟨ const 1 ⟩─→  [ ⋆ digest ]  


    POP     : --------------------------
              [ τ ]  κ─⟨ const 1 ⟩─→  []


    POPEQ   : (v : Value τ)
              -----------------------------
            → [ τ ]  κ─⟨ const ∣ v ∣ ⟩─→  []


    -- What's the type of the thing stored on stack? also for sub
    ADDI    : (v : Value τ)
              ------------------------------------
            → [ τ ]  κ─⟨ const ∣ v ∣ ⟩─→  [ ⋆ int ]


    SUBI    : (v : Value τ)
              ------------------------------------
            → [ τ ]  κ─⟨ const ∣ v ∣ ⟩─→  [ ⋆ int ]


    PUSH    : (v : Value τ)
              -----------------------------
            → []  κ─⟨ const ∣ v ∣ ⟩─→  [ τ ]


    BRANCH  : (steps : ℕ)
              ---------------------------
            → [ τ ]  κ─⟨ const 1  ⟩─→  []


    JMP     : (steps : ℕ)
              -----------------------
            → []  κ─⟨ const 1 ⟩─→  []


    ADD     : --------------------------------------
              [ ⋆ t , ⋆ t ] κ─⟨ const 1 ⟩─→  [ ⋆ t ]    


    SUB     : ---------------------------------------
              [ ⋆ t , ⋆ t ]  κ─⟨ const 1 ⟩─→  [ ⋆ t ] 


    CONCAT  : (limit : ℕ)
              ---------------------------------------
            → [ ⋆ t , ⋆ t ]  κ─⟨ const 1 ⟩─→  [ ⋆ t ] 


    MEMBER  : τ ∈ dict ∣ array
              -----------------------------------------------
            → [ ⋆ t , τ ]  κ─⟨ ∣_∣ ∘ top ∘ pop ⟩─→  [ ⋆ bool ]


    REM     : τ ∈ dict ∣ array
              ------------------------------------------
            → [ ⋆ t , τ ]  κ─⟨ ∣_∣ ∘ top ∘ pop ⟩─→  [ τ ] 


    DUP     : ------------------------------------------------
              Ψ ++ [ τ ]  κ─⟨ const 1 ⟩─→  [ τ ] ++ Ψ ++ [ τ ] 


    SWAP    : -------------------------------------------------------------
              [ τ₁ ] ++ Ψ ++ [ τ₂ ]  κ─⟨ const 1 ⟩─→  [ τ₂ ] ++ Ψ ++ [ τ₁ ] 


    IDX     : ∀ (π : Path Π)
            → τ ∈ dict ∣ array
              -------------------------------------------------------------------------------
            → [ τ ] ++ stackty Π  ─⟨ +[ ∣_∣ , resvc π ] ⟩─→  λ σ → [ resvt (top σ) π (pop σ) ] 

    {- TODO: remaining opcodes -} 

  
-- variable A B C : Set 
--          c c₁ c₂ : Cost 

-- postulate
--   M : Cost → Set → Set
--   η : A → M 0 A
--   μ : M c₁ (M c₂ A) → M (c₁ ℕ+ c₂) A 
--   fmap : (A → B) → M c A → M c B

-- -- The semantics of a stack transitition from Ψ₁ to Ψ₂ with cost function 𝓒 is a
-- -- dependent Kleisli arrow of a cost-graded monad M between stacks with shapes
-- -- given by Ψ and Φ, and grade 𝓒. 
-- execute-op : Ψ ─⟨ 𝓒 ⟩─→ Φ
--              -------------------------------------  
--            → (σ : Stack Ψ) → M (𝓒 σ) (Stack (Φ σ))
-- execute-op σ = {!!} 

-- This used to define the reflexive-transitive closure of stack
-- transformations, but sadly breaks spectacularly once we add an explicit
-- dependency from between the input stack and the type of the output stack
-- 
-- data _─⟪_⟫─→_ : (Φ₁ : Stack Ψ → StackTy) → (Stack Ψ → Cost) → (Stack {!Ψ!} → StackTy) → Set where
-- 
--   stop : ∀ Ψ (Φ : Stack Ψ → StackTy) → Φ ─⟪ const 0 ⟫─→ Φ
-- 
--   step : Ψ ─⟨ 𝓒₁ ⟩─→ Φ₁
--        → {!!} ─⟪ 𝓒₂ ⟫─→ Φ₂
--          --------------------
--        → {!!} ─⟪ {!!} ⟫─→ {!!} 
-- -- 
-- -- execute : Ψ₁ ─⟪ c ⟫─→ Ψ₂ → Stack Ψ₁ → M c (Stack Ψ₂)
-- -- execute stop         σ = η σ
-- -- execute (step op pr) σ = μ (fmap (execute pr) (execute-op op σ))

