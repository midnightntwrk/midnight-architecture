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

open import Relation.Unary using (IUniversal ; Satisfiable ; _⇒_ ; U)

open import Level

open import ListSyntax

open import Relation.Binary.PropositionalEquality hiding ([_])

module Impact where
  
-- Could change this to simulate overflows 
int64 = ℤ 

mutual 
  -- "Aligned values" that can be cast from and to 64 bit integers (represented
  -- here as natural numbers)
  data Typeᴬ : Set where 
    bool int digest : Typeᴬ  
    type : Type → Typeᴬ

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
⟦ type τ   ⟧ᴬ = ⊤ 
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

-- Defines the type of keys in the union of arrays and dictionaries
_~key_ : ∀ τ → τ ∈ array ∣ dict → Type
.(array τ)    ~key inj₁ (τ       , refl) = ⋆ int
.(dict τ₁ τ₂) ~key inj₂ (τ₁ , τ₂ , refl) = ⋆ τ₁

-- Defines the type of values in the union of arrays and dictionaries 
_~val_ : ∀ τ → τ ∈ array ∣ dict → Type 
.(array τ)    ~val (inj₁ (τ       , refl)) = τ
.(dict τ₁ τ₂) ~val (inj₂ (τ₁ , τ₂ , refl)) = τ₂

get : (px : τ ∈ array ∣ dict) → ⟦ τ ⟧ᵀ → ⟦ τ ~key px ⟧ᵀ → ⟦ τ ~val px ⟧ᵀ
get = {!!} 


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
         Φ Φ₁ Φ₂ Φ₃ Φ′ : StackTy 

infix 9 _∈∗_ 
_∈∗_ : (Ψ : StackTy) → TypeConstraint → Set
Ψ ∈∗ C = All (_∈ C) Ψ

Cost = ℕ

data Stack : StackTy → Set where
  ε   : Stack []
  _,_ : Value τ → Stack Ψ → Stack (τ ∷ Ψ)

+[_,_] : (Value τ → Cost) → (Stack Ψ → Cost) → Stack (τ ∷ Ψ) → Cost
+[ f , g ] (v , σ) = f v ℕ+ g σ

-- The type of well-formed paths. A proof of the form `PathTy τ₁ τ₂‵ proves that
-- we can retrieve a value of type `τ₁` from a value of type `τ₂` by repeated
-- indexing into sub-structures.
--
-- A path can be constructed in 2 ways.
--
-- (1) The empty path 
--
-- (2) The "cons" operation, which, given a path to retrieve a `τ` by indexing
--     into the type of values stored in `τ′`, proves that we can also retrieve
--     a `τ` by indexing into `τ′` itself. We store a proof that `τ′` is an
--     "indexable" structure (i.e., `array ∣ dict`), and a flag telling us
--     wether the corresponding key is to be found in the path or on the stack.
--
data PathTy (τ : Type) : Type → Set where
  ε   : PathTy τ τ
  [_,_]∷_ : (stack? : Bool) → (px : τ′ ∈ array ∣ dict) → PathTy τ (τ′ ~val px) → PathTy τ τ′ 

len : PathTy τ₁ τ₂ → ℕ
len ε              = 0
len ([ _ , _ ]∷ Π) = ℕ.suc (len Π)

variable Π Π₁ Π₂ Π′ : PathTy τ₁ τ₂

data Path {τ₁} : ∀ {τ₂} → (Π : PathTy τ₁ τ₂) → Set where

  []  : Path ε

  -- Stack consing, we don't store the key but rather it's to be stored on the
  -- stack.
  _∷s_    : (px : τ₂ ∈ array ∣ dict)
          → {Π : PathTy τ₁ (τ₂ ~val px) }
          → Path Π 
            --------------------------------
          → Path ([ true , px ]∷ Π)

  -- Value consing, we store the key as part of the path. 
  [_,]∷v_ : (px : τ₂ ∈ array ∣ dict)
          → {Π : PathTy τ₁ (τ₂ ~val px)}
          → Value (τ₂ ~key px)
          → Path Π
            ----------------------------
          → Path ([ false , px ]∷ Π) 

-- Converts a path type to a stack type with types for all occurrences of the
-- `stack` marker
⇊s : PathTy τ₁ τ₂ → StackTy
⇊s           ε                   = []
⇊s           ([ false , px ]∷ Π) = ⇊s Π
⇊s {τ₂ = τ₂} ([ true  , px ]∷ Π) = (τ₂ ~key px) ∷ ⇊s Π

-- "downgrades" a path type to a stack type containing all types of the path 
⇊ : PathTy τ₁ τ₂ → StackTy
⇊           ε               = []
⇊ {τ₂ = τ₂} ([ _ , px ]∷ Π) = (τ₂ ~key px) ∷ ⇊ Π

-- 
-- resolve : (v : Value τ) → (π : Path Π) → (σ : Stack (stackty Π)) → Value (resvt v π)
-- resolve = {!!} 
-- 
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
infixr 2 _─⟨_⟩─→_
data _─⟨_⟩─→_ : (Ψ : StackTy) → (𝓒 : Stack Ψ → Cost) → (Φ : StackTy) → Set where

  NOOP    : (c : Cost)
            ----------------------
          → []  ─⟨ const c ⟩─→  []
            

  LT      : -----------------------------------------
            [ ⋆ t , ⋆ t ]  ─⟨ const 1 ⟩─→  [ ⋆ bool ]


  EQ      : -----------------------------------------
            [ ⋆ t , ⋆ t ]  ─⟨ const 1 ⟩─→  [ ⋆ bool ]


  TYPE    : ---------------------------------
            [ τ ]  ─⟨ const 1 ⟩─→  [ ⋆ (type τ) ]


  SIZE    : --------------------------------
            [ τ ]  ─⟨ const 1 ⟩─→  [ ⋆ int ]


  NEW     : -----------------------------------
            [ ⋆ (type τ) ] ─⟨ const 1 ⟩─→ [ τ ]


  AND     : -----------------------------------------------
            [ ⋆ bool , ⋆ bool ]  ─⟨ const 1 ⟩─→  [ ⋆ bool ]


  OR      : -----------------------------------------------
            [ ⋆ bool , ⋆ bool ]  ─⟨ const 1 ⟩─→  [ ⋆ bool ]


  NEG     : --------------------------------------
            [ ⋆ bool ]  ─⟨ const 1 ⟩─→  [ ⋆ bool ]


  LOG     : -------------------------
            [ τ ]  ─⟨ const 1 ⟩─→  []


  ROOT    : ------------------------------------------
            [ bmtree τ ]  ─⟨ const 1 ⟩─→  [ ⋆ digest ]  


  POP     : -------------------------
            [ τ ]  ─⟨ const 1 ⟩─→  []


  POPEQ   : (v : Value τ)
            ----------------------------
          → [ τ ]  ─⟨ const ∣ v ∣ ⟩─→  []


  -- What's the type of the thing stored on stack? also for sub
  ADDI    : (v : Value τ)
            -----------------------------------
          → [ τ ]  ─⟨ const ∣ v ∣ ⟩─→  [ ⋆ int ]


  SUBI    : (v : Value τ)
            -----------------------------------
          → [ τ ]  ─⟨ const ∣ v ∣ ⟩─→  [ ⋆ int ]


  PUSH    : (v : Value τ)
            ----------------------------
          → []  ─⟨ const ∣ v ∣ ⟩─→  [ τ ]


  BRANCH  : (steps : ℕ)
            --------------------------
          → [ τ ]  ─⟨ const 1  ⟩─→  []


  JMP     : (steps : ℕ)
            ----------------------
          → []  ─⟨ const 1 ⟩─→  []


  ADD     : -------------------------------------
            [ ⋆ t , ⋆ t ] ─⟨ const 1 ⟩─→  [ ⋆ t ]    


  SUB     : --------------------------------------
            [ ⋆ t , ⋆ t ]  ─⟨ const 1 ⟩─→  [ ⋆ t ] 


  CONCAT  : (limit : ℕ)
            --------------------------------------
          → [ ⋆ t , ⋆ t ]  ─⟨ const 1 ⟩─→  [ ⋆ t ] 


  MEMBER  : τ ∈ dict ∣ array
            ----------------------------------------------
          → [ ⋆ t , τ ]  ─⟨ ∣_∣ ∘ top ∘ pop ⟩─→  [ ⋆ bool ]


  REM     : τ ∈ dict ∣ array
            -----------------------------------------
          → [ ⋆ t , τ ]  ─⟨ ∣_∣ ∘ top ∘ pop ⟩─→  [ τ ] 


  DUP     : -----------------------------------------------
            Ψ ++ [ τ ]  ─⟨ const 1 ⟩─→  [ τ ] ++ Ψ ++ [ τ ] 


  SWAP    : ------------------------------------------------------------
            [ τ₁ ] ++ Ψ ++ [ τ₂ ]  ─⟨ const 1 ⟩─→  [ τ₂ ] ++ Ψ ++ [ τ₁ ] 


  IDX     : (Π : PathTy τ′ τ)
          → (π : Path Π)
          → (px  : τ   ∈  dict ∣ array)
            ------------------------------------------------
          → [ τ ] ++ ⇊s Π  ─⟨ (_ℕ+ len Π) ∘ {!!} ⟩─→  [ τ′ ] 

  {- TODO: remaining opcodes -} 


variable A B C : Set 
         c c₁ c₂ : Cost 

postulate
  M     : Set → Set
  η     : A → M A
  μ     : M (M A) → M A  
  fmap  : (A → B) → M A → M B

_>>=_ : M A → (A → M B) → M B
m >>= f = μ (fmap f m)

_>>_ : M A → M B → M B
m₁ >> m₂ = m₁ >>= λ _ → m₂

_>=>_ : (A → M B) → (B → M C) → A → M C
f >=> g = λ x → f x >>= g

return = η 


-- The semantics of a stack transitition from Ψ₁ to Ψ₂ with cost function 𝓒 is a
-- dependent Kleisli arrow of a cost-graded monad M between stacks with shapes
-- given by Ψ and Φ, and grade 𝓒. 
⟦_⟧op : Ψ ─⟨ 𝓒 ⟩─→ Φ
        ---------------------  
      → Stack Ψ → M (Stack Φ)
⟦ op ⟧op σ = {!!}



{-
      BYTECODE SEQUENCES 
-} 

-- The free monoid over cost models 
Cost∗ = List (∃ λ Ψ → Stack Ψ → Cost)
variable 𝓒∗ : Cost∗ 

-- The reflexive transitive closure of well-formed opcodes. For now, we index
-- with the free monoid of cost models, because the definition of costs is
-- deeply semantic: at any point in the sequence the cost of an operation may
-- depend fully on the semantics of all preceding opcodes.
--
-- ### NOTE ###
--
-- This enforces *very* strict requirements on the shape of the stack when
-- constructing bytecode sequences, in the sense that it requires the shape of
-- input and output stack on the boundary between operations to be an exact
-- match. Instead, we'd want these to match under more lenient circumstances,
-- i.e., if there's a common prefix.
-- 
-- For example, the sequence `PUSH 1;PUSH 2;PUSH 3;ADD;ADD` should be fine, but
-- we can't define it using the closure relation below.

data _─⟪_⟫─→_ : (Ψ : StackTy) → Cost∗ → (Φ : StackTy) → Set where

  stop : Ψ ─⟪ [] ⟫─→ Ψ

  step : (o : Ψ ─⟨ 𝓒₁ ⟩─→ Φ)  
       → Φ ─⟪ 𝓒∗ ⟫─→ Φ′ 
         ------------------------
       → Ψ ─⟪ (-, 𝓒₁) ∷ 𝓒∗ ⟫─→ Φ′


-- -- The semantics of executing a sequence of opcodes
-- --
-- -- Defined by mapping the the (free) monoidal structure of the reflexive
-- -- transitive closure onto the monoidal structure of the Kleisli category of `M`
-- ⟦_⟧ :   Ψ ─⟪ 𝓒∗ ⟫─→ Φ
--         ---------------------
--       → Stack Ψ → M (Stack Φ)
-- ⟦ stop      ⟧ = η 
-- ⟦ step x xs ⟧ = ⟦ x ⟧op >=> ⟦ xs ⟧

-- price : Ψ ─⟨ 𝓒 ⟩─→ Φ → Stack Ψ → Cost
-- price {𝓒 = 𝓒} op = 𝓒

-- price∗ : Ψ ─⟪ 𝓒∗ ⟫─→ Φ → Stack Ψ → M Cost
-- price∗ stop _        = return 0
-- price∗ (step x xs) σ = do
--   σ′ ← ⟦ x ⟧op σ
--   c  ← price∗ xs σ′ 
--   return (price x σ ℕ+ c) 

