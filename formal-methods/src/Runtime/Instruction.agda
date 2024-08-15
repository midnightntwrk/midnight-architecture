open import Runtime.Type 
open import Runtime.Stack
open import Runtime.Path
open import Runtime.Cost

open import Function
open import Util.ListSyntax

open import Data.Nat
open import Data.List hiding ([_])
open import Data.Product 

module Runtime.Instruction where 

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
          → [ τ ] ++ ⇊s Π ─⟨ const 0 {- TODO -} ⟩─→  [ τ′ ] 

  {- TODO: remaining opcodes -} 
