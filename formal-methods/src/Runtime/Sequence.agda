open import Data.List 
open import Data.Product
open import Data.Nat 

open import Runtime.Stack
open import Runtime.Cost
open import Runtime.Instruction
open import Runtime.Semantics 

module Runtime.Sequence where

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

-- The semantics of executing a sequence of opcodes
--
-- Defined by mapping the the (free) monoidal structure of the reflexive
-- transitive closure onto the monoidal structure of the Kleisli category of `M`
⟦_⟧ :   Ψ ─⟪ 𝓒∗ ⟫─→ Φ
        ---------------------
      → Stack Ψ → M (Stack Φ)
⟦ stop      ⟧ = η 
⟦ step x xs ⟧ = ⟦ x ⟧op >=> ⟦ xs ⟧

price∗ : Ψ ─⟪ 𝓒∗ ⟫─→ Φ → Stack Ψ → M Cost
price∗ stop _        = return 0
price∗ (step x xs) σ = do
  σ′ ← ⟦ x ⟧op σ
  c  ← price∗ xs σ′ 
  return (price x σ + c) 
