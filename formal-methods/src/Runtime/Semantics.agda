open import Runtime.Cost
open import Runtime.Stack
open import Runtime.Instruction 

module Runtime.Semantics where

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

postulate 
  -- The semantics of a stack transitition from Ψ₁ to Ψ₂ with cost function 𝓒 is a
  -- Kleisli arrow of the monad M between stacks with shapes given by Ψ
  -- and Φ. 
  ⟦_⟧op : Ψ ─⟨ 𝓒 ⟩─→ Φ
          ---------------------  
        → Stack Ψ → M (Stack Φ)
      
-- ⟦ NOOP c ⟧op σ
--   = return σ

-- ⟦ LT ⟧op (n , (m , ε))
--   = return ({!!} , ε)

-- ⟦ EQ ⟧op σ = {!!}

-- ⟦ TYPE ⟧op σ = {!!}

-- ⟦ SIZE ⟧op σ = {!!}

-- ⟦ NEW ⟧op σ = {!!}

-- ⟦ AND ⟧op σ = {!!}

-- ⟦ OR ⟧op σ = {!!}

-- ⟦ NEG ⟧op σ = {!!}

-- ⟦ LOG ⟧op σ = {!!}

-- ⟦ ROOT ⟧op σ = {!!}

-- ⟦ POP ⟧op σ = {!!}

-- ⟦ POPEQ v ⟧op σ = {!!}

-- ⟦ ADDI v ⟧op σ = {!!}

-- ⟦ SUBI v ⟧op σ = {!!}

-- ⟦ PUSH v ⟧op σ = {!!}

-- ⟦ BRANCH steps ⟧op σ = {!!}

-- ⟦ JMP steps ⟧op σ = {!!}

-- ⟦ ADD ⟧op σ = {!!}

-- ⟦ SUB ⟧op σ = {!!}

-- ⟦ CONCAT limit ⟧op σ = {!!}

-- ⟦ MEMBER x ⟧op σ = {!!}

-- ⟦ REM x ⟧op σ = {!!}

-- ⟦ DUP ⟧op σ = {!!}

-- ⟦ SWAP ⟧op σ = {!!}

-- ⟦ IDX Π π px ⟧op σ = {!!}


price : Ψ ─⟨ 𝓒 ⟩─→ Φ → Stack Ψ → Cost
price {𝓒 = 𝓒} op = 𝓒
