open import Runtime.Type 
open import Runtime.Stack

open import Data.Nat
open import Data.List 

module Runtime.Cost where

-- Calculates the size of a type 
postulate ∣_∣ : Value τ → ℕ

Cost = ℕ


+[_,_] : (Value τ → Cost) → (Stack Ψ → Cost) → Stack (τ ∷ Ψ) → Cost
+[ f , g ] (v , σ) = f v + g σ

-- 
-- resolve : (v : Value τ) → (π : Path Π) → (σ : Stack (stackty Π)) → Value (resvt v π)
-- resolve = {!!} 
-- 

‵_ : Cost → Stack Ψ → Cost 
(‵ c) σ = c


variable 𝓒 𝓒₁ 𝓒₂ 𝓒₃ 𝓒′ : Stack Ψ → Cost  
