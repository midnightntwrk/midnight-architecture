open import Data.Bool
open import Data.Nat 
open import Data.List 

open import Runtime.Type
open import Runtime.Stack

module Runtime.Path where

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
