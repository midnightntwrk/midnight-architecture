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

open import Util.ListSyntax

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Runtime.Type
open import Runtime.Stack
open import Runtime.Path
open import Runtime.Cost
open import Runtime.Instruction
open import Runtime.Sequence
open import Runtime.Semantics 

module Runtime.Impact where


