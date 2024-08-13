open import Data.List using (List ; _∷_ ; [])
open import Data.String using (String)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Product using (_×_)

module Syntax where 

Identifier = String 

{- Literals -}

data Literal : Set where
  true false : Literal
  nat        : ℕ → Literal
  string     : String → Literal
  pad        : ℕ → String → Literal 


data Type : Set where 

data LType : Set where

data LedgerADT : Set where
  

mutual

  data Term : Set where

    ident : Identifier → Term

    -- Returns the default value of a given type (called "null" currently) 
    default : Type → Term

    -- Returns the default value of a ledger ADT 
    defaultˡ : LType → Term 

    -- Ternary selection 
    sel : {!!} → {!!} → {!sc!} → Term 

    -- Ledger assignment 
    assign : Termscratch

    -- Boolean and comparison operations 
    or and eq neq lt leq gt geq : Term

    -- Boolean negation 
    neg : Term → Term

    -- Number operations
    add mul min : Term → Term → Term

    
  

  LedgerAccessor = Identifier × Term × Term 

 

-- Identifier = String

-- data VersionTerm : Set where
  

-- data VersionExpr : Set where
--   _∣∣_ _&&_ : (e₁ e₂ : VersionExpr) → VersionExpr
--   term : VersionTerm → VersionExpr 


-- data Element : Set where

--   pragma : Identifier → {!!} → Element



-- Program = List Element

