{-# OPTIONS --erasure #-} 


open import Haskell.Prelude using (List ; _∷_ ; [] ; ⊤ ; foldr ; tt ; map ; IO ; String; fromString)
open import Haskell.Prim using (the)

open import Agda.Builtin.Reflection renaming (Name to RName) hiding (Sort)
open import Reflection.TCM.Syntax using (_>>_ ; _>>=_ ; _<$>_ ; _<*>_ )
open import Agda.Builtin.String using (primStringToList)
open import Function using (_∘_)

open import Data.String using (wordsBy)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool.Properties using (T?)
open import Function using (case_of_)
open import Data.String using (_++_)



module Language.Syntax.IR  where 

imports : TC ⊤
imports = do
  pragmaForeign "AGDA2HS" "{-# LANGUAGE TemplateHaskell #-}" 
  pragmaForeign "AGDA2HS" "import Data.Data hiding (Proxy)"
  pragmaForeign "AGDA2HS" "import Data.Aeson"
  pragmaForeign "AGDA2HS" "import Serialize"

datadefs : (ir : List RName) → TC ⊤
datadefs ir =
  foldr _>>_ (returnTC tt)
    ( map
        (λ n → pragmaCompile "AGDA2HS" n "deriving (Show , Typeable , Data)")
        ir )

unqualify : Data.String.String -> Data.String.String
unqualify s with wordsBy (T? ∘ primCharEquality '.') s
... | []       = ""
... | (x ∷ xs) = lastname xs x
  where
    lastname : List Data.String.String → Data.String.String → Data.String.String
    lastname [] s = s
    lastname (x ∷ xs) s = lastname xs x

postulate
  Sort    : Set
  Tag   : (a : Set) → Set
  MkTag : ∀ {a} →  Tag a 
  getSort : ∀ {a} → Tag a → Sort
  serialize : String → List Sort → IO ⊤ 

sortf : RName  → TC Term
sortf n = do
  ref ← unquoteTC (def n []) 
  quoteTC (getSort (the (Tag ref) MkTag))

sortdef : RName → TC RName 
sortdef n = do
  n' ← freshName ("sd" ++ unqualify (primShowQName n))
  tm ← sortf n
  sort ← quoteTC Sort 
  declareDef (arg (arg-info visible (modality relevant quantity-ω)) n') sort
  defineFun n' (clause [] [] tm ∷ [])
  pragmaCompile "AGDA2HS" n' ""
  returnTC n'  

collectSorts : List RName → TC Term
collectSorts []       = quoteTC {A = List Sort} [] 
collectSorts (x ∷ xs) = do
  head ← unquoteTC {A = Sort} (def x [])
  tail ← collectSorts xs >>= unquoteTC 
  quoteTC (head ∷ tail) 

sortdefs : (ir : List RName) → TC RName 
sortdefs ir = do 
  xs    ← foldr (λ m ms -> _∷_ <$> m <*> ms) (returnTC []) (map sortdef ir)
  tm    ← collectSorts xs
  sortl ← quoteTC (List Sort)
  sd    ← freshName ("ir")
  declareDef (arg (arg-info visible (modality relevant quantity-ω)) sd) sortl
  defineFun sd (clause [] [] tm ∷ [])
  pragmaCompile "AGDA2HS" sd ""
  returnTC sd

emitdef : (irName : RName) → TC ⊤
emitdef sd = do
  t     ← quoteTC (IO ⊤)
  n     ← freshName "emit"
  sdtm  ← unquoteTC (def sd []) 
  declareDef (arg (arg-info visible (modality relevant quantity-ω)) n) t
  cls   ← quoteTC (serialize "schema.json" sdtm) 
  defineFun n (clause [] [] cls ∷ [])
  pragmaCompile "AGDA2HS" n "" 

registerIR : (ir : List RName) → TC ⊤ 
registerIR ir = imports >> datadefs ir >> sortdefs ir >>= emitdef  

