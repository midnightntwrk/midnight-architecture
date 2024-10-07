{-# OPTIONS --erasure #-}

open import Haskell.Prelude using
  (String ; Bool ; List ; Nat ; Either ; _∷_ ; [] ; map ; ⊤ ; tt ; foldr ; last ; words)

module Language.Syntax.Lsrc where

{- Based on l58 and onwards of `lang.ss` (compiler source) -}
mutual
  data Name : Set where
    MkName : String → Name 

  data LsrcProgram : Set where
    Elems : (peltl* : List LsrcProgramElement) → LsrcProgram 

  data LsrcProgramElement : Set where
    Incld        : (incld : LsrcInclude) → LsrcProgramElement
    Mdefn        : (mdefn : LsrcModuleDefinition) → LsrcProgramElement
    Idecl        : (idecl : LsrcImportDeclaration) → LsrcProgramElement
    Xdecl        : (xdecl : LsrcExportDeclaration) → LsrcProgramElement
    Ldecl        : (ldecl : LsrcLedgerDeclaration) → LsrcProgramElement
    Lconstructor : (lconstructor : LsrcLedgerConstructor) → LsrcProgramElement
    Cdefn        : (cdefn : LsrcCircuitDefinition) → LsrcProgramElement
    Edecl        : (edecl : LsrcExternalDeclaration) → LsrcProgramElement
    Wdecl        : (wdecl : LsrcWitnessDeclaration) → LsrcProgramElement 
    Ecdecl       : (ecdecl : LsrcExternalContractDeclaration) → LsrcProgramElement
    Structdef    : (structdef : LsrcStructureDefinition) → LsrcProgramElement
    Enumdef      : (enumdef : LsrcEnumDefinition) → LsrcProgramElement 

  data LsrcInclude : Set where
    Include : (file : Name) → LsrcInclude

  data LsrcModuleDefinition : Set where
    Module : ( exported?   : Bool )
             ( module-name : Name )
             ( type-param* : List LsrcTypeParam )
             ( pelt*       : List LsrcProgramElement )
           → LsrcModuleDefinition

  data LsrcImportDeclaration : Set where
    Import : ( module-name : Name )
             ( targ*       : LsrcTypeArgument )
             ( prefix      : Name ) -- Q: is this right?g
           → LsrcImportDeclaration 

  data LsrcExportDeclaration : Set where
    Export : (name* : List Name) → LsrcExportDeclaration

  data LsrcLedgerDeclaration : Set where
    PublicLedgerDeclaration : ( exported?         : Bool )
                                ( sealed?           : Bool )
                                ( ledger-field-name : Name )
                                ( public-adt        : LsrcPublicLedgerAdt )
                              → LsrcLedgerDeclaration

  data LsrcLedgerConstructor : Set where
    Constructor : ( arg* : List LsrcArgument )
                   ( stmt : LsrcStatement ) 
                 → LsrcLedgerConstructor 

  data LsrcCircuitDefinition : Set where
    Circuit : ( exported?     : Bool )
              ( pure-decl?    : Bool ) 
              ( function-name : Name )
              ( type-param*   : List LsrcTypeParam )
              ( arg*          : List LsrcArgument )
              ( type          : LsrcType )
              ( stmt          : LsrcStatement )
            → LsrcCircuitDefinition

  data LsrcExternalDeclaration : Set where
    External : ( exported?     : Bool )
               ( function-name : Name )
               ( type-param*   : List LsrcTypeParam )
               ( arg*          : List LsrcArgument )
               ( type          : LsrcType ) 
             → LsrcExternalDeclaration 

  data LsrcWitnessDeclaration : Set where
    Witness : ( exported? : Bool )
              ( function-name : Bool )
              ( type-param*   : List LsrcTypeParam )
              ( arg*          : List LsrcArgument )
              ( type          : LsrcType )
            → LsrcWitnessDeclaration 

  data LsrcExternalContractDeclaration : Set where
    ExternalContract : ( exported?       : Bool )
                        ( contract-name   : Name )
                        ( ecdecl-circuit* : List LsrcExternalContractCircuit )
                      → LsrcExternalContractDeclaration

  data LsrcExternalContractCircuit : Set where
    ExternalCircuit : ( function-name : Name )
                       ( arg*          : List LsrcArgument )
                       ( type          : LsrcType ) 
                     → LsrcExternalContractCircuit 
  
  
  data LsrcStructureDefinition : Set where
    Struct : ( exported?   : Bool )
             ( struct-name : Name )
             ( type-param* : List LsrcTypeParam )
             ( arg*        : List LsrcArgument )
           → LsrcStructureDefinition 

  data LsrcEnumDefinition : Set where
    Enum : ( exported? : Bool )
           ( enum-name : Name )
           ( elt-name  : Name )
           ( elt-name*  : List Name )
         → LsrcEnumDefinition

  data LsrcPublicLedgerAdt : Set where
    AdtName : ( adt-name : Name )
               ( adt-arg* : LsrcPublicLedgerAdtArg )
             → LsrcPublicLedgerAdt 

  data LsrcPublicLedgerAdtArg : Set where
    Nat'     : (nat : Nat) → LsrcPublicLedgerAdtArg
    AdtType : (adt-type : LsrcPublicLedgerAdtType) → LsrcPublicLedgerAdtArg

  data LsrcPublicLedgerAdtType : Set where
    Type       : LsrcType → LsrcPublicLedgerAdtType 
    PublicAdt : LsrcPublicLedgerAdt → LsrcPublicLedgerAdtType
  
  data LsrcTypeParam : Set where
    NatValued  : (tvar-name : Name) → LsrcTypeParam
    TypeValued : (tvar-name : Name) → LsrcTypeParam  

  data LsrcArgument : Set where
    Arg : (var-name : Name) → (type : LsrcType) → LsrcArgument 

  {-
    ## EXPRESSIONS and STATEMENTS ## 
  -}
  data LsrcStatement : Set where
    StatementExpression : LsrcExpression → LsrcStatement
    _:=_     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    _:+=_     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    _:-=_     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    Return : (expr : LsrcExpression) → LsrcStatement 
    Assert : (expr : LsrcExpression) → (msg : Name) → LsrcStatement
    Const  : (var-name : Name) (adt-type : LsrcPublicLedgerAdtType) (expr : LsrcExpression) → LsrcStatement 
    If     : (expr : LsrcExpression) (stmt1 stmt2 : LsrcStatement) → LsrcStatement
    For    : (var-name : Name) (expr : LsrcExpression) (stmt : LsrcStatement) → LsrcStatement
    Block  : (stmt* : List LsrcStatement) → LsrcStatement 

  data LsrcExpression : Set where 
    QuoteDatum  : (datum : Either Nat Bool)                                                        → LsrcExpression
    VarRef      : (var-name : Name)                                                                → LsrcExpression
    Default     : (adt-type : LsrcType)                                                            → LsrcExpression 
    Sel         : (expr0 expr1 expr2 : LsrcExpression)                                             → LsrcExpression
    EltRef      : (expr : LsrcExpression) (elt-name : Name)                                        → LsrcExpression 
    EltCall     : (expr : LsrcExpression) (elt-name : Name) (expr* : List LsrcExpression)          → LsrcExpression
    Vector      : (expr* : List LsrcExpression)                                                    → LsrcExpression 
    VectorRef  : (expr : LsrcExpression) (nat : Nat)                                               → LsrcExpression
    _:+_        : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:-_        : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:*_        : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    Or          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    And         : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    Not         : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:<_        : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:<=_       : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:>_        : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:>=_       : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:==_       : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    _:!=_       : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    Map         : (fun : LsrcFunction) (expr : LsrcExpression) (expr* : List LsrcExpression)       → LsrcExpression
    Fold        : (fun : LsrcFunction) (expr0 expr : LsrcExpression) (expr* : List LsrcExpression) → LsrcExpression
    Call        : (fun : LsrcFunction) (expr* : List LsrcExpression) → LsrcExpression
    New         : (tref : Name) (expr* : List LsrcExpression) → LsrcExpression
    Seq         : (expr* : List LsrcExpression) (expr : LsrcExpression) → LsrcExpression
    Void        : LsrcExpression
    Cast        : (type : LsrcType) (expr : LsrcExpression) → LsrcExpression 

  data LsrcFunction : Set where
    Fref    : (function-name : Name) (targ* : List LsrcTypeArgument) → LsrcFunction
    AnonymousCircuit : (arg* : List LsrcArgument ) (type : LsrcType) (stmt : LsrcStatement) → LsrcFunction 

  {-
    ## TYPES ## 
  -} 

  data LsrcType : Set where
    Tref       : (tref : LsrcTypeRef)                     → LsrcType
    Tboolean   :                                            LsrcType
    Tfield     :                                            LsrcType
    Tunsigned  : (tsize : LsrcTypeSize)                   → LsrcType
    Tunsigned1 : (tsize tsize^ : LsrcTypeSize)            → LsrcType
    Tbytes     : (tsize : LsrcTypeSize)                   → LsrcType
    Topaque    : (opaque-type : Name)                     → LsrcType
    Tvector    : (tsize : LsrcTypeSize) (type : LsrcType) → LsrcType
    Tvoid      :                                            LsrcType

  data LsrcTypeRef : Set where
    TypeRef : (tvar-name : Name) (targ* : List LsrcTypeArgument) → LsrcTypeRef

  data LsrcTypeSize : Set where
    SizeNat    : (nat : Nat)             → LsrcTypeSize
    TypeSizeRef : (tsize-name : Name) → LsrcTypeSize

  data LsrcTypeArgument : Set where
    -- Called `quote` in `lang.ss`, but that's a protected name in Agda 
    TargNat : (nat : Nat)       → LsrcTypeArgument
    TargType      : (type : LsrcType) → LsrcTypeArgument


{-
  Defines and registers Lsrc as an IR used by the compiler 
-}

open import Language.Syntax.IR

lsrc : List _
lsrc =
   quote Name
 ∷ quote LsrcProgram
 ∷ quote LsrcProgramElement
 ∷ quote LsrcInclude
 ∷ quote LsrcModuleDefinition
 ∷ quote LsrcImportDeclaration
 ∷ quote LsrcExportDeclaration
 ∷ quote LsrcLedgerDeclaration
 ∷ quote LsrcLedgerConstructor
 ∷ quote LsrcCircuitDefinition
 ∷ quote LsrcExternalDeclaration
 ∷ quote LsrcWitnessDeclaration
 ∷ quote LsrcExternalContractDeclaration
 ∷ quote LsrcExternalContractCircuit
 ∷ quote LsrcStructureDefinition
 ∷ quote LsrcEnumDefinition
 ∷ quote LsrcPublicLedgerAdt
 ∷ quote LsrcPublicLedgerAdtArg
 ∷ quote LsrcPublicLedgerAdtType
 ∷ quote LsrcTypeParam
 ∷ quote LsrcArgument
 ∷ quote LsrcStatement
 ∷ quote LsrcExpression
 ∷ quote LsrcFunction
 ∷ quote LsrcType
 ∷ quote LsrcTypeRef
 ∷ quote LsrcTypeSize
 ∷ quote LsrcTypeArgument 
 ∷ []
 
unquoteDecl = registerIR lsrc
  
