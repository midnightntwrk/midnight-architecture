{- Based on l58 and onwards of `lang.ss` (compiler source) -} 

open import Data.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Bool using (Bool)
open import Data.Product using (_×_)

module Language.Syntax.Lsrc where 

mutual
  data LsrcProgram : Set where
    elems : (peltl* : List LsrcProgramElement) → LsrcProgram 

  data LsrcProgramElement : Set where
    incld        : (incld : LsrcInclude) → LsrcProgramElement
    mdefn        : (mdefn : LsrcModuleDefinition) → LsrcProgramElement
    idecl        : (idecl : LsrcImportDeclaration) → LsrcProgramElement
    xdecl        : (xdecl : LsrcExportDeclaration) → LsrcProgramElement
    ldecl        : (ldecl : LsrcLedgerDeclaration) → LsrcProgramElement
    lconstructor : (lconstructor : LsrcLedgerConstructor) → LsrcProgramElement
    cdefn        : (cdefn : LsrcCircuitDefinition) → LsrcProgramElement
    edecl        : (edecl : LsrcExternalDeclaration) → LsrcProgramElement
    wdecl        : (wdecl : LsrcWitnessDeclaration) → LsrcProgramElement 
    ecdecl       : (ecdecl : LsrcExternalContractDeclaration) → LsrcProgramElement
    structdef    : (structdef : LsrcStructureDefinition) → LsrcProgramElement
    enumdef      : (enumdef : LsrcEnumDefinition) → LsrcProgramElement 

  data LsrcInclude : Set where
    include : (file : String) → LsrcInclude

  data LsrcModuleDefinition : Set where
    module′ : ( exported?   : Bool )
              ( module-name : String )
              ( type-param* : List LsrcTypeParam )
              ( pelt*       : List LsrcProgramElement )
            → LsrcModuleDefinition

  data LsrcImportDeclaration : Set where
    import′ : ( module-name : String )
              ( targ*       : LsrcTypeArgument )
              ( prefix      : String ) -- Q: is this right?
            → LsrcImportDeclaration 

  data LsrcExportDeclaration : Set where
    export : (name* : List String) → LsrcExportDeclaration

  data LsrcLedgerDeclaration : Set where
    public-ledger-declaration : ( exported?         : Bool )
                                ( sealed?           : Bool )
                                ( ledger-field-name : String )
                                ( public-adt        : LsrcPublicLedgerADT )
                              → LsrcLedgerDeclaration

  data LsrcLedgerConstructor : Set where
    constructor′ : ( arg* : List (String × LsrcType) )
                   ( stmt : LsrcStatement ) 
                 → LsrcLedgerConstructor 

  data LsrcCircuitDefinition : Set where
    circuit : ( exported?     : Bool )
              ( pure-decl?    : Bool ) 
              ( function-name : String )
              ( type-param*   : List LsrcTypeParam )
              ( arg*          : List (String × LsrcType) )
              ( type          : LsrcType )
              ( stmt          : LsrcStatement )
            → LsrcCircuitDefinition

  data LsrcExternalDeclaration : Set where
    external : ( exported?     : Bool )
               ( function-name : String )
               ( type-param*   : List LsrcTypeParam )
               ( arg*          : List (String × LsrcType) )
               ( type          : LsrcType ) 
             → LsrcExternalDeclaration 

  data LsrcWitnessDeclaration : Set where
    witness : ( exported? : Bool )
              ( function-name : Bool )
              ( type-param*   : List LsrcTypeParam )
              ( arg*          : List (String × LsrcType) )
              ( type          : LsrcType )
            → LsrcWitnessDeclaration 

  data LsrcExternalContractDeclaration : Set where
    external-contract : ( exported?       : Bool )
                        ( contract-name   : String )
                        ( ecdecl-circuit* : List LsrcExternalContractCircuit )
                      → LsrcExternalContractDeclaration

  data LsrcExternalContractCircuit : Set where
    external-circuit : ( function-name : String )
                       ( arg*          : List (String × LsrcType) )
                       ( type          : LsrcType ) 
                     → LsrcExternalContractCircuit 
  
  
  data LsrcStructureDefinition : Set where
    struct : ( exported?   : Bool )
             ( struct-name : String )
             ( type-param* : List LsrcTypeParam )
             ( arg*        : List (String × LsrcType) )
           → LsrcStructureDefinition 

  data LsrcEnumDefinition : Set where
    enum : ( exported? : Bool )
           ( enum-name : String )
           ( elt-name  : String )
           ( elt-name*  : List String )
         → LsrcEnumDefinition

  data LsrcPublicLedgerADT : Set where
    adt-name : ( adt-name : String )
               ( adt-arg* : LsrcPublicLedgerADTArg )
             → LsrcPublicLedgerADT 

  data LsrcPublicLedgerADTArg : Set where
    nat      : (nat : ℕ) → LsrcPublicLedgerADTArg
    adt-type : (adt-type : LsrcPublicLedgerADTType) → LsrcPublicLedgerADTArg

  data LsrcPublicLedgerADTType : Set where
    type       : LsrcType → LsrcPublicLedgerADTType 
    public-adt : LsrcPublicLedgerADT → LsrcPublicLedgerADTType
  
  data LsrcTypeParam : Set where
    nat-valued  : (tvar-name : String) → LsrcTypeParam
    type-valued : (tvar-name : String) → LsrcTypeParam  

  {-
    ## EXPRESSIONS and STATEMENTS ## 
  -}
  data LsrcStatement : Set where
    statement-expression : LsrcExpression → LsrcStatement
    =′     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    +=     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    -=     : (expr1 expr2 : LsrcExpression) → LsrcStatement
    return : (expr : LsrcExpression) → LsrcStatement 
    assert : (expr : LsrcExpression) → (msg : String) → LsrcStatement
    const  : (var-name : String) (adt-type : LsrcPublicLedgerADTType) (expr : LsrcExpression) → LsrcStatement 
    if     : (expr : LsrcExpression) (stmt1 stmt2 : LsrcStatement) → LsrcStatement
    for    : (var-name : String) (expr : LsrcExpression) (stmt : LsrcStatement) → LsrcStatement
    block  : (stmt* : List LsrcStatement) → LsrcStatement 

  data LsrcExpression : Set where 
    quote-datum : (datum : ℕ ⊎ Bool)                                                               → LsrcExpression
    var-ref     : (var-name : String)                                                              → LsrcExpression
    default     : (adt-type : LsrcType)                                                            → LsrcExpression 
    if          : (expr0 expr1 expr2 : LsrcExpression)                                             → LsrcExpression
    -- elt-ref
    -- elt-call
    vector      : (expr* : List LsrcExpression)                                                    → LsrcExpression 
    vector-ref  : (expr : LsrcExpression) (nat : ℕ)                                                → LsrcExpression
    +           : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    -           : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    *           : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    or          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    and         : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    not         : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    <           : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    <=          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    >           : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    >=          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    ==          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    !=          : (expr1 expr2 : LsrcExpression)                                                   → LsrcExpression
    map         : (fun : LsrcFunction) (expr : LsrcExpression) (expr* : List LsrcExpression)       → LsrcExpression
    fold        : (fun : LsrcFunction) (expr0 expr : LsrcExpression) (expr* : List LsrcExpression) → LsrcExpression
    call        : (fun : LsrcFunction) (expr* : List LsrcExpression) → LsrcExpression
    new         : (tref : String) (expr* : List LsrcExpression) → LsrcExpression
    seq         : (expr* : List LsrcExpression) (expr : LsrcExpression) → LsrcExpression
    void        : LsrcExpression
    cast        : (type : LsrcType) (expr : LsrcExpression) → LsrcExpression 

  data LsrcFunction : Set where
    fref    : (function-name : String) (targ* : List LsrcTypeArgument) → LsrcFunction
    circuit : (arg* : List (String × LsrcType) ) (type : LsrcType) (stmt : LsrcStatement) → LsrcFunction 

  {-
    ## TYPES ## 
  -} 

  data LsrcType : Set where
    tref       : (tref : LsrcTypeRef)                     → LsrcType
    tboolean   :                                            LsrcType
    tfield     :                                            LsrcType
    tunsigned  : (tsize : LsrcTypeSize)                   → LsrcType
    tunsigned′ : (tsize tsize^ : LsrcTypeSize)            → LsrcType
    tbytes     : (tsize : LsrcTypeSize)                   → LsrcType
    topaque    : (opaque-type : String)                   → LsrcType
    tvector    : (tsize : LsrcTypeSize) (type : LsrcType) → LsrcType
    tvoid      :                                            LsrcType

  data LsrcTypeRef : Set where
    type-ref : (tvar-name : String) (targ* : List LsrcTypeArgument) → LsrcTypeRef

  data LsrcTypeSize : Set where
    quote-nat     : (nat : ℕ)             → LsrcTypeSize
    type-size-ref : (tsize-name : String) → LsrcTypeSize

  data LsrcTypeArgument : Set where
    -- Called `quote` in `lang.ss`, but that's a protected name in Agda 
    quote-nat : (nat : ℕ)         → LsrcTypeArgument
    type      : (type : LsrcType) → LsrcTypeArgument
