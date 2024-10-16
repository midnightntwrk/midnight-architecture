{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DeriveDataTypeable #-} 
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-} 

module IR  where

import Data.Char qualified as Char
import Data.Aeson
import GHC.Generics hiding (D) 
import Data.Data
import Data.Text qualified as T
import Data.Vector qualified as V
import Language.Haskell.TH
import Data.Map qualified as Map 
import Debug.Trace
import Control.Monad
import Data.Char 
import Data.List (isInfixOf) 

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity 

data Tag a = MkTag

data D = forall a. Data a => D a

allConstrArgs :: D -> [[D]]
allConstrArgs d = constrArgs d <$> allConstrs d

constrArgs :: D -> Constr -> [D]
constrArgs (D a) c = gmapQ D $ mkConstr a c
    where
        mkConstr :: forall a. Data a => a -> Constr -> a
        mkConstr _ = fromConstr

allConstrs :: D -> [Constr]
allConstrs (D a) = case dataTypeRep $ dataTypeOf a of
    AlgRep constrs -> constrs
    _ -> []

mkD :: forall a. Data a => Tag a -> D
mkD _ = D (undefined :: a)

data Sort        = Sort { name :: String , constructors :: [Cons] } deriving (Generic , Show)
data Cons        = Cons { consname :: String , args :: [Argument] } deriving (Generic , Show)
data Argument    = Argument { sort :: String }                      deriving (Generic , Show , Eq)
data IR          = IR { irName :: String , sorts :: [Sort] }        deriving (Generic , Show) 

instance ToJSON Argument where 
instance ToJSON Cons where
instance ToJSON Sort where
instance ToJSON IR where 

getName :: D -> String
getName (D x) = dataTypeName (dataTypeOf x)

getConstructors :: D -> [Cons]
getConstructors d = map (\c -> Cons (show c) (map (\d -> Argument (getName d)) (constrArgs d c)))  $ allConstrs d

getSort :: Data a => Tag a -> Sort
getSort (MkTag :: Tag a) = let d = mkD (MkTag :: Tag a) in 
  Sort (getName d) (getConstructors d)

serialize :: FilePath -> IR -> IO ()
serialize = encodeFile 

infixr 8 :.: 
data SExpr = Atom String
           | SExpr :.: SExpr
           | Nil 
           deriving Show 

type Err = String

data Context = Context
  { metavars  :: Map.Map String String
  , terminals :: [String]
  }
  deriving Show

isTerminal :: MonadState Context m => String -> m Bool
isTerminal str = do
  ctx <- get
  return (str `elem` terminals ctx)

registerMetavar :: MonadState Context m => String -> String -> m ()
registerMetavar k v = do
  ctx <- get
  put (Context (Map.insert k v (metavars ctx)) (terminals ctx)) 

-- | Reads a JSON value as an S expression 
jsonToSExpr :: MonadError Err m =>  Value -> m SExpr 
jsonToSExpr (String x)  = return $ Atom (T.unpack x)
jsonToSExpr (Array arr) = case V.toList arr of
  []     -> return Nil 
  (x:xs) -> do
    l <- jsonToSExpr x
    r <- jsonToSExpr (Array (V.fromList xs))
    return (l :.: r)
jsonToSExpr _ = throwError "Only arrays and strings can be represented as S expressions." 

-- | Converts an S-expression generated from a NanoPass IR to an IR as defined above.
sExprToIR :: (MonadState Context m , MonadError Err m) => SExpr -> m IR 
sExprToIR (Atom "define-language" :.: (Atom irName :.: s)) = IR <$> return irName <*> sExprToSorts s

sExprToArgs :: (MonadState  Context m , MonadError Err m) => SExpr -> m [Argument]
sExprToArgs (Atom x)   = throwError "Found an atom while attempting to convert S expression to argument"
sExprToArgs Nil        = return []
sExprToArgs (s :.: ss) = (:) <$> convertArg s <*> sExprToArgs ss
  where
    convertArg :: (MonadState  Context m , MonadError Err m) => SExpr -> m Argument
    convertArg (Atom aname)                        = return (Argument aname)
    convertArg (Atom aname :.: Atom "..." :.: Nil) = return (Argument aname) 
    convertArg _                                   =
      throwError  "Unexpected structure of S expression while attempting to convert to argument"

sExprToConstructors :: (MonadState  Context m , MonadError Err m) => SExpr -> m [Cons]
sExprToConstructors (Atom x)   = throwError "Found an atom while attempting to convert S expression to constructor"
sExprToConstructors Nil        = return []
sExprToConstructors (s :.: ss) = (:) <$> convertCons s <*> sExprToConstructors ss 
  where
    convertCons :: (MonadState  Context m , MonadError Err m) => SExpr -> m Cons
    convertCons (Atom cname :.: args) = do
      x <- isTerminal cname
      if x then
        Cons <$> return "unnamed" <*> sExprToArgs (Atom cname :.: args)
      else
        Cons <$> return cname <*> sExprToArgs args
    convertCons (Atom cname)          = return $ Cons cname [] 
    convertCons s                     = throwError (show s) 

sExprToTerminals :: MonadError Err m =>  SExpr -> m [String]
sExprToTerminals (Atom "terminals" :.: ts) = convertTerminals ts
  where
    convertSymbols :: (MonadError Err m) => SExpr -> m [String] 
    convertSymbols (Atom tm :.: ts) = (:) <$> return tm <*> convertSymbols ts 
    convertSymbols Nil              = return []
    convertSymbols _                = 
      throwError "Unexpected structure of S expression while attempting to convert terminal list" 
    
    convertCls :: (MonadError Err m) => SExpr -> m [String]
    convertCls (Atom cls :.: ts :.: Nil) = convertSymbols ts 
    convertCls _                         =
      throwError "Unexpected structure of S expression while attempting to convert terminal grouping"  
    
    convertTerminals :: (MonadError Err m) => SExpr -> m [String]
    convertTerminals (Atom x)   = throwError "Found an atom while attempting to convert S expression to terminal list"
    convertTerminals Nil        = return []
    convertTerminals (s :.: ss) = (++) <$> convertCls s <*> convertTerminals ss 
sExprToTerminals _                         = 
  throwError "Unexpected structure of S expression while converting terminal section" 

sExprToSorts :: (MonadState Context m , MonadError Err m) => SExpr -> m [Sort]
sExprToSorts (s :.: terminals :.: sorts) = do
  ctx <- get
  ts  <- sExprToTerminals terminals
  put (Context { metavars = metavars ctx , terminals = ts })   
  convertSorts sorts
  
  where
    convertSort :: (MonadState Context m , MonadError Err m) => SExpr -> m (Sort)
    convertSort (Atom sname :.: (Atom metavar :.: Nil) :.: constructors) = do
      registerMetavar metavar sname
      Sort <$> return sname <*> sExprToConstructors constructors
    
    convertSorts :: (MonadState Context m , MonadError Err m) => SExpr -> m [Sort]
    convertSorts (Atom x)   = throwError "Found an atom while attempting to convert S expression to Sort"
    convertSorts Nil        = return []
    convertSorts (s :.: ss) = (:) <$> convertSort s <*> convertSorts ss
sExprToSorts _ = throwError "Found an S expression with unexpected structure when attempting to convert to IR"

-- | filter arguments from an IR representation based on the given list of predicates 
dropArgs :: [Argument -> Bool] -> IR -> IR
dropArgs ps (IR iname sorts) = IR iname (map dropFromSort sorts)
  where
    dropFromCons :: Cons -> Cons
    dropFromCons (Cons cname args) = Cons cname (filter (not . or . flip map ps . flip ($)) args)
    
    dropFromSort :: Sort -> Sort
    dropFromSort (Sort sname cs) = Sort sname (map dropFromCons cs)

-- | transform arguments from an IR representation based on the given list of transformations 
transformArgs :: [Argument -> Argument] -> IR -> IR
transformArgs ts (IR iname sorts) = IR iname (map transformSort sorts)
  where
    transformCons :: Cons -> Cons
    transformCons (Cons cname args) = Cons cname (map (foldr (.) id ts) args)

    transformSort :: Sort -> Sort
    transformSort (Sort sname cs) = Sort sname (map transformCons cs)

loadJSON :: FilePath -> IO (Either String Value)
loadJSON = eitherDecodeFileStrict

lookupMetavar :: Context -> String -> Maybe String
lookupMetavar ctx str = let x = last str in
  if isDigit x || x == '*' then 
    (++[x]) <$> Map.lookup (init str) (metavars ctx) 
  else
    Map.lookup str (metavars ctx) 
  
load :: IO ()
load = do
  result <- loadJSON "lsrc.json"
  case result of 
    (Left err)  -> do
      putStrLn "Failed to load IR representation"
      putStrLn err
    (Right val) -> do 
      case readIR val of
        (Left err)  -> do
          putStrLn "Faild to convert JSON to IR"
          putStrLn err
        (Right (ir , ctx)) -> do
          putStrLn (show ctx) 
          serialize "lsrc-np.json" (transformArgs (argTransform ctx) $ dropArgs argFilters ir)
      
  where
    readIR :: Value -> Either Err (IR , Context) 
    readIR value = runIdentity $ runExceptT $ runStateT (jsonToSExpr value >>= sExprToIR) (Context Map.empty []) 

    -- Defines which "arguments" should be filtered from the IR after reading the S-expression. 
    argFilters :: [Argument -> Bool]
    argFilters = 
      [ (==) "src" . sort 
      , (==) "..." . sort 
      ]

    -- Defines which transformations oucht to be applied to the IR **after** filtering
    --
    -- Transformations are applied top-to-bottom; it's up to us to
    -- ensure they're applied in the right order if they don't commute
    -- (which they likely will)
    argTransform :: Context -> [Argument -> Argument]
    argTransform ctx = reverse $
      
      [ -- Lookup metavariables and replace with corresponding sort name
        \arg@(Argument str) -> maybe arg Argument (lookupMetavar ctx str)

        -- Replace arguments with postfix '?' with `Bool` 
      , \arg@(Argument str) -> if last str == '?' then Argument "Bool" else arg

        -- Mark arguments ending with '*' as lists
      , \arg@(Argument str) -> if last str == '*' then Argument ("[" ++ init str ++ "]") else arg

        -- Mark arguments that contain the word "name" as strings 
      , \arg@(Argument str) -> if "name" `isInfixOf` str then Argument "String" else arg

        -- Drop postfix numbering, e.g., in `expr1` 
      , \arg@(Argument str) -> if isDigit (last str) then Argument (init str) else arg 
      ] 
