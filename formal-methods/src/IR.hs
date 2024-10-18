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
import Data.Aeson.Encode.Pretty
import GHC.Generics hiding (D) 
import Data.Data
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Map qualified as Map 
import Debug.Trace
import Control.Monad
import Data.Char 
import Data.List qualified as L
import Debug.Trace

import Data.Time (getCurrentTime)
import Data.Time.Format (formatTime, defaultTimeLocale)

import qualified Data.ByteString.Lazy as BL

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Reader 

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

data Sort = Sort
  { name         :: String
  , constructors :: [Cons]
  } deriving (Generic , Show)

data Cons = Cons
  { consname :: String
  , args     :: [Argument]
  } deriving (Generic , Show)

data Argument = Argument
  { sort :: String
  } deriving (Generic , Show , Eq)

data IR = IR
  { irName :: String
  , sorts  :: [Sort]
  } deriving (Generic , Show) 

instance ToJSON Argument where 
instance ToJSON Cons where
instance ToJSON Sort where
instance ToJSON IR where 

getName :: D -> String
getName (D x) = dataTypeName (dataTypeOf x)

getConstructors :: D -> [Cons]
getConstructors d =
  map
    (\c ->
      Cons
        (show c)
        ( map
            (\d ->
              Argument (getName d)
            ) (constrArgs d c)
        )
    ) $ allConstrs d

getSort :: Data a => Tag a -> Sort
getSort (MkTag :: Tag a) = let d = mkD (MkTag :: Tag a) in 
  Sort (getName d) (getConstructors d)

serialize :: FilePath -> IR -> IO ()
serialize fp ir = do
  let bytestr = encodePretty ir
  BL.writeFile (irName ir ++ ".json") bytestr 

infixr 8 :.: 
data SExpr = Atom String
           | SExpr :.: SExpr
           | Nil 
           deriving Show 

type Err = String

data Context = Context
  { metavars  :: Map.Map String String
  , terminals :: [String]
  , connames  :: [String] 
  }
  deriving Show

isTerminal :: MonadState Context m => String -> m Bool
isTerminal str = do
  ctx <- get
  return (str `elem` terminals ctx)

registerMetavar :: MonadState Context m => String -> String -> m ()
registerMetavar k v = do
  ctx <- get
  put (Context (Map.insert k v (metavars ctx)) (terminals ctx) (connames ctx)) 

addCName :: MonadState Context m => String -> m ()
addCName n = do
  ctx <- get
  put (Context (metavars ctx) (terminals ctx) (n:connames ctx))

forgetCNames :: MonadState Context m => m ()
forgetCNames = do
  ctx <- get 
  put (Context (metavars ctx) (terminals ctx) [])

-- | Reads a JSON value as an S expression 
jsonToSExpr :: MonadError Err m =>  Value -> m SExpr 
jsonToSExpr (String x)  = return $ Atom (T.unpack x)
jsonToSExpr (Array arr) = case V.toList arr of
  []     -> return Nil 
  (x:xs) -> do
    l <- jsonToSExpr x
    r <- jsonToSExpr (Array (V.fromList xs))
    return (l :.: r)
jsonToSExpr _ = throwError $
  "Only arrays and strings can be represented as S expressions." 

-- | Converts an S-expression generated from a NanoPass IR to an IR as defined above.
sExprToIR :: (MonadState Context m , MonadError Err m) => SExpr -> m IR 
sExprToIR (Atom "define-language" :.: (Atom irName :.: s)) =
   IR
     <$> return irName
     <*> sExprToSorts s

sExprToArgs :: (MonadState  Context m , MonadError Err m) => SExpr -> m [Argument]
sExprToArgs (Atom x)   = throwError $
   "Found an atom while attempting to convert S expression to argument"
sExprToArgs Nil        = return []
sExprToArgs (s :.: ss) = (:) <$> convertArg s <*> sExprToArgs ss
  where
    convertArg :: (MonadState  Context m , MonadError Err m) => SExpr -> m Argument
    convertArg (Atom aname)                        = return (Argument aname)
    convertArg (Atom aname :.: Atom "..." :.: Nil) = return (Argument aname) 
    convertArg _                                   = throwError $
      "Unexpected structure of S expression while attempting to convert to argument"

sExprToConstructors :: (MonadState  Context m , MonadError Err m) => SExpr -> m [Cons]
sExprToConstructors (Atom x)   = throwError
  "Found an atom while attempting to convert S expression to constructor"
sExprToConstructors Nil        = return []
sExprToConstructors (s :.: ss) = do
  x <- convertCons s
  xs <- sExprToConstructors ss
  return (x:xs)
  where
    convertCons :: (MonadState  Context m , MonadError Err m) => SExpr -> m Cons
    convertCons (Atom cname :.: args) = do 
      x <- isTerminal cname
      
      -- If the first atom in the list is a terminal, we treat it
      -- as an unnamed constructor 
      if x then
        Cons
          <$> return "unnamed"
          <*> sExprToArgs (Atom cname :.: args)
          
      -- Otherwise, use the profided name. However, we'll add a suffix if
      -- the same constructor name has been used before in the current
      -- sort definition 
      else
        do usedNames <- connames <$> get
           let suffix =
                 if cname `elem` usedNames then
                   show (length $ filter (==cname) usedNames)
                 else
                   ""
           addCName cname 
           Cons
            <$> return (cname <> suffix) 
            <*> sExprToArgs args
    convertCons (Atom cname)          = return $ Cons cname [] 
    convertCons s                     = throwError (show s) 

sExprToTerminals :: MonadError Err m =>  SExpr -> m [String]
sExprToTerminals (Atom "terminals" :.: ts) = convertTerminals ts
  where
    convertSymbols :: (MonadError Err m) => SExpr -> m [String] 
    convertSymbols (Atom tm :.: ts) =
      (:)
        <$> return tm
        <*> convertSymbols ts 
    convertSymbols Nil              = return []
    convertSymbols _                = throwError $
      "Unexpected structure of S expression while attempting to convert terminal list" 
    
    convertCls :: (MonadError Err m) => SExpr -> m [String]
    convertCls (Atom cls :.: ts :.: Nil) = convertSymbols ts 
    convertCls _                         = throwError $
      "Unexpected structure of S expression while attempting to convert terminal grouping"  
    
    convertTerminals :: (MonadError Err m) => SExpr -> m [String]
    convertTerminals (Atom x)   = throwError $
      "Found an atom while attempting to convert S expression to terminal list"
    convertTerminals Nil        = return []
    convertTerminals (s :.: ss) =
      (++)
        <$> convertCls s
        <*> convertTerminals ss
        
sExprToTerminals _                         = 
  throwError "Unexpected structure of S expression while converting terminal section" 

sExprToSorts :: (MonadState Context m , MonadError Err m) => SExpr -> m [Sort]
sExprToSorts (s :.: terminals :.: sorts) = do
  ctx <- get
  ts  <- sExprToTerminals terminals
  put ( Context
          { metavars  = metavars ctx
          , terminals = ts
          , connames  = connames ctx
          } )   
  convertSorts sorts
  
  where
    convertSort :: (MonadState Context m , MonadError Err m) => SExpr -> m (Sort)
    convertSort (Atom sname :.: (Atom metavar :.: Nil) :.: constructors) = do
      registerMetavar metavar sname
      s <- Sort
        <$> return sname
        <*> sExprToConstructors constructors
      forgetCNames
      return s
    
    convertSorts :: (MonadState Context m , MonadError Err m) => SExpr -> m [Sort]
    convertSorts (Atom x)   = throwError $
      "Found an atom while attempting to convert S expression to Sort"
    convertSorts Nil        = return []
    convertSorts (s :.: ss) =
      (:)
        <$> convertSort  s
        <*> convertSorts ss
        
sExprToSorts _ = throwError $
  "Found an S expression with unexpected structure when attempting to convert to IR"

-- | filter arguments from an IR representation based on the given list of predicates 
dropArgs :: [Argument -> Bool] -> IR -> IR
dropArgs ps (IR iname sorts) = IR iname (map dropFromSort sorts)
  where
    dropFromCons :: Cons -> Cons
    dropFromCons (Cons cname args) =
      Cons cname (filter (not . or . flip map ps . flip ($)) args)
    
    dropFromSort :: Sort -> Sort
    dropFromSort (Sort sname cs) =
      Sort sname (map dropFromCons cs)

-- | transform arguments from an IR representation based on the given
--   list of transformations
transformArgs :: [Argument -> Argument] -> IR -> IR
transformArgs ts (IR iname sorts) =
  IR iname (map transformSort sorts)
  where
    transformCons :: Cons -> Cons
    transformCons (Cons cname args) =
      Cons cname (map (foldr (.) id ts) args)

    transformSort :: Sort -> Sort
    transformSort (Sort sname cs) =
      Sort sname (map transformCons cs)

transformCons :: [Cons -> Cons] -> IR -> IR
transformCons ts (IR iname sorts) =
  IR iname (map transformSort sorts)
  where
    transformSort :: Sort -> Sort
    transformSort (Sort sname cs) =
      Sort sname (map (foldr (.) id ts) cs) 

loadJSON :: FilePath -> IO (Either String Value)
loadJSON = eitherDecodeFileStrict

lookupMetavar :: Context -> String -> Maybe String
lookupMetavar ctx str = let x = last str in
  if isDigit x || x == '*' || x == '^' then 
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
          let ir' =
                ( transformCons consTransform
                  $ transformArgs (argTransform ctx)
                  $ dropArgs argFilters ir
                )
          putStrLn $ show ctx 
          generateAgdaModule ir' 
      
  where
    readIR :: Value -> Either Err (IR , Context) 
    readIR value =
      runIdentity $
        runExceptT $
          runStateT
            (jsonToSExpr value >>= sExprToIR)
            (Context Map.empty [] []) 

    -- Defines which "arguments" should be filtered from the IR after
    -- reading the S-expression.
    argFilters :: [Argument -> Bool]
    argFilters = 
      [ (==) "src" . sort 
      , (==) "..." . sort 
      ]

    -- Defines which transformations oucht to be applied to the argument names
    -- **after** filtering
    --
    -- Transformations are applied top-to-bottom; it's up to us to
    -- ensure they're applied in the right order if they don't commute
    -- (which they likely will)
    argTransform :: Context -> [Argument -> Argument]
    argTransform ctx = reverse $
      
      [ -- Lookup metavariables and replace with corresponding sort name
        \arg@(Argument str) ->
          maybe arg Argument (lookupMetavar ctx str)

        -- Replace arguments with postfix '?' with `Bool` 
      , \arg@(Argument str) ->
          if last str == '?' then
            Argument "Bool"
          else
            arg

        -- Mark arguments ending with '*' as lists
      , \arg@(Argument str) ->
          if last str == '*' then
            Argument ("List " ++ init str)
          else
            arg

        -- Mark arguments ending with '^' as Optional
      , \arg@(Argument str) ->
          if last str == '^' then
            Argument ("Maybe " ++ init str)
          else
            arg

        -- Mark arguments that contain the word "name" as strings 
      , \arg@(Argument str) ->
          if "name" `L.isInfixOf` str then
            Argument "String"
          else
            arg

      , \arg@(Argument str) ->
          if str == "nat" then
            Argument "ℕ"
          else
            arg
      
        -- Drop postfix numbering, e.g., in `expr1` 
      , \arg@(Argument str) ->
          if isDigit (last str) then
            Argument (init str)
          else
            arg

         -- Replace known terminals 
      ,  \arg@(Argument str) ->
          maybe arg Argument (lookup str terminals)   
      ]
      where
        terminals :: [(String , String)]
        terminals =
          [ ("opaque-type" , "String")
          , ("datum"       , "ℕ ⊎ Bool")
          , ("pure-dcl"    , "Bool")
          , ("mesg"        , "String")
          , ("file"        , "String")
          , ("prefix"      , "String") 
          ] 
      
    consTransform :: [Cons -> Cons]
    consTransform = reverse $

      [ -- Add a prime to the names of constructors that are protected names in agda
        \cons@(Cons cname args) ->
          if cname `elem` protectedNames then
            Cons (cname <> "′") args
          else
            cons
            
      ]
      where
        protectedNames :: [String]
        protectedNames =
          [ "constructor"
          , "quote"
          , "import"
          , "module"
          , "="
          ]

       

type AgdaCode = String

constructorToAgda ::
  ( MonadReader String m
  , MonadWriter AgdaCode m
  , MonadState Int m 
  ) => Cons -> m ()
constructorToAgda cons = do
  dt   <- ask
  let as = map sort (args cons)
  let ty = foldr (\a t -> a <> " -> " <> t) "" as  
  line $ consname cons <> " : " <> ty <> dt 
  
sortToAgda ::
  ( MonadWriter AgdaCode m
  , MonadState Int m 
  ) => Sort -> m ()
sortToAgda sort = do 
  line $ "data " <> name sort <> " : Set where"
  indent $
    mapM_ (flip runReaderT (name sort) . constructorToAgda) (constructors sort)
  tell "\n" 
  
-- | Emits a single line of code 
line ::
  ( MonadWriter AgdaCode m
  , MonadState Int m 
  ) => AgdaCode -> m ()
line code = do
  l <- get
  tell $ (replicate (2*l) ' ') <> code <> "\n" 

-- | automatically prepends all calls to the `line` function in the
-- given computation
indent ::
  (  MonadWriter AgdaCode m
  , MonadState Int m
  ) => m () -> m ()
indent m = do
  l <- get
  put (l + 1) 
  m 
  put l 

irToAgda ::
  ( MonadWriter String m
  , MonadState Int m 
  ) => IR -> m () 
irToAgda ir = do
  line  $ "module " <> irName ir <> " where" 
  indent $ do 
    line "mutual" 
    indent $ do
      mapM_ sortToAgda (sorts ir) 

generateAgdaModule :: IR -> IO ()
generateAgdaModule ir = do
  time <- getCurrentTime
  let timeStr  = formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" time
  let hdr =    "-- ***\n" 
            <> "-- *** The language definition in this file was automatically generated from the "
               <> irName ir <> " Nanopass IR\n"
            <> "-- *** \n" 
            <> "-- *** TIMESTAMP: " <> timeStr <> " \n"
            <> "-- *** \n"
            <> "\n"
            <> "open import Data.String using (String) \n"
            <> "open import Data.List   using (List) \n"
            <> "open import Data.Bool   using (Bool)\n"
            <> "open import Data.Nat    using (ℕ)\n"
            <> "open import Data.Sum    using (_⊎_)\n"
            <> "open import Data.Maybe  using (Maybe)\n" 
            <> "\n" 
  let ((() , _) , code) = runIdentity (runWriterT $ runStateT (irToAgda ir) 0)
  writeFile (irName ir <> ".agda") (hdr <> code) 

-- We define equivalence of IRs as follows:
--
-- IRs are essentialy defined as a list of sorts. We say that two IRs
-- are equivalent if they (1) define the same sorts, up to permutation,
-- and (2) each matching sort is equivalent.
--
-- Similarly, sorts are defined as lists of constructors. We say that
-- two sorts are equivalent if they (1) define the same constructors,
-- up to permutation, and (2) each matching constructor is equivalent.
--
-- Constructors are defined as lists of arguments. We say that two
-- constructors are equivalent if they have the same arguments, up to
-- permutation.
--
-- Comparison between IRs is mostly nominal, which requires some
-- pre-processing before we can compare the definitions emitted
-- respectively from the compiler and the specification. 
--

-- | Compares two sorts for equivalence, throwing an error if a
--   deiscrepancy is found.
compareSort :: MonadError Err m => Sort -> Sort -> m ()
compareSort s1 s2 = return () 

-- | Compares two IRs for equivalence, throwing an error if a
--   discrepancy is found.
compareIR :: MonadError Err m => IR -> IR -> m () 
compareIR ir1 ir2 = do
  if irName ir1 == irName ir2 then
    let snames1 = map name (sorts ir1) in
    let snames2 = map name (sorts ir2) in

    -- Check if both IRs consist of the same sorts (up to permutation) 
    if L.sort snames1 == L.sort snames2 then
      mapM_ (\n -> do
         -- IRs pointwise by comparing sorts 
         s1 <- lookupSort n ir1
         s2 <- lookupSort n ir2
         compareSort s1 s2 
       ) snames1 
    else
      throwError $
        "Sort mismatch while comparing IRs. l: "
        ++ show snames1 ++ ", r: " ++ show snames2  
  else
    throwError $
      "Name mismatch while comparing IRs: "
      ++ irName ir1 ++ " /= " ++ irName ir2  
  where 
    lookupSort :: MonadError Err m => String -> IR -> m Sort
    lookupSort n ir = 
      case L.find (\s -> name s == n) (sorts ir) of 
        (Just s) -> return s
        Nothing  -> throwError $
          "Sort lookup failed for key: " ++ n 
