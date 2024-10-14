{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DeriveDataTypeable #-} 
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TemplateHaskell #-} 

module IR  where

import Data.Char qualified as Char
import Data.Aeson
import GHC.Generics hiding (D) 
import Data.Data
import Language.Haskell.TH

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
data Argument    = Argument { sort :: String }                      deriving (Generic , Show)

instance ToJSON Argument where 
instance ToJSON Cons where
instance ToJSON Sort where

getName :: D -> String
getName (D x) = dataTypeName (dataTypeOf x)

getConstructors :: D -> [Cons]
getConstructors d = map (\c -> Cons (show c) (map (\d -> Argument (getName d)) (constrArgs d c)))  $ allConstrs d

getSort :: Data a => Tag a -> Sort
getSort (MkTag :: Tag a) = let d = mkD (MkTag :: Tag a) in 
  Sort (getName d) (getConstructors d)

serialize :: FilePath -> [Sort] -> IO ()
serialize = encodeFile 
