{-# LANGUAGE GADTs, TypeOperators, DeriveTraversable #-}
module Simplicity.Ty
 ( TyF(..), Ty
 , one, sum, prod
 , TyReflect(..)
 , equalTyReflect
 ) where

import Control.Unification.Types (Unifiable, zipMatch)
import Data.Functor.Fixedpoint (Fix(..))
import Data.Type.Equality ((:~:)(Refl))
import Prelude hiding (sum, prod)

data TyF a = One
           | Sum a a
           | Prod a a 
           deriving (Eq, Functor, Foldable, Traversable)

type Ty = Fix TyF

one :: Ty
one = Fix One

sum :: Ty -> Ty -> Ty
sum a b = Fix $ Sum a b

prod :: Ty -> Ty -> Ty
prod a b = Fix $ Prod a b

instance Unifiable TyF where
  zipMatch One One = Just One
  zipMatch (Sum a1 b1) (Sum a2 b2) = Just (Sum (Right (a1, a2)) (Right (b1, b2)))
  zipMatch (Prod a1 b1) (Prod a2 b2) = Just (Prod (Right (a1, a2)) (Right (b1, b2)))
  zipMatch _ _ = Nothing

data TyReflect a where
  OneR :: TyReflect ()
  SumR  :: TyReflect a -> TyReflect b -> TyReflect (Either a b)
  ProdR :: TyReflect a -> TyReflect b -> TyReflect (a, b)

equalTyReflect :: TyReflect a -> TyReflect b -> Maybe (a :~: b)
equalTyReflect OneR OneR = return Refl
equalTyReflect (SumR a1 b1) (SumR a2 b2) = do
  Refl <- equalTyReflect a1 a2
  Refl <- equalTyReflect b1 b2
  return Refl
equalTyReflect (ProdR a1 b1) (ProdR a2 b2) = do
  Refl <- equalTyReflect a1 a2
  Refl <- equalTyReflect b1 b2
  return Refl
equalTyReflect _ _ = Nothing
