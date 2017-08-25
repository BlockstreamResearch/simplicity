{-# LANGUAGE GADTs, TypeOperators, DeriveTraversable #-}
module Simplicity.Ty
 ( TyC, reify, reifyProxy, reifyArrow
 , TyReflect(..)
 , equalTyReflect
 , TyF(..), Ty
 , one, sum, prod
 , unreflect
 ) where

import Control.Unification.Types (Unifiable, zipMatch)
import Data.Functor.Fixedpoint (Fix(..))
import Data.Type.Equality ((:~:)(Refl))
import Prelude hiding (sum, prod)

-- By not exporting the reify_ method, TyC becomes a "closed class" and no further instances can be made.
class (Eq a, Ord a, Read a, Show a) => TyC a where
  reify_ :: TyReflect a

instance TyC () where
  reify_ = OneR

instance (TyC a, TyC b) => TyC (Either a b) where
  reify_ = SumR reify_ reify_

instance (TyC a, TyC b) => TyC (a, b) where
  reify_ = ProdR reify_ reify_

reify :: TyC a => TyReflect a
reify = reify_

reifyProxy :: TyC a => proxy a -> TyReflect a
reifyProxy _ = reify

reifyArrow :: (TyC a, TyC b) => proxy a b -> (TyReflect a, TyReflect b)
reifyArrow _ = (reify, reify)

data TyReflect a where
  OneR :: TyReflect ()
  SumR  :: (TyC a, TyC b) => TyReflect a -> TyReflect b -> TyReflect (Either a b)
  ProdR :: (TyC a, TyC b) => TyReflect a -> TyReflect b -> TyReflect (a, b)

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

unreflect :: TyReflect a -> Ty
unreflect OneR = one
unreflect (SumR a b) = sum (unreflect a) (unreflect b)
unreflect (ProdR a b) = prod (unreflect a) (unreflect b)

instance Unifiable TyF where
  zipMatch One One = Just One
  zipMatch (Sum a1 b1) (Sum a2 b2) = Just (Sum (Right (a1, a2)) (Right (b1, b2)))
  zipMatch (Prod a1 b1) (Prod a2 b2) = Just (Prod (Right (a1, a2)) (Right (b1, b2)))
  zipMatch _ _ = Nothing
