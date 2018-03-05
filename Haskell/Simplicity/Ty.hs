{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, DeriveTraversable #-}
-- | This module provides representations of Simplicity types in Haskell.
--
-- The 'TyC' class captures those Haskell types that correspond to Simplicity types.
-- The 'Ty' data type is a value-level representation of Simplicity types.
-- The 'TyReflect' GADT links a value-level representation of Simplicity types with corresponding Haskell types.
module Simplicity.Ty
 ( TyC
 , TyReflect(..)
 , reify, reifyProxy, reifyArrow
 , equalTyReflect
 , Ty, TyF(..)
 , one, sum, prod
 , unreflect
 , memoCataTy
 ) where

import Prelude hiding (sum, prod)

import Control.Unification.Types (Unifiable, zipMatch)
import Data.Functor.Fixedpoint (Fix(..))
import Data.MemoTrie (HasTrie(..), memo)
import Data.Type.Equality ((:~:)(Refl))
import Lens.Family2 ((&), (%~))
import Lens.Family2.Stock (mapped, _1)

-- | 'TyC' is a type class for those Haskell types that correspond to Simplicity types;
-- specifically those composed from @()@, @'Either' a b@, and @(a, b)@.
-- The 'ClosedClass_' superclass isn't exported preventing further instances of 'TyC'.
class (ClosedClass_ a, Eq a, Ord a, Read a, Show a) => TyC a where

-- This class isn't exported, so subclasses of it cannot be instantiated outside this module.
class ClosedClass_ a where
  reify_ :: TyReflect a

instance TyC () where
instance ClosedClass_ () where
  reify_ = OneR

instance (TyC a, TyC b) => TyC (Either a b) where
instance (TyC a, TyC b) => ClosedClass_ (Either a b) where
  reify_ = SumR reify_ reify_

instance (TyC a, TyC b) => TyC (a, b) where
instance (TyC a, TyC b) => ClosedClass_ (a, b) where
  reify_ = ProdR reify_ reify_

-- | The 'TyReflect' GADT provides a link between Haskell types correspondng to Simplicity types (i.e. members of the 'TyC' class) and values that can be manipulated by Haskell programs.
--
-- There is a unique value of @'TyReflect' a@ for every @a@ that corresponds to a Simplicity type.
-- This value can be decomposed by pattern matching to get the (unique) values of 'TyRefect' that correspond to the components of the Simplicity type.
-- For example, the unique value of @'TyReflect' ('Either' () (), ())@ is @'ProdR' ('SumR' 'OneR' 'OneR') 'OneR'@.
data TyReflect a where
  OneR :: TyReflect ()
  SumR  :: (TyC a, TyC b) => TyReflect a -> TyReflect b -> TyReflect (Either a b)
  ProdR :: (TyC a, TyC b) => TyReflect a -> TyReflect b -> TyReflect (a, b)

-- | The unique 'TyReflect' value for any given 'TyC' type.
reify :: TyC a => TyReflect a
reify = reify_

-- | A helper function that use a proxy argument to help control the type infered for 'reify'.
reifyProxy :: TyC a => proxy a -> TyReflect a
reifyProxy _ = reify

-- | A helper function that use a proxy argument to help control the types infered for 'reify'.
reifyArrow :: (TyC a, TyC b) => proxy a b -> (TyReflect a, TyReflect b)
reifyArrow _ = (reify, reify)

-- | Decide if two 'TyReflect' values are equal or not, and if they are equal then unify their type variables.
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

-- | A Haskell data type for representing Simplicity types.
-- It uses an explicit 'Fix'edpoint of the 'TyF' functor.
type Ty = Fix TyF

-- | The functor used to define 'Ty' type.
data TyF a = One
           | Sum a a
           | Prod a a 
           deriving (Eq, Functor, Foldable, Traversable)

instance Unifiable TyF where
  zipMatch One One = Just One
  zipMatch (Sum a1 b1) (Sum a2 b2) = Just (Sum (Right (a1, a2)) (Right (b1, b2)))
  zipMatch (Prod a1 b1) (Prod a2 b2) = Just (Prod (Right (a1, a2)) (Right (b1, b2)))
  zipMatch _ _ = Nothing

-- | Construct the unit 'Ty' of Simplicity.
one :: Ty
one = Fix One

-- | Construct the sum 'Ty' of two 'Ty's.
sum :: Ty -> Ty -> Ty
sum a b = Fix $ Sum a b

-- | Construct the product 'Ty' of two 'Ty's.
prod :: Ty -> Ty -> Ty
prod a b = Fix $ Prod a b

-- | Covert a 'TyReflect' value the corresponding 'Ty' value.
unreflect :: TyReflect a -> Ty
unreflect OneR = one
unreflect (SumR a b) = sum (unreflect a) (unreflect b)
unreflect (ProdR a b) = prod (unreflect a) (unreflect b)

-- memoTyF and dememoTyF hare non-exported helper functions for the
-- HasTrie (TyF x) instance.
memoTyF :: Maybe (Bool, x, x) -> TyF x
memoTyF Nothing              = One
memoTyF (Just (False, a, b)) = Sum a b
memoTyF (Just (True, a, b))  = Prod a b

deMemoTyF :: TyF x -> Maybe (Bool, x, x)
deMemoTyF One        = Nothing
deMemoTyF (Sum a b)  = Just (False, a, b)
deMemoTyF (Prod a b) = Just (True, a, b)

instance HasTrie x => HasTrie (TyF x) where
  newtype TyF x :->: a = TyFTrie (Maybe (Bool, x, x) :->: a)
  trie f = TyFTrie (trie (f . memoTyF))
  untrie (TyFTrie t) = untrie t . deMemoTyF
  enumerate (TyFTrie t) = enumerate t & mapped._1 %~ memoTyF

-- MemoTy, memoTy and dememoTy hare non-exported helper types and functions for
-- defining memoCataTy
newtype MemoTy = MemoTy { unMemoTy :: Ty }

memoTy :: TyF MemoTy -> MemoTy
memoTy x = MemoTy (Fix (unMemoTy <$> x))

deMemoTy :: MemoTy -> TyF MemoTy
deMemoTy (MemoTy (Fix v)) = MemoTy <$> v

instance HasTrie MemoTy where
  newtype MemoTy :->: a = TyTrie (TyF MemoTy :->: a)
  trie f = TyTrie (trie (f . memoTy))
  untrie (TyTrie t) = untrie t . deMemoTy
  enumerate (TyTrie t) = enumerate t & mapped._1 %~ memoTy

-- | An implementation of 'Data.Functor.Fixedpoint.cata' for 'TyF' that is
-- transparently memoized.
--
-- @'memoCataTy' = 'Data.Functor.Fixedpoint.cata'@
memoCataTy :: (TyF a -> a) -> Ty -> a
memoCataTy alg = f . MemoTy
 where
  f = memo (alg . fmap f . deMemoTy)
