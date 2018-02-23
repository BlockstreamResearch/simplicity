{-# LANGUAGE TypeOperators, TypeFamilies #-}
module Simplicity.Ty.Memo (memoCataTy) where

import Prelude hiding (sum)

import Data.Functor.Fixedpoint (Fix(..), cata)
import Data.MemoTrie (HasTrie(..), memo)
import Lens.Family2 ((&), (%~))
import Lens.Family2.Stock (mapped, _1)

import Simplicity.Ty

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

memoCataTy :: (TyF a -> a) -> Ty -> a
memoCataTy alg = f . MemoTy
 where
  f = memo (alg . fmap f . deMemoTy)
