{-# LANGUAGE GADTs #-}
module Simplicity.Programs.Generic
  ( scribe
  , eq
  ) where

import Prelude hiding (drop, take)

import Simplicity.Programs.Bit
import Simplicity.Term

scribe :: (TyC a, TyC b, Core term) => b -> term a b
scribe = go reify
 where
  go :: (TyC a, TyC b, Core term) => TyReflect b -> b -> term a b
  go OneR          ()        = unit
  go (SumR l _)    (Left v)  = injl (go l v)
  go (SumR _ r)    (Right v) = injr (go r v)
  go (ProdR b1 b2) (v1, v2)  = pair (go b1 v1) (go b2 v2)

eq :: (TyC a, Core term) => term (a, a) Bit
eq = go reify
 where
  go :: (TyC a, Core term) => TyReflect a -> term (a, a) Bit
  go OneR          = true
  go (SumR l r)    = match (pair (drop iden) (take iden) >>> match (go l) false)
                           (pair (drop iden) (take iden) >>> match false (go r))
  go (ProdR a1 a2) = pair (pair (take (take iden)) (drop (take iden)) >>> (go a1))
                          (pair (take (drop iden)) (drop (drop iden)))
                     >>> cond (go a2) false
