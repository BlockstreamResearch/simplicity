{-# LANGUAGE GADTs #-}
module Simplicity.Generic
  ( scribe
  , eq
  ) where

import Prelude hiding (drop, take)

import Simplicity.Bit
import Simplicity.Term
import Simplicity.Ty

scribe :: Core term => TyReflect b -> b -> term a b
scribe OneR          ()        = unit
scribe (SumR l _)    (Left v)  = injl (scribe l v)
scribe (SumR _ r)    (Right v) = injr (scribe r v)
scribe (ProdR b1 b2) (v1, v2)  = pair (scribe b1 v1) (scribe b2 v2)

eq :: Core term => TyReflect a -> term (a, a) Bit
eq OneR          = true
eq (SumR l r)    = match (pair (drop iden) (take iden) >>> match (eq l) false)
                         (pair (drop iden) (take iden) >>> match false (eq r))
eq (ProdR a1 a2) = pair (pair (take (take iden)) (drop (take iden)) >>> (eq a1))
                        (pair (take (drop iden)) (drop (drop iden)))
                   >>> cond (eq a2) false
