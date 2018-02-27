{-# LANGUAGE RankNTypes #-}
module Simplicity.Term
 ( module Simplicity.Term.Core
 , Primitive(..)
 , Jet(..)
 , Delegate(..)
 , Simplicity(..)
 ) where

import Simplicity.Term.Core
import Simplicity.Primitive
import Simplicity.Ty.Word

class Primitive term where
  primitive :: Prim a b -> term a b

class (Assert term, Primitive term) => Jet term where
  jet :: (TyC a, TyC b) => (forall term0. (Assert term0, Primitive term0) => term0 a b) -> term a b

class Delegate term where
  disconnect :: (TyC a, TyC b, TyC c, TyC d) => term (a, Word256) (b, d) -> term b c -> term a (c, d)

class (Jet term, Witness term, Delegate term) => Simplicity term where
