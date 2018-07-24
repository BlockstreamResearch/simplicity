{-# LANGUAGE GADTs #-}
-- | This module serves as an interface for different Blockchain applications of Simplicity.
--
-- Each blockchain application defines a set of primitive expressions specific to its application through the 'Prim' GADT.
-- Every primitive has a unquie name defined by 'primName' and 'primPrefix' defines the name of the blockchain application.
--
-- The 'primSem' function defines the functional semantics of the primitive expressions.
-- At the moment, this library only supports the environment effect (and partial functions) for the functional semantics of primitives.
-- 'PrimEnv' holds the environment that the primitive expressions are allowed to read from.
--
-- In the future, this interface may be redesigned to support other commutative effects, such as the Writer effect for commutative monoids.
--
-- The blockchain applications supported at the moment are
--
-- * "Simplicity.Primitive.Bitcoin"
module Simplicity.Primitive
 ( Prim, primPrefix, primName
 , getPrimBit, getPrimByte, putPrimBit, putPrimByte
 , PrimEnv, primSem
 , somePrimEq
 ) where

import Data.Maybe (fromMaybe)
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Primitive.Bitcoin
import Simplicity.Ty

somePrimEq :: SomeArrow Prim -> SomeArrow Prim -> Bool
somePrimEq (SomeArrow p0) (SomeArrow p1) = fromMaybe False $ do
    Refl <- equalTyReflect ra0 ra1
    Refl <- equalTyReflect rb0 rb1
    return $ p0 == p1
  where
   (ra0, rb0) = reifyArrow p0
   (ra1, rb1) = reifyArrow p1
