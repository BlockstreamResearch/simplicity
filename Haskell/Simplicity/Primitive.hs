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
 ) where

import Simplicity.Primitive.Bitcoin
