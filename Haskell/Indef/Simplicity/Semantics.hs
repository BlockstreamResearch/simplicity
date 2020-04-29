-- | This module provides the functional semantics of the full 'Simplicity' language.
-- The 'Semantics' arrow is an instance of the 'Simplicity' class and 'sem' evaluates terms of the full Simplicity langauge.
module Simplicity.Semantics
 ( Semantics, sem
 ) where

import Prelude hiding (drop, take, fail)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))

import Simplicity.Delegator.Impl
import Simplicity.Primitive
import Simplicity.Term

-- | The functional semantics of the full Simplicity language consists of
--
-- * Partial effect via the 'Maybe' effect.
--
-- * Environment effects via the 'Control.Monad.Reader.Reader' effect for primitives to access the 'PrimEnv'.
--
-- * Delegation via the 'Delegator' helper.
type Semantics a b = Delegator (Kleisli (ReaderT PrimEnv Maybe)) a b

-- | @
-- sem :: (forall term. Simplicity term => term a b) -> PrimEnv -> a -> Maybe b
-- @
--
-- Execute the fuctional semantics of the full Simplicity language with delegation.
sem :: Semantics a b -> PrimEnv -> a -> Maybe b
sem = flip . (runReaderT .) . runKleisli . runDelegator

instance Primitive p => Primitive (Delegator p) where
  primitive p = Delegator (primitive p) (primitive p)

instance Jet p => Jet (Delegator p) where
  jet t = Delegator (jet t) (jet t)

instance (Jet p, Witness p) => Simplicity (Delegator p) where
