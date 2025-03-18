-- | This module builds a wrapper around 'Simplicity.Bitcoin.Semantics.fastEval' to define a 'testEval' variant.
module Simplicity.Bitcoin.TestEval
  ( testEval, TestEval
  ) where

import Prelude hiding (drop, take, fail)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))

import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.JetType
import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.Semantics
import Simplicity.Bitcoin.Term

-- | An Assert instance for 'testCoreEval'.
data TestEval jt a b = TestEval { testEvalSem :: Kleisli (ReaderT PrimEnv Maybe) a b
                                , testEvalFast :: FastEval jt a b
                                }

-- | 'testEval' optimizes Simplicity with assertions evaluation using jets, similar to 'fastEval',
-- but excludes the expression itself from being substituted.
-- This is used in for testing jets against their specifications under the assumption that jets for any subexpressions are correct.
-- Delegation, witnesses, and jets are not supported since they are not allowed within jet definitions.
testEval :: TestEval Jets.JetType a b -> PrimEnv -> a -> Maybe b
testEval = flip . (runReaderT .) . runKleisli . testEvalSem

testFastKleisli = Kleisli . (ReaderT .) . flip . fastEval . testEvalFast

mkLeaf sComb fComb = TestEval sComb fComb

mkUnary sComb fComb t = TestEval (sComb (testFastKleisli t)) (fComb (testEvalFast t))

mkBinary sComb fComb s t = TestEval (sComb (testFastKleisli s) (testFastKleisli t))
                                    (fComb (testEvalFast s) (testEvalFast t))

instance JetType jt => Core (TestEval jt) where
  iden = mkLeaf iden iden
  comp = mkBinary comp comp
  unit = mkLeaf unit unit
  injl = mkUnary injl injl
  injr = mkUnary injr injr
  match = mkBinary match match
  pair = mkBinary pair pair
  take = mkUnary take take
  drop = mkUnary drop drop

instance JetType jt => Assert (TestEval jt) where
  assertl s h = mkUnary (flip assertl h) (flip assertl h) s
  assertr h t = mkUnary (assertr h) (assertr h) t
  fail b = mkLeaf (fail b) (fail b)

instance JetType jt => Primitive (TestEval jt)  where
  primitive p = mkLeaf (primitive p) (primitive p)
