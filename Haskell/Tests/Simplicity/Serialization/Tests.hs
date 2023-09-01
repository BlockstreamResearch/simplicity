-- This module tests some serialization functionality.
module Simplicity.Serialization.Tests (tests) where

import Control.Monad (mzero)
import Data.Foldable (toList)
import qualified Data.Vector.Unboxed as V

import Simplicity.CoreJets as Core
import Simplicity.Serialization
import Simplicity.Ty

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), testCase)

-- Run tests comparing Bit Machine execution with Simplicity's denotational semantics using both naive and TCO translation.
tests :: TestTree
tests = testGroup "Serialization"
      (testDecodeCoreJet <$> toList coreJetMap)

testDecodeCoreJet :: SomeArrow CoreJet -> TestTree
testDecodeCoreJet (SomeArrow jt) = testCase (show jt) (Just (SomeArrow jt) @=? decode)
 where
  vector = V.fromList $ Core.putJetBit jt []
  decode = evalExactVector (Core.getJetBit mzero) vector
