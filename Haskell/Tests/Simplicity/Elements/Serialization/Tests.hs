-- This module tests some serialization functionality.
module Simplicity.Elements.Serialization.Tests (tests) where

import Control.Monad (mzero)
import Data.Foldable (toList)
import qualified Data.Vector.Unboxed as V

import Simplicity.Elements.Jets as Elements
import Simplicity.Serialization
import Simplicity.Ty

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), testCase)

-- Run tests comparing Bit Machine execution with Simplicity's denotational semantics using both naive and TCO translation.
tests :: TestTree
tests = testGroup "Serialization"
      [testDecodeElementsJet jt | SomeArrow jt@(ElementsJet _) <- toList Elements.jetMap]

testDecodeElementsJet :: (TyC a, TyC b) => Elements.JetType a b -> TestTree
testDecodeElementsJet jt = testCase (show jt) (Just (SomeArrow jt) @=? decode)
 where
  vector = V.fromList $ Elements.putJetBit jt []
  decode = evalExactVector (Elements.getJetBit mzero) vector
