-- This module tests some serialization functionality.
module Simplicity.Bitcoin.Serialization.Tests (tests) where

import Control.Monad (mzero)
import Data.Foldable (toList)
import qualified Data.List as List
import qualified Data.Vector.Unboxed as V

import Simplicity.Arbitrary
import Simplicity.CoreJets
import Simplicity.Bitcoin.Jets as Bitcoin
import Simplicity.Bitcoin.FFI.Primitive as Bitcoin
import Simplicity.FFI.Dag
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Word

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), testCase)
import Test.Tasty.QuickCheck (Property, arbitrary, forAll, chooseInt, testProperty, vectorOf)

-- Run tests comparing Bit Machine execution with Simplicity's denotational semantics using both naive and TCO translation.
tests :: TestTree
tests = testGroup "Bitcoin Serialization"
      [ testGroup "Haskell"
        [ testDecodeBitcoinJet jt | SomeArrow jt@(Bitcoin.BitcoinJet _) <- toList Bitcoin.jetMap ]
      , testGroup "C"
      $ [ testDecodeBitcoinJetFFI jt | SomeArrow jt <- toList Bitcoin.jetMap ]
      ++ [ testProperty "prop_wordCMR" prop_wordCMR ]
      ]

testDecodeBitcoinJet :: (TyC a, TyC b) => Bitcoin.JetType a b -> TestTree
testDecodeBitcoinJet jt = testCase (show jt) (Just (SomeArrow jt) @=? decode)
 where
  vector = V.fromList $ Bitcoin.putJetBit jt []
  decode = evalExactVector (Bitcoin.getJetBit mzero) vector

testDecodeBitcoinJetFFI :: (TyC a, TyC b) => Bitcoin.JetType a b -> TestTree
testDecodeBitcoinJetFFI jt = testCase (show jt) (Right cmr @=? Bitcoin.decodeJetCMR bitstream)
 where
  -- All jet encodings should begin with a 1 bit, which we consume.
  True:bitstream = Bitcoin.putJetBit jt []
  cmr = commitmentRoot (asJet jt)

prop_wordCMR :: SomeConstWordContent -> Property
prop_wordCMR (SomeConstWordContent cwc) = forAll prefix prop
 where
  prefix = do
    n <- chooseInt (0, 7)
    vectorOf n arbitrary
  prop l = wordCMR == computeWordCMR (length l) (l ++ stream)
   where
    wordCMR = commitmentRoot $ asJet (ConstWordJet cwc)
    stream = putConstWordValueBit cwc
