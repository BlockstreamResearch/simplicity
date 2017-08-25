{-# LANGUAGE RankNTypes #-}
module Simplicity.BitMachine.Tests (tests) where

import Simplicity.Arith
import Simplicity.Bit
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.Translate
import Simplicity.BitMachine.Ty
import Simplicity.Term

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests = testGroup "BitMachine"
      [ testProperty "fullAdder word8" prop_fullAdder8
      , testProperty "adder word8" prop_adder8
      , testProperty "fullMultiplier word8" prop_fullMultiplier8
      , testProperty "multiplier word8" prop_multiplier8
      ]

testUsing :: (TyC a, TyC b) => (forall term. Core term => term a b) -> a -> Bool
testUsing program x = executeUsing (runMachine . compile) program x == Just (program x)

prop_fullAdder8 = testUsing (fullAdder word8)
prop_adder8 = testUsing (adder word8)
prop_fullMultiplier8 = testUsing (fullMultiplier word8)
prop_multiplier8 = testUsing (multiplier word8)
