{-# LANGUAGE RankNTypes #-}
module Simplicity.BitMachine.StaticAnalysis.Tests (tests) where

import Control.Monad.Trans.Writer (execWriterT)

import Simplicity.Arith
import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.StaticAnalysis as Analysis
import Simplicity.BitMachine.StaticAnalysis.TCO as AnalysisTCO
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TranslateTCO
import Simplicity.Term

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Arbitrary, testProperty)
import Test.Tasty.HUnit (testCase, assert)

tests :: TestTree
tests = testGroup "StaticAnalysis"
      [ testGroup "memSize"
        [ testSquare "fullAdder word8" (fullAdder word8)
        , testSquare "adder word8" (adder word8)
        , testSquare "fullMultiplier word8" (fullMultiplier word8)
        , testSquare "multiplier word8" (multiplier word8)
        ]
      ]

testSquare :: (Arbitrary a, TyC a, TyC b) => String -> (forall term. (Core term) => term a b) -> TestTree
testSquare name program = testGroup name
                [ testCase "Static TCO <= Static Trans" (assert $ staticMemTCO <= staticMem)
                , testProperty "Dynamic TCO <= Dynamic Trans" (\i -> ((<=) <$> dynamicMemTCO i <*> dynamicMem i) == Just True)
                , testProperty "Dynamic Trans <= Static Trans" (\i -> ((<= staticMem) <$> dynamicMem i) == Just True)
                , testProperty "Dynamic TCO <= Static TCO" (\i -> ((<= staticMemTCO) <$> dynamicMemTCO i) == Just True)
                ]
 where
  staticMem = Analysis.cellsBnd program
  staticMemTCO = AnalysisTCO.cellsBnd program
  dynamicMem i = memSize <$> execWriterT (executeUsing (instrumentMachine . Translate.compile) program i)
  dynamicMemTCO i = memSize <$> execWriterT (executeUsing (instrumentMachine . TranslateTCO.compile) program i)
