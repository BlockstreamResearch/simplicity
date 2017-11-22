{-# LANGUAGE RankNTypes #-}
module Simplicity.BitMachine.StaticAnalysis.Tests (tests) where

import Control.Monad.Trans.Writer (execWriterT)

import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.StaticAnalysis as Analysis
import Simplicity.BitMachine.StaticAnalysis.TCO as AnalysisTCO
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TranslateTCO
import Simplicity.Programs.Word
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
        -- TODO: after QuickCheck 2.10 we perhaps add: , testSquareAdj (withMaxSuccess 10) "hashBlock" hashBlock
        ]
      ]

testSquare :: (Arbitrary a, TyC a, TyC b) => String -> (forall term. (Core term) => term a b) -> TestTree
testSquare name program = testProperty name assertion
 where
  staticMem = Analysis.cellsBnd program
  staticMemTCO = AnalysisTCO.cellsBnd program
  dynamicMem i = memSize <$> execWriterT (executeUsing (instrumentMachine . Translate.compile) program i)
  dynamicMemTCO i = memSize <$> execWriterT (executeUsing (instrumentMachine . TranslateTCO.compile) program i)
  square a b c d = a <= b && a <= c && b <=d && c <= d
  assertion i = Just True == (square <$> dynamicMemTCO i <*> dynamicMem i <*> pure staticMemTCO <*> pure staticMem)
