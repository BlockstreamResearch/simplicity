{-# LANGUAGE RankNTypes #-}
module Simplicity.BitMachine.Tests (tests) where

import Simplicity.Arith
import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TCO
import Simplicity.Programs.Sha256
import Simplicity.Term

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests = testGroup "BitMachine"
      [ testCompiler "Translate" Translate.compile
      , testCompiler "TCO" TCO.compile
      ]

testUsing :: (Core trans, TyC a, TyC b) => (trans a b -> MachineCode) -> (forall term. Core term => term a b) -> a -> Bool
testUsing compiler program x = executeUsing (runMachine . compiler) program x == Just (program x)

testCompiler :: Core trans => String -> (forall a b. (TyC a, TyC b) => trans a b -> MachineCode) -> TestTree
testCompiler name compiler = testGroup name
                  [ testProperty "fullAdder word8" (testUsing compiler (fullAdder word8))
                  , testProperty "adder word8" (testUsing compiler (adder word8))
                  , testProperty "fullMultiplier word8" (testUsing compiler (fullMultiplier word8))
                  , testProperty "multiplier word8" (testUsing compiler (multiplier word8))
                  , testProperty "hashBlock" (testUsing compiler hashBlock)
                  ]
