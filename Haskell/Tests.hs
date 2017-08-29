module Main (main) where

import Test.Tasty

import qualified Simplicity.Arith.Tests as Arith
import qualified Simplicity.BitMachine.Tests as BitMachine
import qualified Simplicity.BitMachine.StaticAnalysis.Tests as StaticAnalysis

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
      [ Arith.tests
      , BitMachine.tests
      , StaticAnalysis.tests
      ]
