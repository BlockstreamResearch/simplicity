module Main (main) where

import Test.Tasty

import qualified Simplicity.BitMachine.Tests as BitMachine
import qualified Simplicity.BitMachine.StaticAnalysis.Tests as StaticAnalysis
import qualified Simplicity.Programs.Tests as Programs

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
      [ Programs.tests
      , BitMachine.tests
      , StaticAnalysis.tests
      ]
