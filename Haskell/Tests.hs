module Main (main) where

import Test.Tasty

import qualified Simplicity.Arith.Tests as Arith

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
      [ Arith.tests
      ]
