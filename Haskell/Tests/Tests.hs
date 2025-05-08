-- The main test module that gathers and runs the tests in the Simplicity Haskell project.
module Main (main) where

import Test.Tasty

import qualified Simplicity.BitMachine.Tests as BitMachine
import qualified Simplicity.BitMachine.StaticAnalysis.Tests as StaticAnalysis
import qualified Simplicity.FFI.Tests as FFI
import qualified Simplicity.Programs.Tests as Programs
import qualified Simplicity.Bitcoin.Tests as Bitcoin
import qualified Simplicity.Bitcoin.FFI.Tests as BitcoinFFI
import qualified Simplicity.Bitcoin.Serialization.Tests as BitcoinSerialization
import qualified Simplicity.Elements.Tests as Elements
import qualified Simplicity.Elements.FFI.Tests as ElementsFFI
import qualified Simplicity.Elements.Serialization.Tests as ElementsSerialization
import qualified Simplicity.Serialization.Tests as Serialization
import qualified Simplicity.Ty.Tests as Ty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
      [ Programs.tests
      , FFI.tests
      , BitMachine.tests
      , StaticAnalysis.tests
      , Bitcoin.tests
      , BitcoinFFI.tests
      , BitcoinSerialization.tests
      , Ty.tests
      , Elements.tests
      , ElementsFFI.tests
      , ElementsSerialization.tests
      , Serialization.tests
      ]
