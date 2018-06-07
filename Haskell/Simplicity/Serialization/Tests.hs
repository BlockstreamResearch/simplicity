-- This modules tests primitive bit-stream serialization and deserialization functions.
module Simplicity.Serialization.Tests (tests) where

import Data.Vector.Unboxed (fromList)

import Simplicity.Serialization

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty, Positive(Positive))

-- This collects the tests for the various primitive Simplicity programs.
tests :: TestTree
tests = testGroup "Serialization"
        [ testProperty "get-put bit-string" prop_getPutBitString
        , testProperty "get-put positive" prop_getPutPositive
        ]

-- Check that deserialization of serialization of bit-strings returns the original input.
prop_getPutBitString :: [Bool] -> Bool
prop_getPutBitString l = evalExactVector getBitString (fromList (putBitString l [])) == Just l

-- Check that deserialization of serialization of positive numbers returns the original input.
prop_getPutPositive :: Positive Integer -> Bool
prop_getPutPositive (Positive n) = evalExactVector getPositive (fromList (putPositive n [])) == Just n
