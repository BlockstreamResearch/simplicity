{-# LANGUAGE GADTs #-}
module Simplicity.Arith.Tests where

import Simplicity.Bit
import Simplicity.Ty
import Simplicity.Term
import Simplicity.Arith

import Test.Tasty
import Test.Tasty.QuickCheck

tests :: TestTree
tests = testGroup "Arith"
      [ testProperty "fullAdder word8" prop_fullAdder8
      , testProperty "adder word8" prop_adder8
      , testProperty "fullMultiplier word8" prop_fullMultiplier8
      , testProperty "multiplier word8" prop_multiplier8
      ]

prop_fullAdder8 :: Word8 -> Word8 -> Bit -> Bool
prop_fullAdder8 x y z = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y + if fromBit z then 1 else 0
 where
  (carry, result8) = fullAdder word8 ((x, y), z)

prop_adder8 :: Word8 -> Word8 -> Bool
prop_adder8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y 
 where
  (carry, result8) = adder word8 (x, y)

prop_fullMultiplier8 :: Word8 -> Word8 -> Word8 -> Word8 -> Bool
prop_fullMultiplier8 w x y z = fromWord16 (fullMultiplier word8 ((x, y), (w, z))) == fromWord8 x * fromWord8 y + fromWord8 w + fromWord8 z

prop_multiplier8 :: Word8 -> Word8 -> Bool
prop_multiplier8 x y = fromWord16 (multiplier word8 (x, y)) == fromWord8 x * fromWord8 y 
