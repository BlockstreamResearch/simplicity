-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Prelude hiding (sqrt, all)
import Control.Arrow ((***), right)
import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import Data.ByteString.Short (toShort)
import qualified Data.List as L
import Lens.Family2 ((^..), allOf, over, zipWithOf)
import Lens.Family2.Stock (backwards, both_)

import Simplicity.Arbitrary
import Simplicity.Bip0340
import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.Elements.Arbitrary (arbitraryLock)
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.LibSecp256k1.Spec ((.+.), (.*.), (.^.))
import qualified Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.MerkleRoot
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.LibSecp256k1.Lib
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.Word
import Simplicity.Term.Core
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word as Ty
import qualified Simplicity.Word as W

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), Assertion, testCase)
import Test.Tasty.QuickCheck (Arbitrary(..), Discard(Discard), Gen, Property
                             , arbitraryBoundedIntegral, choose, elements, forAll, resize, sized, vectorOf
                             , property
                             , testProperty, withMaxSuccess
                             , label
                             )

toW256 :: W.Word256 -> Word256
toW256 = toWord256 . fromIntegral

toW32 :: W.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW16 :: W.Word16 -> Word16
toW16 = toWord16 . fromIntegral

-- This collects the tests for the various Simplicity programs.
tests :: TestTree
tests = testGroup "Programs"
      [ testGroup "Word"
        [ testCase "verify" assert_verify
        , testCase     "low_1" assert_low_1
        , testCase     "low_8" assert_low_8
        , testCase     "low_16" assert_low_16
        , testCase     "low_32" assert_low_32
        , testCase     "low_64" assert_low_64
        , testCase     "high_1" assert_high_1
        , testCase     "high_8" assert_high_8
        , testCase     "high_16" assert_high_16
        , testCase     "high_32" assert_high_32
        , testCase     "high_64" assert_high_64
        , testProperty "complement_1"  prop_complement_1
        , testProperty "complement_8"  prop_complement_8
        , testProperty "complement_16"  prop_complement_16
        , testProperty "complement_32"  prop_complement_32
        , testProperty "complement_64"  prop_complement_64
        , testProperty "and_1"  prop_and_1
        , testProperty "and_8"  prop_and_8
        , testProperty "and_16"  prop_and_16
        , testProperty "and_32"  prop_and_32
        , testProperty "and_64"  prop_and_64
        , testProperty "or_1"  prop_or_1
        , testProperty "or_8"  prop_or_8
        , testProperty "or_16"  prop_or_16
        , testProperty "or_32"  prop_or_32
        , testProperty "or_64"  prop_or_64
        , testProperty "xor_1"  prop_xor_1
        , testProperty "xor_8"  prop_xor_8
        , testProperty "xor_16"  prop_xor_16
        , testProperty "xor_32"  prop_xor_32
        , testProperty "xor_64"  prop_xor_64
        , testProperty "maj_1"  prop_maj_1
        , testProperty "maj_8"  prop_maj_8
        , testProperty "maj_16"  prop_maj_16
        , testProperty "maj_32"  prop_maj_32
        , testProperty "maj_64"  prop_maj_64
        , testProperty "xor_xor_1"  prop_xor_xor_1
        , testProperty "xor_xor_8"  prop_xor_xor_8
        , testProperty "xor_xor_16"  prop_xor_xor_16
        , testProperty "xor_xor_32"  prop_xor_xor_32
        , testProperty "xor_xor_64"  prop_xor_xor_64
        , testProperty "ch_1"  prop_ch_1
        , testProperty "ch_8"  prop_ch_8
        , testProperty "ch_16"  prop_ch_16
        , testProperty "ch_32"  prop_ch_32
        , testProperty "ch_64"  prop_ch_64
        , testProperty "some_1"  prop_some_1
        , testProperty "some_8"  prop_some_8
        , testProperty "some_16"  prop_some_16
        , testProperty "some_32"  prop_some_32
        , testProperty "some_64"  prop_some_64
        , testProperty "all_8"  prop_all_8
        , testProperty "all_16"  prop_all_16
        , testProperty "all_32"  prop_all_32
        , testProperty "all_64"  prop_all_64
        , testProperty "eq_8"  prop_eq_8
        , testProperty "eq_16"  prop_eq_16
        , testProperty "eq_32"  prop_eq_32
        , testProperty "eq_64"  prop_eq_64
        , testProperty "eq_256"  prop_eq_256
        , testProperty "eq_diag_8"  prop_eq_diag_8
        , testProperty "eq_diag_16"  prop_eq_diag_16
        , testProperty "eq_diag_32"  prop_eq_diag_32
        , testProperty "eq_diag_64"  prop_eq_diag_64
        , testProperty "eq_diag_256"  prop_eq_diag_256
        , testProperty "full_left_shift_8_1"  prop_full_left_shift_8_1
        , testProperty "full_left_shift_8_2"  prop_full_left_shift_8_2
        , testProperty "full_left_shift_8_4"  prop_full_left_shift_8_4
        , testProperty "full_left_shift_16_1"  prop_full_left_shift_16_1
        , testProperty "full_left_shift_16_2"  prop_full_left_shift_16_2
        , testProperty "full_left_shift_16_4"  prop_full_left_shift_16_4
        , testProperty "full_left_shift_16_8"  prop_full_left_shift_16_8
        , testProperty "full_left_shift_32_1"  prop_full_left_shift_32_1
        , testProperty "full_left_shift_32_2"  prop_full_left_shift_32_2
        , testProperty "full_left_shift_32_4"  prop_full_left_shift_32_4
        , testProperty "full_left_shift_32_8"  prop_full_left_shift_32_8
        , testProperty "full_left_shift_32_16"  prop_full_left_shift_32_16
        , testProperty "full_left_shift_64_1"  prop_full_left_shift_64_1
        , testProperty "full_left_shift_64_2"  prop_full_left_shift_64_2
        , testProperty "full_left_shift_64_4"  prop_full_left_shift_64_4
        , testProperty "full_left_shift_64_8"  prop_full_left_shift_64_8
        , testProperty "full_left_shift_64_16"  prop_full_left_shift_64_16
        , testProperty "full_left_shift_64_32"  prop_full_left_shift_64_32
        , testProperty "full_right_shift_8_1"  prop_full_right_shift_8_1
        , testProperty "full_right_shift_8_2"  prop_full_right_shift_8_2
        , testProperty "full_right_shift_8_4"  prop_full_right_shift_8_4
        , testProperty "full_right_shift_16_1"  prop_full_right_shift_16_1
        , testProperty "full_right_shift_16_2"  prop_full_right_shift_16_2
        , testProperty "full_right_shift_16_4"  prop_full_right_shift_16_4
        , testProperty "full_right_shift_16_8"  prop_full_right_shift_16_8
        , testProperty "full_right_shift_32_1"  prop_full_right_shift_32_1
        , testProperty "full_right_shift_32_2"  prop_full_right_shift_32_2
        , testProperty "full_right_shift_32_4"  prop_full_right_shift_32_4
        , testProperty "full_right_shift_32_8"  prop_full_right_shift_32_8
        , testProperty "full_right_shift_32_16"  prop_full_right_shift_32_16
        , testProperty "full_right_shift_64_1"  prop_full_right_shift_64_1
        , testProperty "full_right_shift_64_2"  prop_full_right_shift_64_2
        , testProperty "full_right_shift_64_4"  prop_full_right_shift_64_4
        , testProperty "full_right_shift_64_8"  prop_full_right_shift_64_8
        , testProperty "full_right_shift_64_16"  prop_full_right_shift_64_16
        , testProperty "full_right_shift_64_32"  prop_full_right_shift_64_32
        , testProperty "leftmost_8_1"  prop_leftmost_8_1
        , testProperty "leftmost_8_2"  prop_leftmost_8_2
        , testProperty "leftmost_8_4"  prop_leftmost_8_4
        , testProperty "leftmost_16_1"  prop_leftmost_16_1
        , testProperty "leftmost_16_2"  prop_leftmost_16_2
        , testProperty "leftmost_16_4"  prop_leftmost_16_4
        , testProperty "leftmost_16_8"  prop_leftmost_16_8
        , testProperty "leftmost_32_1"  prop_leftmost_32_1
        , testProperty "leftmost_32_2"  prop_leftmost_32_2
        , testProperty "leftmost_32_4"  prop_leftmost_32_4
        , testProperty "leftmost_32_8"  prop_leftmost_32_8
        , testProperty "leftmost_32_16"  prop_leftmost_32_16
        , testProperty "leftmost_64_1"  prop_leftmost_64_1
        , testProperty "leftmost_64_2"  prop_leftmost_64_2
        , testProperty "leftmost_64_4"  prop_leftmost_64_4
        , testProperty "leftmost_64_8"  prop_leftmost_64_8
        , testProperty "leftmost_64_16"  prop_leftmost_64_16
        , testProperty "leftmost_64_32"  prop_leftmost_64_32
        , testProperty "rightmost_8_1"  prop_rightmost_8_1
        , testProperty "rightmost_8_2"  prop_rightmost_8_2
        , testProperty "rightmost_8_4"  prop_rightmost_8_4
        , testProperty "rightmost_16_1"  prop_rightmost_16_1
        , testProperty "rightmost_16_2"  prop_rightmost_16_2
        , testProperty "rightmost_16_4"  prop_rightmost_16_4
        , testProperty "rightmost_16_8"  prop_rightmost_16_8
        , testProperty "rightmost_32_1"  prop_rightmost_32_1
        , testProperty "rightmost_32_2"  prop_rightmost_32_2
        , testProperty "rightmost_32_4"  prop_rightmost_32_4
        , testProperty "rightmost_32_8"  prop_rightmost_32_8
        , testProperty "rightmost_32_16"  prop_rightmost_32_16
        , testProperty "rightmost_64_1"  prop_rightmost_64_1
        , testProperty "rightmost_64_2"  prop_rightmost_64_2
        , testProperty "rightmost_64_4"  prop_rightmost_64_4
        , testProperty "rightmost_64_8"  prop_rightmost_64_8
        , testProperty "rightmost_64_16"  prop_rightmost_64_16
        , testProperty "rightmost_64_32"  prop_rightmost_64_32
        , testProperty "left_pad_low_1_8" prop_left_pad_low_1_8
        , testProperty "left_pad_low_1_16" prop_left_pad_low_1_16
        , testProperty "left_pad_low_8_16" prop_left_pad_low_8_16
        , testProperty "left_pad_low_1_32" prop_left_pad_low_1_32
        , testProperty "left_pad_low_8_32" prop_left_pad_low_8_32
        , testProperty "left_pad_low_16_32" prop_left_pad_low_16_32
        , testProperty "left_pad_low_1_64" prop_left_pad_low_1_64
        , testProperty "left_pad_low_8_64" prop_left_pad_low_8_64
        , testProperty "left_pad_low_16_64" prop_left_pad_low_16_64
        , testProperty "left_pad_low_32_64" prop_left_pad_low_32_64
        , testProperty "left_pad_high_1_8" prop_left_pad_high_1_8
        , testProperty "left_pad_high_1_16" prop_left_pad_high_1_16
        , testProperty "left_pad_high_8_16" prop_left_pad_high_8_16
        , testProperty "left_pad_high_1_32" prop_left_pad_high_1_32
        , testProperty "left_pad_high_8_32" prop_left_pad_high_8_32
        , testProperty "left_pad_high_16_32" prop_left_pad_high_16_32
        , testProperty "left_pad_high_1_64" prop_left_pad_high_1_64
        , testProperty "left_pad_high_8_64" prop_left_pad_high_8_64
        , testProperty "left_pad_high_16_64" prop_left_pad_high_16_64
        , testProperty "left_pad_high_32_64" prop_left_pad_high_32_64
        , testProperty "left_extend_1_8" prop_left_extend_1_8
        , testProperty "left_extend_1_16" prop_left_extend_1_16
        , testProperty "left_extend_8_16" prop_left_extend_8_16
        , testProperty "left_extend_1_32" prop_left_extend_1_32
        , testProperty "left_extend_8_32" prop_left_extend_8_32
        , testProperty "left_extend_16_32" prop_left_extend_16_32
        , testProperty "left_extend_1_64" prop_left_extend_1_64
        , testProperty "left_extend_8_64" prop_left_extend_8_64
        , testProperty "left_extend_16_64" prop_left_extend_16_64
        , testProperty "left_extend_32_64" prop_left_extend_32_64
        , testProperty "right_pad_low_1_8" prop_right_pad_low_1_8
        , testProperty "right_pad_low_1_16" prop_right_pad_low_1_16
        , testProperty "right_pad_low_8_16" prop_right_pad_low_8_16
        , testProperty "right_pad_low_1_32" prop_right_pad_low_1_32
        , testProperty "right_pad_low_8_32" prop_right_pad_low_8_32
        , testProperty "right_pad_low_16_32" prop_right_pad_low_16_32
        , testProperty "right_pad_low_1_64" prop_right_pad_low_1_64
        , testProperty "right_pad_low_8_64" prop_right_pad_low_8_64
        , testProperty "right_pad_low_16_64" prop_right_pad_low_16_64
        , testProperty "right_pad_low_32_64" prop_right_pad_low_32_64
        , testProperty "right_pad_high_1_8" prop_right_pad_high_1_8
        , testProperty "right_pad_high_1_16" prop_right_pad_high_1_16
        , testProperty "right_pad_high_8_16" prop_right_pad_high_8_16
        , testProperty "right_pad_high_1_32" prop_right_pad_high_1_32
        , testProperty "right_pad_high_8_32" prop_right_pad_high_8_32
        , testProperty "right_pad_high_16_32" prop_right_pad_high_16_32
        , testProperty "right_pad_high_1_64" prop_right_pad_high_1_64
        , testProperty "right_pad_high_8_64" prop_right_pad_high_8_64
        , testProperty "right_pad_high_16_64" prop_right_pad_high_16_64
        , testProperty "right_pad_high_32_64" prop_right_pad_high_32_64
        , testProperty "right_extend_8_16" prop_right_extend_8_16
        , testProperty "right_extend_8_32" prop_right_extend_8_32
        , testProperty "right_extend_16_32" prop_right_extend_16_32
        , testProperty "right_extend_8_64" prop_right_extend_8_64
        , testProperty "right_extend_16_64" prop_right_extend_16_64
        , testProperty "right_extend_32_64" prop_right_extend_32_64
        , testProperty "left_shift_with_8"  prop_left_shift_with_8
        , testProperty "left_shift_with_16"  prop_left_shift_with_16
        , testProperty "left_shift_with_32"  prop_left_shift_with_32
        , testProperty "left_shift_with_64"  prop_left_shift_with_64
        , testProperty "left_shift_8"  prop_left_shift_8
        , testProperty "left_shift_16"  prop_left_shift_16
        , testProperty "left_shift_32"  prop_left_shift_32
        , testProperty "left_shift_64"  prop_left_shift_64
        , testProperty "right_shift_with_8"  prop_right_shift_with_8
        , testProperty "right_shift_with_16"  prop_right_shift_with_16
        , testProperty "right_shift_with_32"  prop_right_shift_with_32
        , testProperty "right_shift_with_64"  prop_right_shift_with_64
        , testProperty "right_shift_8"  prop_right_shift_8
        , testProperty "right_shift_16"  prop_right_shift_16
        , testProperty "right_shift_32"  prop_right_shift_32
        , testProperty "right_shift_64"  prop_right_shift_64
        , testProperty "left_rotate_8"  prop_left_rotate_8
        , testProperty "left_rotate_16"  prop_left_rotate_16
        , testProperty "left_rotate_32"  prop_left_rotate_32
        , testProperty "left_rotate_64"  prop_left_rotate_64
        , testProperty "right_rotate_8"  prop_right_rotate_8
        , testProperty "right_rotate_16"  prop_right_rotate_16
        , testProperty "right_rotate_32"  prop_right_rotate_32
        , testProperty "right_rotate_64"  prop_right_rotate_64
        , testProperty "shift_const_by false word8" prop_shift_const_by_false8
        , testProperty "rotate_const word8" prop_rotate_const8
        , testProperty "transpose zv2 zv8" prop_transpose_2x8
        , testProperty "transpose zv8 zv8" prop_transpose_8x8
        ]
      , testGroup "Arith"
        [ testProperty "lsb word8" prop_lsb8
        , testProperty "msb word8" prop_msb8
        , testProperty "bezout word8" prop_bezout8
        , testProperty "cofactors word8" prop_cofactors8
        , testProperty "gcd word8" prop_gcd8
        , testProperty "lcm word8" prop_lcm8
        , testProperty "absolute_value word4" prop_absolute_value4
        , testProperty "sign word4" prop_sign4
        , testCase     "one_8" assert_one_8
        , testCase     "one_16" assert_one_16
        , testCase     "one_32" assert_one_32
        , testCase     "one_64" assert_one_64
        , testProperty "add_8"  prop_add_8
        , testProperty "add_16"  prop_add_16
        , testProperty "add_32"  prop_add_32
        , testProperty "add_64"  prop_add_64
        , testProperty "full_add_8"  prop_full_add_8
        , testProperty "full_add_16"  prop_full_add_16
        , testProperty "full_add_32"  prop_full_add_32
        , testProperty "full_add_64"  prop_full_add_64
        , testProperty "full_increment_8"  prop_full_increment_8
        , testProperty "full_increment_16"  prop_full_increment_16
        , testProperty "full_increment_32"  prop_full_increment_32
        , testProperty "full_increment_64"  prop_full_increment_64
        , testCase     "full_increment_max_8" assert_full_increment_max_8
        , testCase     "full_increment_max_16" assert_full_increment_max_16
        , testCase     "full_increment_max_32" assert_full_increment_max_32
        , testCase     "full_increment_max_64" assert_full_increment_max_64
        , testProperty "increment_8"  prop_increment_8
        , testProperty "increment_16"  prop_increment_16
        , testProperty "increment_32"  prop_increment_32
        , testProperty "increment_64"  prop_increment_64
        , testCase     "increment_max_8" assert_increment_max_8
        , testCase     "increment_max_16" assert_increment_max_16
        , testCase     "increment_max_32" assert_increment_max_32
        , testCase     "increment_max_64" assert_increment_max_64
        , testProperty "subtract_8"  prop_subtract_8
        , testProperty "subtract_16"  prop_subtract_16
        , testProperty "subtract_32"  prop_subtract_32
        , testProperty "subtract_64"  prop_subtract_64
        , testProperty "full_subtract_8"  prop_full_subtract_8
        , testProperty "full_subtract_16"  prop_full_subtract_16
        , testProperty "full_subtract_32"  prop_full_subtract_32
        , testProperty "full_subtract_64"  prop_full_subtract_64
        , testProperty "negate_8"  prop_negate_8
        , testProperty "negate_16"  prop_negate_16
        , testProperty "negate_32"  prop_negate_32
        , testProperty "negate_64"  prop_negate_64
        , testProperty "full_decrement_8"  prop_full_decrement_8
        , testProperty "full_decrement_16"  prop_full_decrement_16
        , testProperty "full_decrement_32"  prop_full_decrement_32
        , testProperty "full_decrement_64"  prop_full_decrement_64
        , testCase     "full_decrement_zero_8" assert_full_decrement_zero_8
        , testCase     "full_decrement_zero_16" assert_full_decrement_zero_16
        , testCase     "full_decrement_zero_32" assert_full_decrement_zero_32
        , testCase     "full_decrement_zero_64" assert_full_decrement_zero_64
        , testProperty "decrement_8"  prop_decrement_8
        , testProperty "decrement_16"  prop_decrement_16
        , testProperty "decrement_32"  prop_decrement_32
        , testProperty "decrement_64"  prop_decrement_64
        , testCase     "decrement_zero_8" assert_decrement_zero_8
        , testCase     "decrement_zero_16" assert_decrement_zero_16
        , testCase     "decrement_zero_32" assert_decrement_zero_32
        , testCase     "decrement_zero_64" assert_decrement_zero_64
        , testProperty "multiply_8"  prop_multiply_8
        , testProperty "multiply_16"  prop_multiply_16
        , testProperty "multiply_32"  prop_multiply_32
        , testProperty "multiply_64"  prop_multiply_64
        , testProperty "full_multiply_8"  prop_full_multiply_8
        , testProperty "full_multiply_16"  prop_full_multiply_16
        , testProperty "full_multiply_32"  prop_full_multiply_32
        , testProperty "full_multiply_64"  prop_full_multiply_64
        , testProperty "is_zero_8"  prop_is_zero_8
        , testProperty "is_zero_16"  prop_is_zero_16
        , testProperty "is_zero_32"  prop_is_zero_32
        , testProperty "is_zero_64"  prop_is_zero_64
        , testCase     "zero_is_zero_8" assert_zero_is_zero_8
        , testCase     "zero_is_zero_16" assert_zero_is_zero_16
        , testCase     "zero_is_zero_32" assert_zero_is_zero_32
        , testCase     "zero_is_zero_64" assert_zero_is_zero_64
        , testProperty "is_one_8"  prop_is_one_8
        , testProperty "is_one_16"  prop_is_one_16
        , testProperty "is_one_32"  prop_is_one_32
        , testProperty "is_one_64"  prop_is_one_64
        , testCase     "one_is_one_8" assert_one_is_one_8
        , testCase     "one_is_one_16" assert_one_is_one_16
        , testCase     "one_is_one_32" assert_one_is_one_32
        , testCase     "one_is_one_64" assert_one_is_one_64
        , testProperty "le_8"  prop_le_8
        , testProperty "le_16"  prop_le_16
        , testProperty "le_32"  prop_le_32
        , testProperty "le_64"  prop_le_64
        , testProperty "le_diag_8"  prop_le_diag_8
        , testProperty "le_diag_16"  prop_le_diag_16
        , testProperty "le_diag_32"  prop_le_diag_32
        , testProperty "le_diag_64"  prop_le_diag_64
        , testProperty "lt_8"  prop_lt_8
        , testProperty "lt_16"  prop_lt_16
        , testProperty "lt_32"  prop_lt_32
        , testProperty "lt_64"  prop_lt_64
        , testProperty "lt_diag_8"  prop_lt_diag_8
        , testProperty "lt_diag_16"  prop_lt_diag_16
        , testProperty "lt_diag_32"  prop_lt_diag_32
        , testProperty "lt_diag_64"  prop_lt_diag_64
        , testProperty "min_8"  prop_min_8
        , testProperty "min_16"  prop_min_16
        , testProperty "min_32"  prop_min_32
        , testProperty "min_64"  prop_min_64
        , testProperty "max_8"  prop_max_8
        , testProperty "max_16"  prop_max_16
        , testProperty "max_32"  prop_max_32
        , testProperty "max_64"  prop_max_64
        , testProperty "median_8"  prop_median_8
        , testProperty "median_16"  prop_median_16
        , testProperty "median_32"  prop_median_32
        , testProperty "median_64"  prop_median_64
        , testProperty "div_mod_8"  prop_div_mod_8
        , testProperty "div_mod_16"  prop_div_mod_16
        , testProperty "div_mod_32"  prop_div_mod_32
        , testProperty "div_mod_64"  prop_div_mod_64
        , testProperty "divide_8"  prop_divide_8
        , testProperty "divide_16"  prop_divide_16
        , testProperty "divide_32"  prop_divide_32
        , testProperty "divide_64"  prop_divide_64
        , testProperty "modulo_8"  prop_modulo_8
        , testProperty "modulo_16"  prop_modulo_16
        , testProperty "modulo_32"  prop_modulo_32
        , testProperty "modulo_64"  prop_modulo_64
        , testProperty "divides_8"  prop_divides_8
        , testProperty "divides_16"  prop_divides_16
        , testProperty "divides_32"  prop_divides_32
        , testProperty "divides_64"  prop_divides_64
        , testProperty "div_mod_zero_8"  prop_div_mod_zero_8
        , testProperty "div_mod_zero_16"  prop_div_mod_zero_16
        , testProperty "div_mod_zero_32"  prop_div_mod_zero_32
        , testProperty "div_mod_zero_64"  prop_div_mod_zero_64
        , testProperty "divide_zero_8"  prop_divide_zero_8
        , testProperty "divide_zero_16"  prop_divide_zero_16
        , testProperty "divide_zero_32"  prop_divide_zero_32
        , testProperty "divide_zero_64"  prop_divide_zero_64
        , testProperty "modulo_zero_8"  prop_modulo_zero_8
        , testProperty "modulo_zero_16"  prop_modulo_zero_16
        , testProperty "modulo_zero_32"  prop_modulo_zero_32
        , testProperty "modulo_zero_64"  prop_modulo_zero_64
        , testProperty "divides_zero_8"  prop_divides_zero_8
        , testProperty "divides_zero_16"  prop_divides_zero_16
        , testProperty "divides_zero_32"  prop_divides_zero_32
        , testProperty "divides_zero_64"  prop_divides_zero_64
        , testProperty "div_mod_128_64"   prop_div_mod_128_64
        , testProperty "div_mod_128_64_low_y"   prop_div_mod_128_64_low_y
        , testProperty "div_mod_128_64_high_x"   prop_div_mod_128_64_high_x
        ]
      , testGroup "Hash"
        [ testCase "sha_256_iv" assert_sha_256_iv
        , testProperty "sha_256_block" prop_sha_256_block
        , testCase "sha_256_ctx_8_init" assert_sha_256_ctx_8_init
        , testProperty "sha_256_ctx_8_add_1" prop_sha_256_ctx_8_add_1
        , testProperty "sha_256_ctx_8_add_2" prop_sha_256_ctx_8_add_2
        , testProperty "sha_256_ctx_8_add_4" prop_sha_256_ctx_8_add_4
        , testProperty "sha_256_ctx_8_add_8" prop_sha_256_ctx_8_add_8
        , testProperty "sha_256_ctx_8_add_16" prop_sha_256_ctx_8_add_16
        , testProperty "sha_256_ctx_8_add_32" prop_sha_256_ctx_8_add_32
        , testProperty "sha_256_ctx_8_add_64" prop_sha_256_ctx_8_add_64
        , testProperty "sha_256_ctx_8_add_128" prop_sha_256_ctx_8_add_128
        , testProperty "sha_256_ctx_8_add_256" prop_sha_256_ctx_8_add_256
        , testProperty "sha_256_ctx_8_add_512" prop_sha_256_ctx_8_add_512
        , testProperty "sha_256_ctx_8_add_buffer_511" prop_sha_256_ctx_8_add_buffer_511
        , testProperty "sha_256_ctx_8_finalize" prop_sha_256_ctx_8_finalize
        ]
      , testGroup "ellipticCurve"
        [ testProperty "fe_normalize" prop_fe_normalize
        , testProperty "fe_add" prop_fe_add
        , testProperty "fe_multiply" prop_fe_multiply
        , testProperty "fe_square" prop_fe_square
        , testProperty "fe_negate" prop_fe_negate
        , testProperty "fe_halve" prop_fe_halve
        , testProperty "fe_invert" (withMaxSuccess 10 prop_fe_invert)
        , testProperty "fe_square_root" (withMaxSuccess 10 prop_fe_square_root)
        , testProperty "gej_rescale" prop_gej_rescale
        , testProperty "gej_rescale_inf" prop_gej_rescale_inf
        , testProperty "gej_double" prop_gej_double
        , testProperty "gej_double_inf" prop_gej_double_inf
        , testProperty "gej_add_ex" prop_gej_add_ex
        , testProperty "gej_add_ex_double" prop_gej_add_ex_double
        , testProperty "gej_add_ex_opp" prop_gej_add_ex_opp
        , testProperty "gej_add_ex_infl" prop_gej_add_ex_infl
        , testProperty "gej_add_ex_infr" prop_gej_add_ex_infr
        , testProperty "gej_add" prop_gej_add
        , testProperty "gej_add_double" prop_gej_add_double
        , testProperty "gej_add_opp" prop_gej_add_opp
        , testProperty "gej_add_infl" prop_gej_add_infl
        , testProperty "gej_add_infr" prop_gej_add_infr
        , testProperty "gej_ge_add_ex" prop_gej_ge_add_ex
        , testProperty "gej_ge_add_ex_double" prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp" prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf" prop_gej_ge_add_ex_inf
        , testProperty "gej_equiv" prop_gej_equiv
        , testProperty "gej_equiv_infl" prop_gej_equiv_infl
        , testProperty "gej_equiv_infr" prop_gej_equiv_infr
        , testProperty "gej_equiv_inf" prop_gej_equiv_inf
        , testProperty "gej_equiv_true" prop_gej_equiv_true
        , testProperty "gej_ge_equiv" prop_gej_ge_equiv
        , testProperty "gej_ge_equiv_inf" prop_gej_ge_equiv_inf
        , testProperty "gej_ge_equiv_true" prop_gej_ge_equiv_true
        , testProperty "gej_x_equiv" prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf" prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true" prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero" prop_gej_x_equiv_inf_zero
        , testProperty "gej_is_on_curve" prop_gej_is_on_curve
        , testProperty "gej_is_on_curve_half" prop_gej_is_on_curve_half
        , testProperty "gej_is_on_curve_inf" prop_gej_is_on_curve_inf
        , testProperty "gej_is_on_curve_inf_half" prop_gej_is_on_curve_inf_half
        , testProperty "ge_is_on_curve" prop_ge_is_on_curve
        , testProperty "ge_is_on_curve_half" prop_ge_is_on_curve_half
        , testProperty "scalar_normalize" prop_scalar_normalize
        , testProperty "scalar_add" prop_scalar_add
        , testProperty "scalar_square" prop_scalar_square
        , testProperty "scalar_multiply" prop_scalar_multiply
        , testProperty "scalar_negate" prop_scalar_negate
        , testProperty "scalar_invert" (withMaxSuccess 10 prop_scalar_invert)
        , testProperty "scalar_split_lambda" prop_scalar_split_lambda
        , testProperty "wnaf5" prop_wnaf5
        , testProperty "wnaf15" prop_wnaf15
        , testProperty "decompress" prop_decompress
        , testProperty "linear_combination_1" prop_linear_combination_1
        , testProperty "linear_combination_1_0" prop_linear_combination_1_0
        , testProperty "linear_combination_1_inf" prop_linear_combination_1_inf
        , testProperty "linear_check_1" prop_linear_check_1
        , testProperty "point_check_1" prop_point_check_1
        , testProperty "swu" prop_swu
        , testProperty "hash_to_curve" prop_hash_to_curve
        ]
      , testGroup "bip0340"
        [ testProperty "pubkey_unpack" prop_pubkey_unpack
        , testProperty "pubkey_unpack_neg" prop_pubkey_unpack_neg
        , testProperty "signature_unpack" prop_signature_unpack
        , testProperty "check_sig_verify" prop_check_sig_verify
        , testProperty "check_sig_verify_true" prop_check_sig_verify_true
        ]
      , group_bip_0340_check
      , testGroup "timelock"
        [ testProperty "parse_lock" prop_parse_lock
        , testProperty "parse_sequence" prop_parse_sequence
        ]
      ]

assert_verify :: Assertion
assert_verify =
  (fastF (toBit False), fastF (toBit True))
    @=?
  (implF (toBit False), implF (toBit True))
 where
  fastF = testCoreEval (specification (WordJet Verify))
  implF = implementation (WordJet Verify)

prop_shift_const_by_false8 :: Word8 -> Property
prop_shift_const_by_false8 x = forAll (choose (-8,16)) $ \c ->
                               W.shift (conv x) c == conv (shift_const_by false word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_rotate_const8 :: Word8 -> Property
prop_rotate_const8 x = forAll (choose (-8,16)) $ \c ->
                       W.rotate (conv x) c == conv (rotate_const word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_transpose_2x8 :: Word16 -> Bool
prop_transpose_2x8 x = L.transpose (map (^..both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv2 zv8 x^..both_)
 where
  zv2 = DoubleZV SingleZV
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV

prop_transpose_8x8 :: Word64 -> Bool
prop_transpose_8x8 x = L.transpose (map (^..both_.both_.both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv8 zv8' x^..both_.both_.both_)
 where
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV
  zv8' = DoubleZV . DoubleZV . DoubleZV $ SingleZV -- monomorhpism restriction

prop_lsb8 :: Word8 -> Bool
prop_lsb8 x = W.testBit (fromWord8 x) 0 == fromBit (Arith.lsb word8 x)

prop_msb8 :: Word8 -> Bool
prop_msb8 x = W.testBit (fromWord8 x) 7 == fromBit (Arith.msb word8 x)

prop_bezout8 :: Word8 -> Word8 -> Bool
prop_bezout8 x y = a * x' + b * y' == d
                && if x' == y' then (a == 1 && b == 0)
                   else if y' == 0 then (a == 1 && b == 0)
                   else if x' == 0 then (a == 0 && b == 1)
                   else (if d == y' then a == 0 else abs a * 2 * d <= y')
                     && (if d == x' then b == 0 else abs b * 2 * d <= x')
 where
  x' = fromWord8 x
  y' = fromWord8 y
  d = x' `gcd` y'
  (a, b) = either f g $ Arith.bezout word8 (x, y)
  f (a, b) = (fromWord8 a, - fromWord8 b)
  g (a, b) = (- fromWord8 a, fromWord8 b)

prop_cofactors8 :: Word8 -> Word8 -> Bool
prop_cofactors8 x y = fromWord8 x == d * fromWord8 a
                   && fromWord8 y == d * fromWord8 b
 where
  d = fromWord8 x `gcd` fromWord8 y
  (a, b) = Arith.cofactors word8 (x, y)

prop_gcd8 :: Word8 -> Word8 -> Bool
prop_gcd8 x y = (fromWord8 x `gcd` fromWord8 y) == fromWord8 (Arith.gcd word8 (x,y))

prop_lcm8 :: Word8 -> Word8 -> Bool
prop_lcm8 x y = (fromWord8 x `lcm` fromWord8 y) == fromWord16 (Arith.lcm word8 (x,y))

prop_absolute_value4 :: Word4 -> Bool
prop_absolute_value4 x = abs (fromInt4 x) == fromWord4 (Arith.absolute_value word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x

prop_sign4 :: Word4 -> Bool
prop_sign4 x = signum (fromInt4 x) == fromInt2 (Arith.sign word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x
  fromInt2 x = if 2^1 <= w2 then w2 - 2^2 else w2
   where
    w2 = fromWord2 x

assert_low_1 :: Assertion
assert_low_1 = fastF () @=? implementation (WordJet Low1) ()
 where
  fastF = testCoreEval (specification (WordJet Low1))

assert_low_8 :: Assertion
assert_low_8 = fastF () @=? implementation (WordJet Low8) ()
 where
  fastF = testCoreEval (specification (WordJet Low8))

assert_low_16 :: Assertion
assert_low_16 = fastF () @=? implementation (WordJet Low16) ()
 where
  fastF = testCoreEval (specification (WordJet Low16))

assert_low_32 :: Assertion
assert_low_32 = fastF () @=? implementation (WordJet Low32) ()
 where
  fastF = testCoreEval (specification (WordJet Low32))

assert_low_64 :: Assertion
assert_low_64 = fastF () @=? implementation (WordJet Low64) ()
 where
  fastF = testCoreEval (specification (WordJet Low64))

assert_high_1 :: Assertion
assert_high_1 = fastF () @=? implementation (WordJet High1) ()
 where
  fastF = testCoreEval (specification (WordJet High1))

assert_high_8 :: Assertion
assert_high_8 = fastF () @=? implementation (WordJet High8) ()
 where
  fastF = testCoreEval (specification (WordJet High8))

assert_high_16 :: Assertion
assert_high_16 = fastF () @=? implementation (WordJet High16) ()
 where
  fastF = testCoreEval (specification (WordJet High16))

assert_high_32 :: Assertion
assert_high_32 = fastF () @=? implementation (WordJet High32) ()
 where
  fastF = testCoreEval (specification (WordJet High32))

assert_high_64 :: Assertion
assert_high_64 = fastF () @=? implementation (WordJet High64) ()
 where
  fastF = testCoreEval (specification (WordJet High64))

prop_complement_1 :: Bool -> Bool
prop_complement_1 = \x -> let input = toBit x
                       in fastF input == implementation (WordJet Complement1) input
 where
  fastF = testCoreEval (specification (WordJet Complement1))

prop_complement_8 :: W.Word8 -> Bool
prop_complement_8 = \x -> let input = toW8 x
                       in fastF input == implementation (WordJet Complement8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement8))

prop_complement_16 :: W.Word16 -> Bool
prop_complement_16 = \x -> let input = toW16 x
                        in fastF input == implementation (WordJet Complement16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement16))

prop_complement_32 :: W.Word32 -> Bool
prop_complement_32 = \x -> let input = toW32 x
                        in fastF input == implementation (WordJet Complement32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement32))

prop_complement_64 :: W.Word64 -> Bool
prop_complement_64 = \x -> let input = toW64 x
                        in fastF input == implementation (WordJet Complement64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement64))

prop_and_1 :: Bool -> Bool -> Bool
prop_and_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == implementation (WordJet And1) input
 where
  fastF = testCoreEval (specification (WordJet And1))

prop_and_8 :: W.Word8 -> W.Word8 -> Bool
prop_and_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (WordJet And8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet And8))

prop_and_16 :: W.Word16 -> W.Word16 -> Bool
prop_and_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (WordJet And16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet And16))

prop_and_32 :: W.Word32 -> W.Word32 -> Bool
prop_and_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (WordJet And32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet And32))

prop_and_64 :: W.Word64 -> W.Word64 -> Bool
prop_and_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (WordJet And64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet And64))

prop_or_1 :: Bool -> Bool -> Bool
prop_or_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == implementation (WordJet Or1) input
 where
  fastF = testCoreEval (specification (WordJet Or1))

prop_or_8 :: W.Word8 -> W.Word8 -> Bool
prop_or_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (WordJet Or8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or8))

prop_or_16 :: W.Word16 -> W.Word16 -> Bool
prop_or_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (WordJet Or16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or16))

prop_or_32 :: W.Word32 -> W.Word32 -> Bool
prop_or_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (WordJet Or32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or32))

prop_or_64 :: W.Word64 -> W.Word64 -> Bool
prop_or_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (WordJet Or64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or64))

prop_xor_1 :: Bool -> Bool -> Bool
prop_xor_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == implementation (WordJet Xor1) input
 where
  fastF = testCoreEval (specification (WordJet Xor1))

prop_xor_8 :: W.Word8 -> W.Word8 -> Bool
prop_xor_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (WordJet Xor8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor8))

prop_xor_16 :: W.Word16 -> W.Word16 -> Bool
prop_xor_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (WordJet Xor16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor16))

prop_xor_32 :: W.Word32 -> W.Word32 -> Bool
prop_xor_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (WordJet Xor32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor32))

prop_xor_64 :: W.Word64 -> W.Word64 -> Bool
prop_xor_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (WordJet Xor64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor64))

prop_maj_1 :: Bool -> Bool -> Bool -> Bool
prop_maj_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == implementation (WordJet Maj1) input
 where
  fastF = testCoreEval (specification (WordJet Maj1))

prop_maj_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_maj_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == implementation (WordJet Maj8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj8))

prop_maj_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_maj_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == implementation (WordJet Maj16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj16))

prop_maj_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_maj_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == implementation (WordJet Maj32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj32))

prop_maj_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_maj_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == implementation (WordJet Maj64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj64))

prop_xor_xor_1 :: Bool -> Bool -> Bool -> Bool
prop_xor_xor_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == implementation (WordJet XorXor1) input
 where
  fastF = testCoreEval (specification (WordJet XorXor1))

prop_xor_xor_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_xor_xor_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == implementation (WordJet XorXor8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor8))

prop_xor_xor_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_xor_xor_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == implementation (WordJet XorXor16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor16))

prop_xor_xor_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_xor_xor_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == implementation (WordJet XorXor32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor32))

prop_xor_xor_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_xor_xor_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == implementation (WordJet XorXor64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor64))

prop_ch_1 :: Bool -> Bool -> Bool -> Bool
prop_ch_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == implementation (WordJet Ch1) input
 where
  fastF = testCoreEval (specification (WordJet Ch1))

prop_ch_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_ch_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == implementation (WordJet Ch8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch8))

prop_ch_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_ch_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == implementation (WordJet Ch16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch16))

prop_ch_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_ch_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == implementation (WordJet Ch32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch32))

prop_ch_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_ch_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == implementation (WordJet Ch64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch64))

prop_some_1 :: Bool -> Bool
prop_some_1 = \x -> let input = toBit x
                       in fastF input == implementation (WordJet Some1) input
 where
  fastF = testCoreEval (specification (WordJet Some1))

prop_some_8 :: W.Word8 -> Bool
prop_some_8 = \x -> let input = toW8 x
                       in fastF input == implementation (WordJet Some8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some8))

prop_some_16 :: W.Word16 -> Bool
prop_some_16 = \x -> let input = toW16 x
                        in fastF input == implementation (WordJet Some16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some16))

prop_some_32 :: W.Word32 -> Bool
prop_some_32 = \x -> let input = toW32 x
                        in fastF input == implementation (WordJet Some32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some32))

prop_some_64 :: W.Word64 -> Bool
prop_some_64 = \x -> let input = toW64 x
                        in fastF input == implementation (WordJet Some64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some64))

prop_all_8 :: W.Word8 -> Bool
prop_all_8 = \x -> let input = toW8 x
                       in fastF input == implementation (WordJet All8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet All8))

prop_all_16 :: W.Word16 -> Bool
prop_all_16 = \x -> let input = toW16 x
                        in fastF input == implementation (WordJet All16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet All16))

prop_all_32 :: W.Word32 -> Bool
prop_all_32 = \x -> let input = toW32 x
                        in fastF input == implementation (WordJet All32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet All32))

prop_all_64 :: W.Word64 -> Bool
prop_all_64 = \x -> let input = toW64 x
                        in fastF input == implementation (WordJet All64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet All64))

prop_eq_8 :: W.Word8 -> W.Word8 -> Bool
prop_eq_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (WordJet Eq8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq8))

prop_eq_16 :: W.Word16 -> W.Word16 -> Bool
prop_eq_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (WordJet Eq16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq16))

prop_eq_32 :: W.Word32 -> W.Word32 -> Bool
prop_eq_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (WordJet Eq32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq32))

prop_eq_64 :: W.Word64 -> W.Word64 -> Bool
prop_eq_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (WordJet Eq64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq64))

prop_eq_256 :: W.Word256 -> W.Word256 -> Bool
prop_eq_256 = \x y -> let input = (toW256 x, toW256 y)
                       in fastF input == implementation (WordJet Eq256) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq256))

prop_eq_diag_8 :: W.Word8 -> Bool
prop_eq_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == implementation (WordJet Eq8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq8))

prop_eq_diag_16 :: W.Word16 -> Bool
prop_eq_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == implementation (WordJet Eq16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq16))

prop_eq_diag_32 :: W.Word32 -> Bool
prop_eq_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == implementation (WordJet Eq32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq32))

prop_eq_diag_64 :: W.Word64 -> Bool
prop_eq_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == implementation (WordJet Eq64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq64))

prop_eq_diag_256 :: W.Word256 -> Bool
prop_eq_diag_256 = \x -> let input = (toW256 x, toW256 x)
                         in fastF input == implementation (WordJet Eq256) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq256))

prop_full_left_shift_8_1 :: W.Word8 -> Bool -> Bool
prop_full_left_shift_8_1 = \x y -> let input = (toW8 x, toBit y)
                                   in fastF input == implementation (WordJet FullLeftShift8_1) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_1))

prop_full_left_shift_8_2 :: W.Word8 -> W.Word8 -> Bool
prop_full_left_shift_8_2 = \x y -> let input = (toW8 x, toW2 y)
                                   in fastF input == implementation (WordJet FullLeftShift8_2) input
 where
  toW8 = toWord8 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_2))

prop_full_left_shift_8_4 :: W.Word8 -> W.Word8 -> Bool
prop_full_left_shift_8_4 = \x y -> let input = (toW8 x, toW4 y)
                                   in fastF input == implementation (WordJet FullLeftShift8_4) input
 where
  toW8 = toWord8 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_4))

prop_full_left_shift_16_1 :: W.Word16 -> Bool -> Bool
prop_full_left_shift_16_1 = \x y -> let input = (toW16 x, toBit y)
                                   in fastF input == implementation (WordJet FullLeftShift16_1) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_1))

prop_full_left_shift_16_2 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_2 = \x y -> let input = (toW16 x, toW2 y)
                                   in fastF input == implementation (WordJet FullLeftShift16_2) input
 where
  toW16 = toWord16 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_2))

prop_full_left_shift_16_4 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_4 = \x y -> let input = (toW16 x, toW4 y)
                                   in fastF input == implementation (WordJet FullLeftShift16_4) input
 where
  toW16 = toWord16 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_4))

prop_full_left_shift_16_8 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_8 = \x y -> let input = (toW16 x, toW8 y)
                                   in fastF input == implementation (WordJet FullLeftShift16_8) input
 where
  toW16 = toWord16 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_8))

prop_full_left_shift_32_1 :: W.Word32 -> Bool -> Bool
prop_full_left_shift_32_1 = \x y -> let input = (toW32 x, toBit y)
                                   in fastF input == implementation (WordJet FullLeftShift32_1) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_1))

prop_full_left_shift_32_2 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_2 = \x y -> let input = (toW32 x, toW2 y)
                                   in fastF input == implementation (WordJet FullLeftShift32_2) input
 where
  toW32 = toWord32 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_2))

prop_full_left_shift_32_4 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_4 = \x y -> let input = (toW32 x, toW4 y)
                                   in fastF input == implementation (WordJet FullLeftShift32_4) input
 where
  toW32 = toWord32 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_4))

prop_full_left_shift_32_8 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_8 = \x y -> let input = (toW32 x, toW8 y)
                                   in fastF input == implementation (WordJet FullLeftShift32_8) input
 where
  toW32 = toWord32 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_8))

prop_full_left_shift_32_16 :: W.Word32 -> W.Word16 -> Bool
prop_full_left_shift_32_16 = \x y -> let input = (toW32 x, toW16 y)
                                   in fastF input == implementation (WordJet FullLeftShift32_16) input
 where
  toW32 = toWord32 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_16))

prop_full_left_shift_64_1 :: W.Word64 -> Bool -> Bool
prop_full_left_shift_64_1 = \x y -> let input = (toW64 x, toBit y)
                                   in fastF input == implementation (WordJet FullLeftShift64_1) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_1))

prop_full_left_shift_64_2 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_2 = \x y -> let input = (toW64 x, toW2 y)
                                   in fastF input == implementation (WordJet FullLeftShift64_2) input
 where
  toW64 = toWord64 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_2))

prop_full_left_shift_64_4 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_4 = \x y -> let input = (toW64 x, toW4 y)
                                   in fastF input == implementation (WordJet FullLeftShift64_4) input
 where
  toW64 = toWord64 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_4))

prop_full_left_shift_64_8 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_8 = \x y -> let input = (toW64 x, toW8 y)
                                   in fastF input == implementation (WordJet FullLeftShift64_8) input
 where
  toW64 = toWord64 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_8))

prop_full_left_shift_64_16 :: W.Word64 -> W.Word16 -> Bool
prop_full_left_shift_64_16 = \x y -> let input = (toW64 x, toW16 y)
                                   in fastF input == implementation (WordJet FullLeftShift64_16) input
 where
  toW64 = toWord64 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_16))

prop_full_left_shift_64_32 :: W.Word64 -> W.Word32 -> Bool
prop_full_left_shift_64_32 = \x y -> let input = (toW64 x, toW32 y)
                                   in fastF input == implementation (WordJet FullLeftShift64_32) input
 where
  toW64 = toWord64 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_32))

prop_full_right_shift_8_1 :: W.Word8 -> Bool -> Bool
prop_full_right_shift_8_1 = \x y -> let input = (toBit y, toW8 x)
                                   in fastF input == implementation (WordJet FullRightShift8_1) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_1))

prop_full_right_shift_8_2 :: W.Word8 -> W.Word8 -> Bool
prop_full_right_shift_8_2 = \x y -> let input = (toW2 y, toW8 x)
                                   in fastF input == implementation (WordJet FullRightShift8_2) input
 where
  toW8 = toWord8 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_2))

prop_full_right_shift_8_4 :: W.Word8 -> W.Word8 -> Bool
prop_full_right_shift_8_4 = \x y -> let input = (toW4 y, toW8 x)
                                   in fastF input == implementation (WordJet FullRightShift8_4) input
 where
  toW8 = toWord8 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_4))

prop_full_right_shift_16_1 :: W.Word16 -> Bool -> Bool
prop_full_right_shift_16_1 = \x y -> let input = (toBit y, toW16 x)
                                   in fastF input == implementation (WordJet FullRightShift16_1) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_1))

prop_full_right_shift_16_2 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_2 = \x y -> let input = (toW2 y, toW16 x)
                                   in fastF input == implementation (WordJet FullRightShift16_2) input
 where
  toW16 = toWord16 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_2))

prop_full_right_shift_16_4 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_4 = \x y -> let input = (toW4 y, toW16 x)
                                   in fastF input == implementation (WordJet FullRightShift16_4) input
 where
  toW16 = toWord16 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_4))

prop_full_right_shift_16_8 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_8 = \x y -> let input = (toW8 y, toW16 x)
                                   in fastF input == implementation (WordJet FullRightShift16_8) input
 where
  toW16 = toWord16 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_8))

prop_full_right_shift_32_1 :: W.Word32 -> Bool -> Bool
prop_full_right_shift_32_1 = \x y -> let input = (toBit y, toW32 x)
                                   in fastF input == implementation (WordJet FullRightShift32_1) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_1))

prop_full_right_shift_32_2 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_2 = \x y -> let input = (toW2 y, toW32 x)
                                   in fastF input == implementation (WordJet FullRightShift32_2) input
 where
  toW32 = toWord32 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_2))

prop_full_right_shift_32_4 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_4 = \x y -> let input = (toW4 y, toW32 x)
                                   in fastF input == implementation (WordJet FullRightShift32_4) input
 where
  toW32 = toWord32 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_4))

prop_full_right_shift_32_8 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_8 = \x y -> let input = (toW8 y, toW32 x)
                                   in fastF input == implementation (WordJet FullRightShift32_8) input
 where
  toW32 = toWord32 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_8))

prop_full_right_shift_32_16 :: W.Word32 -> W.Word16 -> Bool
prop_full_right_shift_32_16 = \x y -> let input = (toW16 y, toW32 x)
                                   in fastF input == implementation (WordJet FullRightShift32_16) input
 where
  toW32 = toWord32 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_16))

prop_full_right_shift_64_1 :: W.Word64 -> Bool -> Bool
prop_full_right_shift_64_1 = \x y -> let input = (toBit y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_1) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_1))

prop_full_right_shift_64_2 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_2 = \x y -> let input = (toW2 y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_2) input
 where
  toW64 = toWord64 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_2))

prop_full_right_shift_64_4 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_4 = \x y -> let input = (toW4 y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_4) input
 where
  toW64 = toWord64 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_4))

prop_full_right_shift_64_8 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_8 = \x y -> let input = (toW8 y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_8) input
 where
  toW64 = toWord64 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_8))

prop_full_right_shift_64_16 :: W.Word64 -> W.Word16 -> Bool
prop_full_right_shift_64_16 = \x y -> let input = (toW16 y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_16) input
 where
  toW64 = toWord64 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_16))

prop_full_right_shift_64_32 :: W.Word64 -> W.Word32 -> Bool
prop_full_right_shift_64_32 = \x y -> let input = (toW32 y, toW64 x)
                                   in fastF input == implementation (WordJet FullRightShift64_32) input
 where
  toW64 = toWord64 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_32))

prop_leftmost_8_1 :: W.Word8 -> Bool
prop_leftmost_8_1 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Leftmost8_1) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_1))

prop_leftmost_8_2 :: W.Word8 -> Bool
prop_leftmost_8_2 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Leftmost8_2) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_2))

prop_leftmost_8_4 :: W.Word8 -> Bool
prop_leftmost_8_4 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Leftmost8_4) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_4))

prop_leftmost_16_1 :: W.Word16 -> Bool
prop_leftmost_16_1 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Leftmost16_1) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_1))

prop_leftmost_16_2 :: W.Word16 -> Bool
prop_leftmost_16_2 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Leftmost16_2) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_2))

prop_leftmost_16_4 :: W.Word16 -> Bool
prop_leftmost_16_4 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Leftmost16_4) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_4))

prop_leftmost_16_8 :: W.Word16 -> Bool
prop_leftmost_16_8 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Leftmost16_8) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_8))

prop_leftmost_32_1 :: W.Word32 -> Bool
prop_leftmost_32_1 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Leftmost32_1) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_1))

prop_leftmost_32_2 :: W.Word32 -> Bool
prop_leftmost_32_2 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Leftmost32_2) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_2))

prop_leftmost_32_4 :: W.Word32 -> Bool
prop_leftmost_32_4 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Leftmost32_4) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_4))

prop_leftmost_32_8 :: W.Word32 -> Bool
prop_leftmost_32_8 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Leftmost32_8) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_8))

prop_leftmost_32_16 :: W.Word32 -> Bool
prop_leftmost_32_16 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Leftmost32_16) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_16))

prop_leftmost_64_1 :: W.Word64 -> Bool
prop_leftmost_64_1 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_1) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_1))

prop_leftmost_64_2 :: W.Word64 -> Bool
prop_leftmost_64_2 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_2) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_2))

prop_leftmost_64_4 :: W.Word64 -> Bool
prop_leftmost_64_4 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_4) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_4))

prop_leftmost_64_8 :: W.Word64 -> Bool
prop_leftmost_64_8 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_8) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_8))

prop_leftmost_64_16 :: W.Word64 -> Bool
prop_leftmost_64_16 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_16) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_16))

prop_leftmost_64_32 :: W.Word64 -> Bool
prop_leftmost_64_32 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Leftmost64_32) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_32))

prop_rightmost_8_1 :: W.Word8 -> Bool
prop_rightmost_8_1 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Rightmost8_1) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_1))

prop_rightmost_8_2 :: W.Word8 -> Bool
prop_rightmost_8_2 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Rightmost8_2) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_2))

prop_rightmost_8_4 :: W.Word8 -> Bool
prop_rightmost_8_4 = \x -> let input = toW8 x
                            in fastF input == implementation (WordJet Rightmost8_4) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_4))

prop_rightmost_16_1 :: W.Word16 -> Bool
prop_rightmost_16_1 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Rightmost16_1) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_1))

prop_rightmost_16_2 :: W.Word16 -> Bool
prop_rightmost_16_2 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Rightmost16_2) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_2))

prop_rightmost_16_4 :: W.Word16 -> Bool
prop_rightmost_16_4 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Rightmost16_4) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_4))

prop_rightmost_16_8 :: W.Word16 -> Bool
prop_rightmost_16_8 = \x -> let input = toW16 x
                            in fastF input == implementation (WordJet Rightmost16_8) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_8))

prop_rightmost_32_1 :: W.Word32 -> Bool
prop_rightmost_32_1 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Rightmost32_1) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_1))

prop_rightmost_32_2 :: W.Word32 -> Bool
prop_rightmost_32_2 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Rightmost32_2) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_2))

prop_rightmost_32_4 :: W.Word32 -> Bool
prop_rightmost_32_4 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Rightmost32_4) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_4))

prop_rightmost_32_8 :: W.Word32 -> Bool
prop_rightmost_32_8 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Rightmost32_8) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_8))

prop_rightmost_32_16 :: W.Word32 -> Bool
prop_rightmost_32_16 = \x -> let input = toW32 x
                            in fastF input == implementation (WordJet Rightmost32_16) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_16))

prop_rightmost_64_1 :: W.Word64 -> Bool
prop_rightmost_64_1 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_1) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_1))

prop_rightmost_64_2 :: W.Word64 -> Bool
prop_rightmost_64_2 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_2) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_2))

prop_rightmost_64_4 :: W.Word64 -> Bool
prop_rightmost_64_4 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_4) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_4))

prop_rightmost_64_8 :: W.Word64 -> Bool
prop_rightmost_64_8 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_8) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_8))

prop_rightmost_64_16 :: W.Word64 -> Bool
prop_rightmost_64_16 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_16) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_16))

prop_rightmost_64_32 :: W.Word64 -> Bool
prop_rightmost_64_32 = \x -> let input = toW64 x
                            in fastF input == implementation (WordJet Rightmost64_32) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_32))

prop_left_pad_low_1_8 :: Bool -> Bool
prop_left_pad_low_1_8 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadLow1_8) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_8))

prop_left_pad_low_1_16 :: Bool -> Bool
prop_left_pad_low_1_16 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadLow1_16) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_16))

prop_left_pad_low_8_16 :: W.Word8 -> Bool
prop_left_pad_low_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadLow8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_16))

prop_left_pad_low_1_32 :: Bool -> Bool
prop_left_pad_low_1_32 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadLow1_32) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_32))

prop_left_pad_low_8_32 :: W.Word8 -> Bool
prop_left_pad_low_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadLow8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_32))

prop_left_pad_low_16_32 :: W.Word16 -> Bool
prop_left_pad_low_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftPadLow16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow16_32))

prop_left_pad_low_1_64 :: Bool -> Bool
prop_left_pad_low_1_64 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadLow1_64) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_64))

prop_left_pad_low_8_64 :: W.Word8 -> Bool
prop_left_pad_low_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadLow8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_64))

prop_left_pad_low_16_64 :: W.Word16 -> Bool
prop_left_pad_low_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftPadLow16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow16_64))

prop_left_pad_low_32_64 :: W.Word32 -> Bool
prop_left_pad_low_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet LeftPadLow32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow32_64))

prop_left_pad_high_1_8 :: Bool -> Bool
prop_left_pad_high_1_8 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadHigh1_8) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_8))

prop_left_pad_high_1_16 :: Bool -> Bool
prop_left_pad_high_1_16 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadHigh1_16) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_16))

prop_left_pad_high_8_16 :: W.Word8 -> Bool
prop_left_pad_high_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadHigh8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_16))

prop_left_pad_high_1_32 :: Bool -> Bool
prop_left_pad_high_1_32 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadHigh1_32) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_32))

prop_left_pad_high_8_32 :: W.Word8 -> Bool
prop_left_pad_high_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadHigh8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_32))

prop_left_pad_high_16_32 :: W.Word16 -> Bool
prop_left_pad_high_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftPadHigh16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh16_32))

prop_left_pad_high_1_64 :: Bool -> Bool
prop_left_pad_high_1_64 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftPadHigh1_64) input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_64))

prop_left_pad_high_8_64 :: W.Word8 -> Bool
prop_left_pad_high_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftPadHigh8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_64))

prop_left_pad_high_16_64 :: W.Word16 -> Bool
prop_left_pad_high_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftPadHigh16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh16_64))

prop_left_pad_high_32_64 :: W.Word32 -> Bool
prop_left_pad_high_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet LeftPadHigh32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh32_64))

prop_left_extend_1_8 :: Bool -> Bool
prop_left_extend_1_8 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftExtend1_8) input
 where
  fastF = testCoreEval (specification (WordJet LeftExtend1_8))

prop_left_extend_1_16 :: Bool -> Bool
prop_left_extend_1_16 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftExtend1_16) input
 where
  fastF = testCoreEval (specification (WordJet LeftExtend1_16))

prop_left_extend_8_16 :: W.Word8 -> Bool
prop_left_extend_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftExtend8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend8_16))

prop_left_extend_1_32 :: Bool -> Bool
prop_left_extend_1_32 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftExtend1_32) input
 where
  fastF = testCoreEval (specification (WordJet LeftExtend1_32))

prop_left_extend_8_32 :: W.Word8 -> Bool
prop_left_extend_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftExtend8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend8_32))

prop_left_extend_16_32 :: W.Word16 -> Bool
prop_left_extend_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftExtend16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend16_32))

prop_left_extend_1_64 :: Bool -> Bool
prop_left_extend_1_64 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet LeftExtend1_64) input
 where
  fastF = testCoreEval (specification (WordJet LeftExtend1_64))

prop_left_extend_8_64 :: W.Word8 -> Bool
prop_left_extend_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet LeftExtend8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend8_64))

prop_left_extend_16_64 :: W.Word16 -> Bool
prop_left_extend_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet LeftExtend16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend16_64))

prop_left_extend_32_64 :: W.Word32 -> Bool
prop_left_extend_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet LeftExtend32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftExtend32_64))

prop_right_pad_low_1_8 :: Bool -> Bool
prop_right_pad_low_1_8 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadLow1_8) input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_8))

prop_right_pad_low_1_16 :: Bool -> Bool
prop_right_pad_low_1_16 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadLow1_16) input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_16))

prop_right_pad_low_8_16 :: W.Word8 -> Bool
prop_right_pad_low_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadLow8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_16))

prop_right_pad_low_1_32 :: Bool -> Bool
prop_right_pad_low_1_32 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadLow1_32) input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_32))

prop_right_pad_low_8_32 :: W.Word8 -> Bool
prop_right_pad_low_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadLow8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_32))

prop_right_pad_low_16_32 :: W.Word16 -> Bool
prop_right_pad_low_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightPadLow16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow16_32))

prop_right_pad_low_1_64 :: Bool -> Bool
prop_right_pad_low_1_64 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadLow1_64) input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_64))

prop_right_pad_low_8_64 :: W.Word8 -> Bool
prop_right_pad_low_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadLow8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_64))

prop_right_pad_low_16_64 :: W.Word16 -> Bool
prop_right_pad_low_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightPadLow16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow16_64))

prop_right_pad_low_32_64 :: W.Word32 -> Bool
prop_right_pad_low_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet RightPadLow32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow32_64))

prop_right_pad_high_1_8 :: Bool -> Bool
prop_right_pad_high_1_8 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadHigh1_8) input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_8))

prop_right_pad_high_1_16 :: Bool -> Bool
prop_right_pad_high_1_16 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadHigh1_16) input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_16))

prop_right_pad_high_8_16 :: W.Word8 -> Bool
prop_right_pad_high_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadHigh8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_16))

prop_right_pad_high_1_32 :: Bool -> Bool
prop_right_pad_high_1_32 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadHigh1_32) input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_32))

prop_right_pad_high_8_32 :: W.Word8 -> Bool
prop_right_pad_high_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadHigh8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_32))

prop_right_pad_high_16_32 :: W.Word16 -> Bool
prop_right_pad_high_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightPadHigh16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh16_32))

prop_right_pad_high_1_64 :: Bool -> Bool
prop_right_pad_high_1_64 = \x -> let input = toBit x
                                in fastF input == implementation (WordJet RightPadHigh1_64) input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_64))

prop_right_pad_high_8_64 :: W.Word8 -> Bool
prop_right_pad_high_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightPadHigh8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_64))

prop_right_pad_high_16_64 :: W.Word16 -> Bool
prop_right_pad_high_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightPadHigh16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh16_64))

prop_right_pad_high_32_64 :: W.Word32 -> Bool
prop_right_pad_high_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet RightPadHigh32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh32_64))

prop_right_extend_8_16 :: W.Word8 -> Bool
prop_right_extend_8_16 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightExtend8_16) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend8_16))

prop_right_extend_8_32 :: W.Word8 -> Bool
prop_right_extend_8_32 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightExtend8_32) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend8_32))

prop_right_extend_16_32 :: W.Word16 -> Bool
prop_right_extend_16_32 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightExtend16_32) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend16_32))

prop_right_extend_8_64 :: W.Word8 -> Bool
prop_right_extend_8_64 = \x -> let input = toW8 x
                                in fastF input == implementation (WordJet RightExtend8_64) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend8_64))

prop_right_extend_16_64 :: W.Word16 -> Bool
prop_right_extend_16_64 = \x -> let input = toW16 x
                                in fastF input == implementation (WordJet RightExtend16_64) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend16_64))

prop_right_extend_32_64 :: W.Word32 -> Bool
prop_right_extend_32_64 = \x -> let input = toW32 x
                                in fastF input == implementation (WordJet RightExtend32_64) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightExtend32_64))

prop_left_shift_with_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_left_shift_with_8 = \w x y -> let input = (toBit w, (toW4 x, toW8 y))
                                  in fastF input == implementation (WordJet LeftShiftWith8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShiftWith8))

prop_left_shift_with_16 :: Bool -> W.Word8 -> W.Word16 -> Bool
prop_left_shift_with_16 = \w x y -> let input = (toBit w, (toW4 x, toW16 y))
                                  in fastF input == implementation (WordJet LeftShiftWith16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShiftWith16))

prop_left_shift_with_32 :: Bool -> W.Word8 -> W.Word32 -> Bool
prop_left_shift_with_32 = \w x y -> let input = (toBit w, (toW8 x, toW32 y))
                                  in fastF input == implementation (WordJet LeftShiftWith32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShiftWith32))

prop_left_shift_with_64 :: Bool -> W.Word8 -> W.Word64 -> Bool
prop_left_shift_with_64 = \w x y -> let input = (toBit w, (toW8 x, toW64 y))
                                  in fastF input == implementation (WordJet LeftShiftWith64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShiftWith64))

prop_left_shift_8 :: W.Word8 -> W.Word8 -> Bool
prop_left_shift_8 = \x y -> let input = (toW4 x, toW8 y)
                             in fastF input == implementation (WordJet LeftShift8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShift8))

prop_left_shift_16 :: W.Word8 -> W.Word16 -> Bool
prop_left_shift_16 = \x y -> let input = (toW4 x, toW16 y)
                              in fastF input == implementation (WordJet LeftShift16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShift16))

prop_left_shift_32 :: W.Word8 -> W.Word32 -> Bool
prop_left_shift_32 = \x y -> let input = (toW8 x, toW32 y)
                              in fastF input == implementation (WordJet LeftShift32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShift32))

prop_left_shift_64 :: W.Word8 -> W.Word64 -> Bool
prop_left_shift_64 = \x y -> let input = (toW8 x, toW64 y)
                              in fastF input == implementation (WordJet LeftShift64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftShift64))

prop_right_shift_with_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_right_shift_with_8 = \w x y -> let input = (toBit w, (toW4 x, toW8 y))
                                  in fastF input == implementation (WordJet RightShiftWith8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShiftWith8))

prop_right_shift_with_16 :: Bool -> W.Word8 -> W.Word16 -> Bool
prop_right_shift_with_16 = \w x y -> let input = (toBit w, (toW4 x, toW16 y))
                                  in fastF input == implementation (WordJet RightShiftWith16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShiftWith16))

prop_right_shift_with_32 :: Bool -> W.Word8 -> W.Word32 -> Bool
prop_right_shift_with_32 = \w x y -> let input = (toBit w, (toW8 x, toW32 y))
                                  in fastF input == implementation (WordJet RightShiftWith32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShiftWith32))

prop_right_shift_with_64 :: Bool -> W.Word8 -> W.Word64 -> Bool
prop_right_shift_with_64 = \w x y -> let input = (toBit w, (toW8 x, toW64 y))
                                  in fastF input == implementation (WordJet RightShiftWith64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShiftWith64))

prop_right_shift_8 :: W.Word8 -> W.Word8 -> Bool
prop_right_shift_8 = \x y -> let input = (toW4 x, toW8 y)
                             in fastF input == implementation (WordJet RightShift8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShift8))

prop_right_shift_16 :: W.Word8 -> W.Word16 -> Bool
prop_right_shift_16 = \x y -> let input = (toW4 x, toW16 y)
                              in fastF input == implementation (WordJet RightShift16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShift16))

prop_right_shift_32 :: W.Word8 -> W.Word32 -> Bool
prop_right_shift_32 = \x y -> let input = (toW8 x, toW32 y)
                              in fastF input == implementation (WordJet RightShift32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShift32))

prop_right_shift_64 :: W.Word8 -> W.Word64 -> Bool
prop_right_shift_64 = \x y -> let input = (toW8 x, toW64 y)
                              in fastF input == implementation (WordJet RightShift64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightShift64))

prop_left_rotate_8 :: W.Word8 -> W.Word8 -> Bool
prop_left_rotate_8 = \x y -> let input = (toW4 x, toW8 y)
                             in fastF input == implementation (WordJet LeftRotate8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftRotate8))

prop_left_rotate_16 :: W.Word8 -> W.Word16 -> Bool
prop_left_rotate_16 = \x y -> let input = (toW4 x, toW16 y)
                              in fastF input == implementation (WordJet LeftRotate16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftRotate16))

prop_left_rotate_32 :: W.Word8 -> W.Word32 -> Bool
prop_left_rotate_32 = \x y -> let input = (toW8 x, toW32 y)
                              in fastF input == implementation (WordJet LeftRotate32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftRotate32))

prop_left_rotate_64 :: W.Word8 -> W.Word64 -> Bool
prop_left_rotate_64 = \x y -> let input = (toW8 x, toW64 y)
                              in fastF input == implementation (WordJet LeftRotate64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftRotate64))

prop_right_rotate_8 :: W.Word8 -> W.Word8 -> Bool
prop_right_rotate_8 = \x y -> let input = (toW4 x, toW8 y)
                             in fastF input == implementation (WordJet RightRotate8) input
 where
  toW4 = toWord4 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightRotate8))

prop_right_rotate_16 :: W.Word8 -> W.Word16 -> Bool
prop_right_rotate_16 = \x y -> let input = (toW4 x, toW16 y)
                              in fastF input == implementation (WordJet RightRotate16) input
 where
  toW4 = toWord4 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightRotate16))

prop_right_rotate_32 :: W.Word8 -> W.Word32 -> Bool
prop_right_rotate_32 = \x y -> let input = (toW8 x, toW32 y)
                              in fastF input == implementation (WordJet RightRotate32) input
 where
  toW8 = toWord8 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightRotate32))

prop_right_rotate_64 :: W.Word8 -> W.Word64 -> Bool
prop_right_rotate_64 = \x y -> let input = (toW8 x, toW64 y)
                              in fastF input == implementation (WordJet RightRotate64) input
 where
  toW8 = toWord8 . fromIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightRotate64))

assert_one_8 :: Assertion
assert_one_8 = fastF () @=? implementation (ArithJet One8) ()
 where
  fastF = testCoreEval (specification (ArithJet One8))

assert_one_16 :: Assertion
assert_one_16 = fastF () @=? implementation (ArithJet One16) ()
 where
  fastF = testCoreEval (specification (ArithJet One16))

assert_one_32 :: Assertion
assert_one_32 = fastF () @=? implementation (ArithJet One32) ()
 where
  fastF = testCoreEval (specification (ArithJet One32))

assert_one_64 :: Assertion
assert_one_64 = fastF () @=? implementation (ArithJet One64) ()
 where
  fastF = testCoreEval (specification (ArithJet One64))

prop_add_8 :: W.Word8 -> W.Word8 -> Bool
prop_add_8 = \x y -> let input = (toW8 x, toW8 y)
                      in fastF input == implementation (ArithJet Add8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add8))

prop_add_16 :: W.Word16 -> W.Word16 -> Bool
prop_add_16 = \x y -> let input = (toW16 x, toW16 y)
                       in fastF input == implementation (ArithJet Add16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add16))

prop_add_32 :: W.Word32 -> W.Word32 -> Bool
prop_add_32 = \x y -> let input = (toW32 x, toW32 y)
                       in fastF input == implementation (ArithJet Add32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add32))

prop_add_64 :: W.Word64 -> W.Word64 -> Bool
prop_add_64 = \x y -> let input = (toW64 x, toW64 y)
                       in fastF input == implementation (ArithJet Add64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add64))

prop_full_add_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_full_add_8 = \c x y -> let input = (toBit c, (toW8 x, toW8 y))
                             in fastF input == implementation (ArithJet FullAdd8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd8))

prop_full_add_16 :: Bool -> W.Word16 -> W.Word16 -> Bool
prop_full_add_16 = \c x y -> let input = (toBit c, (toW16 x, toW16 y))
                              in fastF input == implementation (ArithJet FullAdd16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd16))

prop_full_add_32 :: Bool -> W.Word32 -> W.Word32 -> Bool
prop_full_add_32 = \c x y -> let input = (toBit c, (toW32 x, toW32 y))
                              in fastF input == implementation (ArithJet FullAdd32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd32))

prop_full_add_64 :: Bool -> W.Word64 -> W.Word64 -> Bool
prop_full_add_64 = \c x y -> let input = (toBit c, (toW64 x, toW64 y))
                              in fastF input == implementation (ArithJet FullAdd64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd64))

prop_full_increment_8 :: Bool -> W.Word8 -> Bool
prop_full_increment_8 = \b x -> let input = (toBit b, toW8 x)
                                in fastF input == implementation (ArithJet FullIncrement8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement8))

prop_full_increment_16 :: Bool -> W.Word16 -> Bool
prop_full_increment_16 = \b x -> let input = (toBit b, toW16 x)
                                 in fastF input == implementation (ArithJet FullIncrement16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement16))

prop_full_increment_32 :: Bool -> W.Word32 -> Bool
prop_full_increment_32 = \b x -> let input = (toBit b, toW32 x)
                                 in fastF input == implementation (ArithJet FullIncrement32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement32))

prop_full_increment_64 :: Bool -> W.Word64 -> Bool
prop_full_increment_64 = \b x -> let input = (toBit b, toW64 x)
                                 in fastF input == implementation (ArithJet FullIncrement64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement64))

assert_full_increment_max_8 :: Assertion
assert_full_increment_max_8 = fastF input @=? implementation (ArithJet FullIncrement8) input
 where
  input = (toBit True, toWord8 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement8))

assert_full_increment_max_16 :: Assertion
assert_full_increment_max_16 = fastF input @=? implementation (ArithJet FullIncrement16) input
 where
  input = (toBit True, toWord16 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement16))

assert_full_increment_max_32 :: Assertion
assert_full_increment_max_32 = fastF input @=? implementation (ArithJet FullIncrement32) input
 where
  input = (toBit True, toWord32 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement32))

assert_full_increment_max_64 :: Assertion
assert_full_increment_max_64 = fastF input @=? implementation (ArithJet FullIncrement64) input
 where
  input = (toBit True, toWord64 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement64))

prop_increment_8 :: W.Word8 -> Bool
prop_increment_8 = \x -> let input = toW8 x
                       in fastF input == implementation (ArithJet Increment8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment8))

prop_increment_16 :: W.Word16 -> Bool
prop_increment_16 = \x -> let input = toW16 x
                        in fastF input == implementation (ArithJet Increment16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment16))

prop_increment_32 :: W.Word32 -> Bool
prop_increment_32 = \x -> let input = toW32 x
                        in fastF input == implementation (ArithJet Increment32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment32))

prop_increment_64 :: W.Word64 -> Bool
prop_increment_64 = \x -> let input = toW64 x
                        in fastF input == implementation (ArithJet Increment64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment64))

assert_increment_max_8 :: Assertion
assert_increment_max_8 = fastF input @=? implementation (ArithJet Increment8) input
 where
  input = toWord8 (-1)
  fastF = testCoreEval (specification (ArithJet Increment8))

assert_increment_max_16 :: Assertion
assert_increment_max_16 = fastF input @=? implementation (ArithJet Increment16) input
 where
  input = toWord16 (-1)
  fastF = testCoreEval (specification (ArithJet Increment16))

assert_increment_max_32 :: Assertion
assert_increment_max_32 = fastF input @=? implementation (ArithJet Increment32) input
 where
  input = toWord32 (-1)
  fastF = testCoreEval (specification (ArithJet Increment32))

assert_increment_max_64 :: Assertion
assert_increment_max_64 = fastF input @=? implementation (ArithJet Increment64) input
 where
  input = toWord64 (-1)
  fastF = testCoreEval (specification (ArithJet Increment64))

prop_subtract_8 :: W.Word8 -> W.Word8 -> Bool
prop_subtract_8 = \x y -> let input = (toW8 x, toW8 y)
                           in fastF input == implementation (ArithJet Subtract8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract8))

prop_subtract_16 :: W.Word16 -> W.Word16 -> Bool
prop_subtract_16 = \x y -> let input = (toW16 x, toW16 y)
                            in fastF input == implementation (ArithJet Subtract16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract16))

prop_subtract_32 :: W.Word32 -> W.Word32 -> Bool
prop_subtract_32 = \x y -> let input = (toW32 x, toW32 y)
                            in fastF input == implementation (ArithJet Subtract32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract32))

prop_subtract_64 :: W.Word64 -> W.Word64 -> Bool
prop_subtract_64 = \x y -> let input = (toW64 x, toW64 y)
                            in fastF input == implementation (ArithJet Subtract64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract64))

prop_full_subtract_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_full_subtract_8 = \c x y -> let input = (toBit c, (toW8 x, toW8 y))
                                  in fastF input == implementation (ArithJet FullSubtract8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract8))

prop_full_subtract_16 :: Bool -> W.Word16 -> W.Word16 -> Bool
prop_full_subtract_16 = \c x y -> let input = (toBit c, (toW16 x, toW16 y))
                                   in fastF input == implementation (ArithJet FullSubtract16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract16))

prop_full_subtract_32 :: Bool -> W.Word32 -> W.Word32 -> Bool
prop_full_subtract_32 = \c x y -> let input = (toBit c, (toW32 x, toW32 y))
                                   in fastF input == implementation (ArithJet FullSubtract32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract32))

prop_full_subtract_64 :: Bool -> W.Word64 -> W.Word64 -> Bool
prop_full_subtract_64 = \c x y -> let input = (toBit c, (toW64 x, toW64 y))
                                   in fastF input == implementation (ArithJet FullSubtract64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract64))

prop_full_decrement_8 :: Bool -> W.Word8 -> Bool
prop_full_decrement_8 = \b x -> let input = (toBit b, toW8 x)
                                in fastF input == implementation (ArithJet FullDecrement8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement8))

prop_full_decrement_16 :: Bool -> W.Word16 -> Bool
prop_full_decrement_16 = \b x -> let input = (toBit b, toW16 x)
                                 in fastF input == implementation (ArithJet FullDecrement16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement16))

prop_full_decrement_32 :: Bool -> W.Word32 -> Bool
prop_full_decrement_32 = \b x -> let input = (toBit b, toW32 x)
                                 in fastF input == implementation (ArithJet FullDecrement32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement32))

prop_full_decrement_64 :: Bool -> W.Word64 -> Bool
prop_full_decrement_64 = \b x -> let input = (toBit b, toW64 x)
                                 in fastF input == implementation (ArithJet FullDecrement64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement64))

assert_full_decrement_zero_8 :: Assertion
assert_full_decrement_zero_8 = fastF input @=? implementation (ArithJet FullDecrement8) input
 where
  input = (toBit True, toWord8 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement8))

assert_full_decrement_zero_16 :: Assertion
assert_full_decrement_zero_16 = fastF input @=? implementation (ArithJet FullDecrement16) input
 where
  input = (toBit True, toWord16 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement16))

assert_full_decrement_zero_32 :: Assertion
assert_full_decrement_zero_32 = fastF input @=? implementation (ArithJet FullDecrement32) input
 where
  input = (toBit True, toWord32 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement32))

assert_full_decrement_zero_64 :: Assertion
assert_full_decrement_zero_64 = fastF input @=? implementation (ArithJet FullDecrement64) input
 where
  input = (toBit True, toWord64 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement64))

prop_decrement_8 :: W.Word8 -> Bool
prop_decrement_8 = \x -> let input = toW8 x
                       in fastF input == implementation (ArithJet Decrement8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement8))

prop_decrement_16 :: W.Word16 -> Bool
prop_decrement_16 = \x -> let input = toW16 x
                        in fastF input == implementation (ArithJet Decrement16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement16))

prop_decrement_32 :: W.Word32 -> Bool
prop_decrement_32 = \x -> let input = toW32 x
                        in fastF input == implementation (ArithJet Decrement32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement32))

prop_decrement_64 :: W.Word64 -> Bool
prop_decrement_64 = \x -> let input = toW64 x
                        in fastF input == implementation (ArithJet Decrement64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement64))

assert_decrement_zero_8 :: Assertion
assert_decrement_zero_8 = fastF input @=? implementation (ArithJet Decrement8) input
 where
  input = toWord8 0
  fastF = testCoreEval (specification (ArithJet Decrement8))

assert_decrement_zero_16 :: Assertion
assert_decrement_zero_16 = fastF input @=? implementation (ArithJet Decrement16) input
 where
  input = toWord16 0
  fastF = testCoreEval (specification (ArithJet Decrement16))

assert_decrement_zero_32 :: Assertion
assert_decrement_zero_32 = fastF input @=? implementation (ArithJet Decrement32) input
 where
  input = toWord32 0
  fastF = testCoreEval (specification (ArithJet Decrement32))

assert_decrement_zero_64 :: Assertion
assert_decrement_zero_64 = fastF input @=? implementation (ArithJet Decrement64) input
 where
  input = toWord64 0
  fastF = testCoreEval (specification (ArithJet Decrement64))

prop_negate_8 :: W.Word8 -> Bool
prop_negate_8 = \x -> let input = toW8 x
                       in fastF input == implementation (ArithJet Negate8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate8))

prop_negate_16 :: W.Word16 -> Bool
prop_negate_16 = \x -> let input = toW16 x
                        in fastF input == implementation (ArithJet Negate16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate16))

prop_negate_32 :: W.Word32 -> Bool
prop_negate_32 = \x -> let input = toW32 x
                        in fastF input == implementation (ArithJet Negate32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate32))

prop_negate_64 :: W.Word64 -> Bool
prop_negate_64 = \x -> let input = toW64 x
                        in fastF input == implementation (ArithJet Negate64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate64))

prop_multiply_8 :: W.Word8 -> W.Word8 -> Bool
prop_multiply_8 = \x y -> let input = (toW8 x, toW8 y)
                           in fastF input == implementation (ArithJet Multiply8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply8))

prop_multiply_16 :: W.Word16 -> W.Word16 -> Bool
prop_multiply_16 = \x y -> let input = (toW16 x, toW16 y)
                            in fastF input == implementation (ArithJet Multiply16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply16))

prop_multiply_32 :: W.Word32 -> W.Word32 -> Bool
prop_multiply_32 = \x y -> let input = (toW32 x, toW32 y)
                            in fastF input == implementation (ArithJet Multiply32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply32))

prop_multiply_64 :: W.Word64 -> W.Word64 -> Bool
prop_multiply_64 = \x y -> let input = (toW64 x, toW64 y)
                            in fastF input == implementation (ArithJet Multiply64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply64))

prop_full_multiply_8 :: W.Word8 -> W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_full_multiply_8 = \x y z w -> let input = ((toW8 x, toW8 y), (toW8 z, toW8 w))
                                    in fastF input == implementation (ArithJet FullMultiply8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply8))

prop_full_multiply_16 :: W.Word16 -> W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_full_multiply_16 = \x y z w -> let input = ((toW16 x, toW16 y), (toW16 z, toW16 w))
                                     in fastF input == implementation (ArithJet FullMultiply16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply16))

prop_full_multiply_32 :: W.Word32 -> W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_full_multiply_32 = \x y z w -> let input = ((toW32 x, toW32 y), (toW32 z, toW32 w))
                                     in fastF input == implementation (ArithJet FullMultiply32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply32))

prop_full_multiply_64 :: W.Word64 -> W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_full_multiply_64 = \x y z w -> let input = ((toW64 x, toW64 y), (toW64 z, toW64 w))
                                     in fastF input == implementation (ArithJet FullMultiply64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply64))

prop_is_zero_8 :: W.Word8 -> Bool
prop_is_zero_8 = \x -> let input = toW8 x
                       in fastF input == implementation (ArithJet IsZero8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero8))

prop_is_zero_16 :: W.Word16 -> Bool
prop_is_zero_16 = \x -> let input = toW16 x
                        in fastF input == implementation (ArithJet IsZero16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero16))

prop_is_zero_32 :: W.Word32 -> Bool
prop_is_zero_32 = \x -> let input = toW32 x
                        in fastF input == implementation (ArithJet IsZero32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero32))

prop_is_zero_64 :: W.Word64 -> Bool
prop_is_zero_64 = \x -> let input = toW64 x
                        in fastF input == implementation (ArithJet IsZero64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero64))

assert_zero_is_zero_8 :: Assertion
assert_zero_is_zero_8 = fastF input @=? implementation (ArithJet IsZero8) input
 where
  input = toWord8 0
  fastF = testCoreEval (specification (ArithJet IsZero8))

assert_zero_is_zero_16 :: Assertion
assert_zero_is_zero_16 = fastF input @=? implementation (ArithJet IsZero16) input
 where
  input = toWord16 0
  fastF = testCoreEval (specification (ArithJet IsZero16))

assert_zero_is_zero_32 :: Assertion
assert_zero_is_zero_32 = fastF input @=? implementation (ArithJet IsZero32) input
 where
  input = toWord32 0
  fastF = testCoreEval (specification (ArithJet IsZero32))

assert_zero_is_zero_64 :: Assertion
assert_zero_is_zero_64 = fastF input @=? implementation (ArithJet IsZero64) input
 where
  input = toWord64 0
  fastF = testCoreEval (specification (ArithJet IsZero64))

prop_is_one_8 :: W.Word8 -> Bool
prop_is_one_8 = \x -> let input = toW8 x
                       in fastF input == implementation (ArithJet IsOne8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne8))

prop_is_one_16 :: W.Word16 -> Bool
prop_is_one_16 = \x -> let input = toW16 x
                        in fastF input == implementation (ArithJet IsOne16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne16))

prop_is_one_32 :: W.Word32 -> Bool
prop_is_one_32 = \x -> let input = toW32 x
                        in fastF input == implementation (ArithJet IsOne32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne32))

prop_is_one_64 :: W.Word64 -> Bool
prop_is_one_64 = \x -> let input = toW64 x
                        in fastF input == implementation (ArithJet IsOne64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne64))

assert_one_is_one_8 :: Assertion
assert_one_is_one_8 = fastF input @=? implementation (ArithJet IsOne8) input
 where
  input = toWord8 1
  fastF = testCoreEval (specification (ArithJet IsOne8))

assert_one_is_one_16 :: Assertion
assert_one_is_one_16 = fastF input @=? implementation (ArithJet IsOne16) input
 where
  input = toWord16 1
  fastF = testCoreEval (specification (ArithJet IsOne16))

assert_one_is_one_32 :: Assertion
assert_one_is_one_32 = fastF input @=? implementation (ArithJet IsOne32) input
 where
  input = toWord32 1
  fastF = testCoreEval (specification (ArithJet IsOne32))

assert_one_is_one_64 :: Assertion
assert_one_is_one_64 = fastF input @=? implementation (ArithJet IsOne64) input
 where
  input = toWord64 1
  fastF = testCoreEval (specification (ArithJet IsOne64))

prop_le_8 :: W.Word8 -> W.Word8 -> Bool
prop_le_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Le8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le8))

prop_le_16 :: W.Word16 -> W.Word16 -> Bool
prop_le_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Le16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le16))

prop_le_32 :: W.Word32 -> W.Word32 -> Bool
prop_le_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Le32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le32))

prop_le_64 :: W.Word64 -> W.Word64 -> Bool
prop_le_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Le64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le64))

prop_le_diag_8 :: W.Word8 -> Bool
prop_le_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == implementation (ArithJet Le8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le8))

prop_le_diag_16 :: W.Word16 -> Bool
prop_le_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == implementation (ArithJet Le16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le16))

prop_le_diag_32 :: W.Word32 -> Bool
prop_le_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == implementation (ArithJet Le32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le32))

prop_le_diag_64 :: W.Word64 -> Bool
prop_le_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == implementation (ArithJet Le64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le64))

prop_lt_8 :: W.Word8 -> W.Word8 -> Bool
prop_lt_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Lt8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt8))

prop_lt_16 :: W.Word16 -> W.Word16 -> Bool
prop_lt_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Lt16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt16))

prop_lt_32 :: W.Word32 -> W.Word32 -> Bool
prop_lt_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Lt32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt32))

prop_lt_64 :: W.Word64 -> W.Word64 -> Bool
prop_lt_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Lt64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt64))

prop_lt_diag_8 :: W.Word8 -> Bool
prop_lt_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == implementation (ArithJet Lt8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt8))

prop_lt_diag_16 :: W.Word16 -> Bool
prop_lt_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == implementation (ArithJet Lt16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt16))

prop_lt_diag_32 :: W.Word32 -> Bool
prop_lt_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == implementation (ArithJet Lt32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt32))

prop_lt_diag_64 :: W.Word64 -> Bool
prop_lt_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == implementation (ArithJet Lt64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt64))

prop_min_8 :: W.Word8 -> W.Word8 -> Bool
prop_min_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Min8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min8))

prop_min_16 :: W.Word16 -> W.Word16 -> Bool
prop_min_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Min16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min16))

prop_min_32 :: W.Word32 -> W.Word32 -> Bool
prop_min_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Min32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min32))

prop_min_64 :: W.Word64 -> W.Word64 -> Bool
prop_min_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Min64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min64))

prop_max_8 :: W.Word8 -> W.Word8 -> Bool
prop_max_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Max8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max8))

prop_max_16 :: W.Word16 -> W.Word16 -> Bool
prop_max_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Max16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max16))

prop_max_32 :: W.Word32 -> W.Word32 -> Bool
prop_max_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Max32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max32))

prop_max_64 :: W.Word64 -> W.Word64 -> Bool
prop_max_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Max64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max64))

prop_median_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_median_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == implementation (ArithJet Median8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median8))

prop_median_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_median_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == implementation (ArithJet Median16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median16))

prop_median_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_median_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == implementation (ArithJet Median32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median32))

prop_median_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_median_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == implementation (ArithJet Median64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median64))

prop_div_mod_8 :: W.Word8 -> W.Word8 -> Bool
prop_div_mod_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet DivMod8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod8))

prop_div_mod_16 :: W.Word16 -> W.Word16 -> Bool
prop_div_mod_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet DivMod16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod16))

prop_div_mod_32 :: W.Word32 -> W.Word32 -> Bool
prop_div_mod_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet DivMod32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod32))

prop_div_mod_64 :: W.Word64 -> W.Word64 -> Bool
prop_div_mod_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet DivMod64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod64))

prop_divide_8 :: W.Word8 -> W.Word8 -> Bool
prop_divide_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Divide8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide8))

prop_divide_16 :: W.Word16 -> W.Word16 -> Bool
prop_divide_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Divide16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide16))

prop_divide_32 :: W.Word32 -> W.Word32 -> Bool
prop_divide_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Divide32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide32))

prop_divide_64 :: W.Word64 -> W.Word64 -> Bool
prop_divide_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Divide64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide64))

prop_modulo_8 :: W.Word8 -> W.Word8 -> Bool
prop_modulo_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Modulo8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo8))

prop_modulo_16 :: W.Word16 -> W.Word16 -> Bool
prop_modulo_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Modulo16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo16))

prop_modulo_32 :: W.Word32 -> W.Word32 -> Bool
prop_modulo_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Modulo32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo32))

prop_modulo_64 :: W.Word64 -> W.Word64 -> Bool
prop_modulo_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Modulo64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo64))

prop_divides_8 :: W.Word8 -> W.Word8 -> Bool
prop_divides_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == implementation (ArithJet Divides8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides8))

prop_divides_16 :: W.Word16 -> W.Word16 -> Bool
prop_divides_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == implementation (ArithJet Divides16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides16))

prop_divides_32 :: W.Word32 -> W.Word32 -> Bool
prop_divides_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == implementation (ArithJet Divides32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides32))

prop_divides_64 :: W.Word64 -> W.Word64 -> Bool
prop_divides_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == implementation (ArithJet Divides64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides64))

prop_div_mod_zero_8 :: W.Word8 -> Bool
prop_div_mod_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == implementation (ArithJet DivMod8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod8))

prop_div_mod_zero_16 :: W.Word16 -> Bool
prop_div_mod_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == implementation (ArithJet DivMod16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod16))

prop_div_mod_zero_32 :: W.Word32 -> Bool
prop_div_mod_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == implementation (ArithJet DivMod32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod32))

prop_div_mod_zero_64 :: W.Word64 -> Bool
prop_div_mod_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == implementation (ArithJet DivMod64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod64))

prop_divide_zero_8 :: W.Word8 -> Bool
prop_divide_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == implementation (ArithJet Divide8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide8))

prop_divide_zero_16 :: W.Word16 -> Bool
prop_divide_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == implementation (ArithJet Divide16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide16))

prop_divide_zero_32 :: W.Word32 -> Bool
prop_divide_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == implementation (ArithJet Divide32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide32))

prop_divide_zero_64 :: W.Word64 -> Bool
prop_divide_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == implementation (ArithJet Divide64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide64))

prop_modulo_zero_8 :: W.Word8 -> Bool
prop_modulo_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == implementation (ArithJet Modulo8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo8))

prop_modulo_zero_16 :: W.Word16 -> Bool
prop_modulo_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == implementation (ArithJet Modulo16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo16))

prop_modulo_zero_32 :: W.Word32 -> Bool
prop_modulo_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == implementation (ArithJet Modulo32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo32))

prop_modulo_zero_64 :: W.Word64 -> Bool
prop_modulo_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == implementation (ArithJet Modulo64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo64))

prop_divides_zero_8 :: W.Word8 -> Bool
prop_divides_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == implementation (ArithJet Divides8) input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides8))

prop_divides_zero_16 :: W.Word16 -> Bool
prop_divides_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == implementation (ArithJet Divides16) input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides16))

prop_divides_zero_32 :: W.Word32 -> Bool
prop_divides_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == implementation (ArithJet Divides32) input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides32))

prop_divides_zero_64 :: W.Word64 -> Bool
prop_divides_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == implementation (ArithJet Divides64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides64))

prop_div_mod_128_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Property
prop_div_mod_128_64 = \xh0 xl0 y0 ->
  let y = y0 .|. 2^63
      xh = y - 1 - xh0 `mod` y
      xl = - xl0
      input = ((toW64 xh, toW64 xl), toW64 y)
      x = toInteger xh * 2^64 + toInteger xl
      qh = (x `div` 2^32) `div` toInteger y
      approxQh = toInteger xh `div` (toInteger y `div` 2^32)
      annotate | 2^32 <= approxQh = label "high approxQh"
               | otherwise = label ("deltaQh: " ++ show (approxQh -qh))
   in annotate $ fastF input == implementation (ArithJet DivMod128_64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod128_64))

prop_div_mod_128_64_low_y :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_div_mod_128_64_low_y = \xh0 xl0 y0 ->
  let y = y0 `mod` 2^63
      xh = y - xh0 `mod` (y + 1)
      xl = - xl0
      input = ((toW64 xh, toW64 xl), toW64 y)
   in fastF input == implementation (ArithJet DivMod128_64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod128_64))

prop_div_mod_128_64_high_x :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_div_mod_128_64_high_x = \xh0 xl0 y0 ->
  let y = y0
      xh = - xh0
      xl = - xl0
      input = ((toW64 xh, toW64 xl), toW64 y)
   in fastF input == implementation (ArithJet DivMod128_64) input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod128_64))

assert_sha_256_iv :: Assertion
assert_sha_256_iv = fastF () @=? implementation (HashJet Sha256Iv) ()
 where
  fastF = testCoreEval (specification (HashJet Sha256Iv))

prop_sha_256_block :: HashElement -> HashElement -> HashElement -> Bool
prop_sha_256_block = \h b1 b2 ->
  let input = (heAsTy h, (heAsTy b1, heAsTy b2))
  in implementation (HashJet Sha256Block) input == fastF input
 where
  fastF = testCoreEval (specification (HashJet Sha256Block))

assert_sha_256_ctx_8_init :: Assertion
assert_sha_256_ctx_8_init = fastF () @=? implementation (HashJet Sha256Ctx8Init) ()
 where
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Init))

prop_sha_256_ctx_8_add_1 :: Sha256CtxElement -> W.Word8 -> Bool
prop_sha_256_ctx_8_add_1 = \ce w -> fastF (ctxAsTy ce, toW8 w) == implementation (HashJet Sha256Ctx8Add1) (ctxAsTy ce, toW8 w)
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add1))

prop_sha_256_ctx_8_add_2 :: Sha256CtxElement -> W.Word16 -> Bool
prop_sha_256_ctx_8_add_2 = \ce w -> fastF (ctxAsTy ce, toW16 w) == implementation (HashJet Sha256Ctx8Add2) (ctxAsTy ce, toW16 w)
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add2))

prop_sha_256_ctx_8_add_4 :: Sha256CtxElement -> W.Word32 -> Bool
prop_sha_256_ctx_8_add_4 = \ce w -> fastF (ctxAsTy ce, toW32 w) == implementation (HashJet Sha256Ctx8Add4) (ctxAsTy ce, toW32 w)
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add4))

prop_sha_256_ctx_8_add_8 :: Sha256CtxElement -> W.Word64 -> Bool
prop_sha_256_ctx_8_add_8 = \ce w -> fastF (ctxAsTy ce, toW64 w) == implementation (HashJet Sha256Ctx8Add8) (ctxAsTy ce, toW64 w)
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add8))

prop_sha_256_ctx_8_add_16 :: Sha256CtxElement -> (W.Word64, W.Word64) -> Bool
prop_sha_256_ctx_8_add_16 = \ce (w1, w2) -> fastF (ctxAsTy ce, (toW64 w1, toW64 w2)) == implementation (HashJet Sha256Ctx8Add16) (ctxAsTy ce, (toW64 w1, toW64 w2))
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add16))

prop_sha_256_ctx_8_add_32 :: Sha256CtxElement -> W.Word256 -> Bool
prop_sha_256_ctx_8_add_32 = \ce w -> fastF (ctxAsTy ce, toW256 w) == implementation (HashJet Sha256Ctx8Add32) (ctxAsTy ce, toW256 w)
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add32))

prop_sha_256_ctx_8_add_64 :: Sha256CtxElement -> (W.Word256, W.Word256) -> Bool
prop_sha_256_ctx_8_add_64 = \ce (w1, w2) -> fastF (ctxAsTy ce, (toW256 w1, toW256 w2)) == implementation (HashJet Sha256Ctx8Add64) (ctxAsTy ce, (toW256 w1, toW256 w2))
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add64))

prop_sha_256_ctx_8_add_128 :: Sha256CtxElement -> ((W.Word256, W.Word256), (W.Word256, W.Word256)) -> Bool
prop_sha_256_ctx_8_add_128 = \ce ws ->
   let input = (ctxAsTy ce, over (both_.both_) toW256 ws)
   in fastF input == implementation (HashJet Sha256Ctx8Add128) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add128))

prop_sha_256_ctx_8_add_256 :: Sha256CtxElement -> (((W.Word256, W.Word256), (W.Word256, W.Word256)), ((W.Word256, W.Word256), (W.Word256, W.Word256))) -> Bool
prop_sha_256_ctx_8_add_256 = \ce ws ->
   let input = (ctxAsTy ce, over (both_.both_.both_) toW256 ws)
   in fastF input == implementation (HashJet Sha256Ctx8Add256) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add256))

prop_sha_256_ctx_8_add_512 :: Sha256CtxElement -> ((((W.Word256, W.Word256), (W.Word256, W.Word256)), ((W.Word256, W.Word256), (W.Word256, W.Word256))),
                                                   (((W.Word256, W.Word256), (W.Word256, W.Word256)), ((W.Word256, W.Word256), (W.Word256, W.Word256)))) -> Bool
prop_sha_256_ctx_8_add_512 = \ce ws ->
   let input = (ctxAsTy ce, over (both_.both_.both_.both_) toW256 ws)
   in fastF input == implementation (HashJet Sha256Ctx8Add512) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add512))

prop_sha_256_ctx_8_add_buffer_511 :: Int -> Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_buffer_511 = \preLen ce -> forAll (vectorOf (preLen `mod` 512) arbitraryBoundedIntegral)
                                  $ \ws -> let input = (ctxAsTy ce, fst $ bufferFill buffer511 (toW8 <$> ws))
                                           in fastF input == implementation (HashJet Sha256Ctx8AddBuffer511) input
 where
  toW8 :: W.Word8 -> Word8
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8AddBuffer511))

prop_sha_256_ctx_8_finalize :: Sha256CtxElement -> Bool
prop_sha_256_ctx_8_finalize = \ce -> fastF (ctxAsTy ce) == implementation (HashJet Sha256Ctx8Finalize) (ctxAsTy ce)
 where
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Finalize))

prop_fe_normalize :: FieldElement -> Bool
prop_fe_normalize a = fe_normalize (feAsTy a) == toFE (feAsSpec a)

fe_unary_prop f g = \a -> fastF (feAsTy a) == Just (toFE (g (feAsSpec a)))
 where
  fastF = testCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == Just (toFE (g (feAsSpec a) (feAsSpec b)))
 where
  fastF = testCoreEval f

prop_fe_add :: FieldElement -> FieldElement -> Bool
prop_fe_add = fe_binary_prop fe_add Spec.fe_add

prop_fe_multiply :: FieldElement -> FieldElement -> Bool
prop_fe_multiply = fe_binary_prop fe_multiply Spec.fe_multiply

prop_fe_square :: FieldElement -> Bool
prop_fe_square = fe_unary_prop fe_square Spec.fe_square

prop_fe_negate :: FieldElement -> Bool
prop_fe_negate = fe_unary_prop fe_negate Spec.fe_negate

prop_fe_halve :: FieldElement -> Bool
prop_fe_halve = fe_unary_prop fe_halve Spec.fe_halve

prop_fe_invert :: FieldElement -> Bool
prop_fe_invert = fe_unary_prop fe_invert Spec.fe_invert

prop_fe_square_root :: FieldElement -> Bool
prop_fe_square_root = \a -> fastSqrt (feAsTy a) == Just ((fmap toFE . maybeToTy) (Spec.fe_square_root (feAsSpec a)))
 where
  fastSqrt = testCoreEval fe_square_root

prop_gej_rescale :: GroupElementJacobian -> FieldElement -> Bool
prop_gej_rescale = \a c -> fast_gej_rescale (gejAsTy a, feAsTy c) == Just (toGEJ (Spec.gej_rescale (gejAsSpec a) (feAsSpec c)))
 where
  fast_gej_rescale = testCoreEval gej_rescale

prop_gej_rescale_inf :: FieldElement -> Property
prop_gej_rescale_inf c = forAll gen_inf $ flip prop_gej_rescale c

prop_gej_double :: GroupElementJacobian -> Bool
prop_gej_double = \a -> fast_gej_double (gejAsTy a) == Just (toGEJ (Spec.gej_double (gejAsSpec a)))
 where
  fast_gej_double = testCoreEval gej_double

prop_gej_double_inf :: Property
prop_gej_double_inf = forAll gen_inf $ prop_gej_double

prop_gej_add_ex :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add_ex = \a b ->
  let rzc = fast_gej_add_ex (gejAsTy a, gejAsTy b)
      (rz', c') = Spec.gej_add_ex (gejAsSpec a) (gejAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_add_ex = testCoreEval gej_add_ex

prop_gej_add_ex_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_double z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_infl b = forAll gen_inf $ \a -> prop_gej_add_ex a b
prop_gej_add_ex_infr a = forAll gen_inf $ \b -> prop_gej_add_ex a b

prop_gej_add :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add = \a b -> fast_gej_add (gejAsTy a, gejAsTy b) == Just (toGEJ (gejAsSpec a <> gejAsSpec b))
 where
  fast_gej_add = testCoreEval gej_add

prop_gej_add_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_double z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_infl b = forAll gen_inf $ \a -> prop_gej_add a b
prop_gej_add_infr a = forAll gen_inf $ \b -> prop_gej_add a b

prop_gej_ge_add_ex :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_add_ex = \a b ->
  let rzc = fast_gej_ge_add_ex (gejAsTy a, geAsTy b)
      (rz', c') = Spec.gej_ge_add_ex (gejAsSpec a) (geAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_ge_add_ex = testCoreEval gej_ge_add_ex

prop_gej_ge_add_ex_double :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_double z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_opp :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_opp z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b

prop_gej_equiv :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_equiv = \a b -> fast_gej_equiv (gejAsTy a, gejAsTy b) == Just (toBit (Spec.gej_equiv (gejAsSpec a) (gejAsSpec b)))
 where
  fast_gej_equiv = testCoreEval gej_equiv

prop_gej_equiv_infl b = forAll gen_inf $ \a -> prop_gej_equiv a b
prop_gej_equiv_infr a = forAll gen_inf $ \b -> prop_gej_equiv a b
prop_gej_equiv_inf = forAll gen_inf $ \a -> forAll gen_inf $ \b -> prop_gej_equiv a b
prop_gej_equiv_true = \a c ->
   let b = Spec.gej_rescale (gejAsSpec a) (feAsSpec c)
   in fast_gej_equiv (gejAsTy a, toGEJ b) == Just (toBit (Spec.gej_equiv (gejAsSpec a) b))
 where
  fast_gej_equiv = testCoreEval gej_equiv

prop_gej_ge_equiv :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_equiv = \a b -> fast_gej_ge_equiv (gejAsTy a, geAsTy b) == Just (toBit (Spec.gej_ge_equiv (gejAsSpec a) (geAsSpec b)))
 where
  fast_gej_ge_equiv = testCoreEval gej_ge_equiv

prop_gej_x_equiv :: FieldElement -> GroupElementJacobian -> Bool -- gej_x_equiv will essentially always be false on random inputs.
prop_gej_x_equiv = \x0 a -> fast_gej_x_equiv (feAsTy x0, gejAsTy a) == Just (toBit (Spec.gej_x_equiv (feAsSpec x0) (gejAsSpec a) ))
 where
  fast_gej_x_equiv = testCoreEval gej_x_equiv

prop_gej_x_equiv_inf x0 = forAll gen_inf $ prop_gej_x_equiv x0
prop_gej_x_equiv_true y z x0 = prop_gej_x_equiv x0 a
  where
   z' = feAsSpec z
   x0' = feAsSpec x0
   a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x0' .*. z' .^. 2) y z

prop_gej_ge_equiv_inf b = forAll gen_inf $ \a -> prop_gej_ge_equiv a b
prop_gej_ge_equiv_true = \a ->
   maybe (property Discard)
   (\b -> property $ fast_gej_ge_equiv (gejAsTy a, toGE b) == Just (toBit (Spec.gej_ge_equiv (gejAsSpec a) b)))
   (Spec.gej_normalize (gejAsSpec a))
 where
  fast_gej_ge_equiv = testCoreEval gej_ge_equiv

prop_gej_x_equiv_inf_zero = prop_gej_x_equiv_inf (FieldElement 0)

prop_ge_is_on_curve :: GroupElement -> Bool
prop_ge_is_on_curve = \a -> fast_ge_is_on_curve (geAsTy a) == Just (toBit (Spec.ge_is_on_curve (geAsSpec a)))
 where
  fast_ge_is_on_curve = testCoreEval ge_is_on_curve

prop_ge_is_on_curve_half = forAll gen_half_curve prop_ge_is_on_curve

prop_gej_is_on_curve :: GroupElementJacobian -> Bool
prop_gej_is_on_curve = \a -> fast_gej_is_on_curve (gejAsTy a) == Just (toBit (Spec.gej_is_on_curve (gejAsSpec a)))
 where
  fast_gej_is_on_curve = testCoreEval gej_is_on_curve

prop_gej_is_on_curve_inf = forAll gen_inf prop_gej_is_on_curve
prop_gej_is_on_curve_inf_half = forAll gen_half_curve_inf prop_gej_is_on_curve
prop_gej_is_on_curve_half = forAll gen_half_curve_jacobian prop_gej_is_on_curve

scalar_unary_prop f g = \a -> fastF (scalarAsTy a) == Just (toScalar (g (scalarAsSpec a)))
 where
  fastF = testCoreEval f

scalar_binary_prop f g = \a b -> fastF (scalarAsTy a, scalarAsTy b) == Just (toScalar (g (scalarAsSpec a) (scalarAsSpec b)))
 where
  fastF = testCoreEval f

prop_scalar_normalize :: ScalarElement -> Bool
prop_scalar_normalize a@(ScalarElement w) = scalar_normalize (scalarAsTy a) == toScalar (Spec.scalar (toInteger w))

prop_scalar_add :: ScalarElement -> ScalarElement -> Bool
prop_scalar_add = scalar_binary_prop scalar_add Spec.scalar_add

prop_scalar_square :: ScalarElement -> Bool
prop_scalar_square = scalar_unary_prop scalar_square Spec.scalar_square

prop_scalar_multiply :: ScalarElement -> ScalarElement -> Bool
prop_scalar_multiply = scalar_binary_prop scalar_multiply Spec.scalar_multiply

prop_scalar_negate :: ScalarElement -> Bool
prop_scalar_negate = scalar_unary_prop scalar_negate Spec.scalar_negate

prop_scalar_invert :: ScalarElement -> Bool
prop_scalar_invert = scalar_unary_prop scalar_invert Spec.scalar_invert

prop_scalar_split_lambda :: ScalarElement -> Bool
prop_scalar_split_lambda = \a -> ((interp *** interp) <$> fast_scalar_split_lambda (scalarAsTy a))
                            == Just (Spec.scalar_split_lambda (scalarAsSpec a))
 where
  interp (b,x) = fromWord128 x - if fromBit b then 2^128 else 0
  fast_scalar_split_lambda = testCoreEval scalar_split_lambda

prop_wnaf5 :: WnafElement -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 5 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap fromWord4 <$> wnaf5 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^4 + x
           | otherwise = x

prop_wnaf15 :: WnafElement -> Bool
prop_wnaf15 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 15 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap (fromWord16) <$> wnaf15 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1

prop_linear_combination_1 :: ScalarElement -> GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1 = \na a ng -> fast_linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
             == Just (toGEJ (Spec.linear_combination_1 (scalarAsSpec na) (gejAsSpec a) (scalarAsSpec ng)))
 where
  fast_linear_combination_1 = testCoreEval linear_combination_1

prop_linear_combination_1_0 :: GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1_0 a ng = prop_linear_combination_1 na a ng
 where
  na = ScalarElement 0

prop_linear_combination_1_inf :: ScalarElement -> ScalarElement -> Property
prop_linear_combination_1_inf na ng = forAll gen_inf $ \a -> prop_linear_combination_1 na a ng

prop_linear_check_1 :: ScalarElement -> GroupElement -> ScalarElement -> GroupElement -> Bool
prop_linear_check_1 = \na a ng r -> fast_linear_check_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
             == Just (toBit (Spec.linear_check [(scalarAsSpec na, geAsSpec a)] (scalarAsSpec ng) (geAsSpec r)))
 where
  fast_linear_check_1 = testCoreEval linear_check_1

prop_decompress :: PointElement -> Bool
prop_decompress = \a -> fast_decompress (pointAsTy a)
             == Just ((fmap toGE . maybeToTy) (Spec.decompress (pointAsSpec a)))
 where
  fast_decompress = testCoreEval decompress

prop_point_check_1 :: ScalarElement -> PointElement -> ScalarElement -> PointElement -> Bool
prop_point_check_1 = \na a ng r -> fast_point_check_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
             == Just (toBit (Spec.point_check [(scalarAsSpec na, pointAsSpec a)] (scalarAsSpec ng) (pointAsSpec r)))
 where
  fast_point_check_1 = testCoreEval point_check_1

prop_swu :: FieldElement -> Bool
prop_swu = \a -> let input = feAsTy a in fastF input == implementation (Secp256k1Jet Swu) input
 where
  fastF = testCoreEval (specification (Secp256k1Jet Swu))

prop_hash_to_curve :: W.Word256 -> Bool
prop_hash_to_curve = \a -> let input = toW256 a in fastF input == implementation (Secp256k1Jet HashToCurve) input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (Secp256k1Jet HashToCurve))

prop_pubkey_unpack :: FieldElement -> Bool
prop_pubkey_unpack a@(FieldElement w) = fast_pubkey_unpack (feAsTy a)
                                     == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack (Spec.PubKey w)))
 where
  fast_pubkey_unpack = testCoreEval pubkey_unpack

prop_pubkey_unpack_neg :: FieldElement -> Bool
prop_pubkey_unpack_neg a@(FieldElement w) = fast_pubkey_unpack_neg (feAsTy a)
                                         == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack_neg (Spec.PubKey w)))
 where
  fast_pubkey_unpack_neg = testCoreEval pubkey_unpack_neg

prop_signature_unpack :: FieldElement -> ScalarElement -> Bool
prop_signature_unpack r@(FieldElement wr) s@(ScalarElement ws) =
  fast_signature_unpack (feAsTy r, scalarAsTy s) ==
  Just ((fmap (toFE *** toScalar) . maybeToTy) (Spec.signature_unpack (Spec.Sig wr ws)))
 where
  fast_signature_unpack = testCoreEval signature_unpack

fast_bip_0340_check = fromJust . testCoreEval bip_0340_check
 where
  fromJust (Just a) = fromBit a
  fromJust Nothing = False

group_bip_0340_check = testGroup "bip_0340_check" (zipWith case_bip_0340_check_vector [0..] bip0340Vectors)
 where
  assert_bip_0340_check_vector tv = bip0340TestResult tv @=? fast_bip_0340_check (bip0340TestAsTy tv)
  case_bip_0340_check_vector n tv = testCase name (assert_bip_0340_check_vector tv)
   where
    name = "bip_0340_vector_" ++ show n

prop_check_sig_verify :: FieldElement -> HashElement -> HashElement -> FieldElement -> ScalarElement -> Bool
prop_check_sig_verify = \pk m1 m2 r s ->
   let input = ((feAsTy pk, (heAsTy m1, heAsTy m2)), (feAsTy r, scalarAsTy s))
   in fast_check_sig_verify input == implementation (SignatureJet CheckSigVerify) input
 where
  fast_check_sig_verify = testCoreEval (specification (SignatureJet CheckSigVerify))

prop_check_sig_verify_true :: HashElement -> HashElement -> Property
prop_check_sig_verify_true = \m1 m2 ->
   let msg = sigHash (heAsSpec m1) (heAsSpec m2)
   in forAll (genSignature msg) $ \(PubKey pk, Sig r s) ->
     let input = ((toW256 pk, (heAsTy m1, heAsTy m2)), (toW256 r, toW256 s))
     in Just () == implementation (SignatureJet CheckSigVerify) input
     && Just () == fast_check_sig_verify input
 where
  toW256 = toWord256 . fromIntegral
  fast_check_sig_verify = testCoreEval (specification (SignatureJet CheckSigVerify))

prop_parse_lock = forAll arbitraryLock
                $ \a -> fastF (toW32 a) == implementation (BitcoinJet ParseLock) (toW32 a)
 where
  fastF = testCoreEval (specification (BitcoinJet ParseLock))

prop_parse_sequence a = fastF (toW32 a) == implementation (BitcoinJet ParseSequence) (toW32 a)
 where
  fastF = testCoreEval (specification (BitcoinJet ParseSequence))
