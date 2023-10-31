module Simplicity.FFI.Tests
 ( tests
 , main
 ) where

import Control.Arrow ((***))
import Lens.Family2 ((^.), (^..), over, allOf, review, zipWithOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck ( Arbitrary(..), Gen, Property, arbitraryBoundedIntegral, arbitrarySizedBoundedIntegral, shrinkIntegral
                             , choose, forAll, property, Discard(Discard), testProperty, vectorOf, withMaxSuccess
                             )
import Test.Tasty.HUnit (Assertion, (@=?), assertBool, testCase)

import Simplicity.Arbitrary
import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.Elements.Arbitrary
import qualified Simplicity.FFI.Jets as C
import Simplicity.Programs.LibSecp256k1.Lib as Prog
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.MerkleRoot
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word
import Simplicity.Bip0340
import Simplicity.Word as W

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "word" $
        [ testCase     "verify" assert_verify
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
        , testProperty "eq_1"  prop_eq_1
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
        ]
      , testGroup "arith" $
        [ testCase     "one_8" assert_one_8
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
        ]
      , testGroup "sha256" $
        [ testCase     "sha_256_iv"                   assert_sha_256_iv
        , testProperty "sha_256_block"                prop_sha_256_block
        , testCase     "sha_256_ctx_8_init"           assert_sha_256_ctx_8_init
        , testProperty "sha_256_ctx_8_add_1"          prop_sha_256_ctx_8_add_1
        , testProperty "sha_256_ctx_8_add_2"          prop_sha_256_ctx_8_add_2
        , testProperty "sha_256_ctx_8_add_4"          prop_sha_256_ctx_8_add_4
        , testProperty "sha_256_ctx_8_add_8"          prop_sha_256_ctx_8_add_8
        , testProperty "sha_256_ctx_8_add_16"         prop_sha_256_ctx_8_add_16
        , testProperty "sha_256_ctx_8_add_32"         prop_sha_256_ctx_8_add_32
        , testProperty "sha_256_ctx_8_add_64"         prop_sha_256_ctx_8_add_64
        , testProperty "sha_256_ctx_8_add_128"        prop_sha_256_ctx_8_add_128
        , testProperty "sha_256_ctx_8_add_256"        prop_sha_256_ctx_8_add_256
        , testProperty "sha_256_ctx_8_add_512"        prop_sha_256_ctx_8_add_512
        , testProperty "sha_256_ctx_8_add_buffer_511" prop_sha_256_ctx_8_add_buffer_511
        , testProperty "sha_256_ctx_8_finalize"       prop_sha_256_ctx_8_finalize
        ]
      , testGroup "locktime" $
        [ testProperty "parse_lock"     prop_parse_lock
        , testProperty "parse_sequence" prop_parse_sequence
        ]
      , testGroup "field"
        [ testProperty "fe_normlaize"     prop_fe_normalize
        , testProperty "fe_negate"        prop_fe_negate
        , testProperty "fe_add"           prop_fe_add
        , testProperty "fe_square"        prop_fe_square
        , testProperty "fe_multiply"      prop_fe_multiply
        , testProperty "fe_multiply_beta" prop_fe_multiply_beta
        , testProperty "fe_invert"        (withMaxSuccess 10 prop_fe_invert)
        , testProperty "fe_square_root"   prop_fe_square_root
        , testProperty "fe_is_zero"       prop_fe_is_zero
        , testProperty "fe_is_odd"        prop_fe_is_odd
        ]
      , testGroup "scalar"
        [ testProperty "scalar_normalize"       prop_scalar_normalize
        , testProperty "scalar_negate"          prop_scalar_negate
        , testProperty "scalar_add"             prop_scalar_add
        , testProperty "scalar_square"          prop_scalar_square
        , testProperty "scalar_multiply"        prop_scalar_multiply
        , testProperty "scalar_multiply_lambda" prop_scalar_multiply_lambda
        , testProperty "scalar_invert"          (withMaxSuccess 10 prop_scalar_invert)
        , testProperty "scalar_is_zero"         prop_scalar_is_zero
        ]
      , testGroup "group"
        [ testCase     "gej_infinity"             assert_gej_infinity
        , testProperty "gej_rescale"              prop_gej_rescale
        , testProperty "gej_rescale_inf"          prop_gej_rescale_inf
        , testProperty "gej_normalize"            prop_gej_normalize
        , testProperty "gej_normalize_inf"        prop_gej_normalize_inf
        , testProperty "gej_negate"               prop_gej_negate
        , testProperty "gej_negate_inf"           prop_gej_negate_inf
        , testProperty "ge_negate"                prop_ge_negate
        , testProperty "gej_double"               prop_gej_double
        , testProperty "gej_double_inf"           prop_gej_double_inf
        , testProperty "gej_double_zero"          prop_gej_double_zero
        , testProperty "gej_add"                  prop_gej_add
        , testProperty "gej_add_double"           prop_gej_add_double
        , testProperty "gej_add_opp"              prop_gej_add_opp
        , testProperty "gej_add_infl"             prop_gej_add_infl
        , testProperty "gej_add_infr"             prop_gej_add_infr
        , testProperty "gej_ge_add_ex_double"     prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp"        prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf"        prop_gej_ge_add_ex_inf
        , testProperty "gej_ge_add"               prop_gej_ge_add
        , testProperty "gej_is_infinity"          prop_gej_is_infinity
        , testProperty "gej_x_equiv"              prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf"          prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true"         prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero"     prop_gej_x_equiv_inf_zero
        , testProperty "gej_y_is_odd"             prop_gej_y_is_odd
        , testProperty "gej_is_on_curve"          prop_gej_is_on_curve
        , testProperty "gej_is_on_curve_inf"      prop_gej_is_on_curve_inf
        , testProperty "gej_is_on_curve_half"     prop_gej_is_on_curve_half
        , testProperty "gej_is_on_curve_inf_half" prop_gej_is_on_curve_inf_half
        , testProperty "ge_is_on_curve"           prop_ge_is_on_curve
        , testProperty "ge_is_on_curve_half"      prop_ge_is_on_curve_half
        ]
      , testGroup "ecMult"
        [ testCase     "linear_combination_1_order_6" assert_linear_combination_1_order_6
        , testProperty "linear_combination_1_inf"     prop_linear_combination_1_inf
        , testProperty "linear_combination_1_0"       prop_linear_combination_1_0
        , testProperty "linear_combination_1"         prop_linear_combination_1
        , testProperty "generate"                     prop_generate
        , testProperty "scale"                        prop_scale
        , testProperty "scale_0"                      prop_scale_0
        , testProperty "scale_inf"                    prop_scale_inf
        , testProperty "linear_verify_1_true_half"    prop_linear_verify_1_true_half
        , testProperty "linear_verify_1_0"            prop_linear_verify_1_0
        , testProperty "linear_verify_1"              prop_linear_verify_1
        ]
      , testGroup "point"
        [ testProperty "point_verify_1"      prop_point_verify_1
        , testProperty "point_verify_1_true" prop_point_verify_1
        , testProperty "decompress"          prop_decompress
        ]
      , testGroup "bip0340" $
        [ testProperty "bip_0340_verify"   prop_bip_0340_verify
        ]
        ++ zipWith case_bip_0340_verify_vector [0..] bip0340Vectors ++
        [ testProperty "check_sig_verify" prop_check_sig_verify
        , testProperty "check_sig_verify_true" prop_check_sig_verify_true
        ]
      ]
assert_verify :: Assertion
assert_verify =
  (fastF (toBit False), fastF (toBit True))
    @=?
  (C.verify (toBit False), C.verify (toBit True))
 where
  fastF = testCoreEval (specification (WordJet Verify))

assert_low_1 :: Assertion
assert_low_1 = fastF () @=? C.low_1 ()
 where
  fastF = testCoreEval (specification (WordJet Low1))

assert_low_8 :: Assertion
assert_low_8 = fastF () @=? C.low_8 ()
 where
  fastF = testCoreEval (specification (WordJet Low8))

assert_low_16 :: Assertion
assert_low_16 = fastF () @=? C.low_16 ()
 where
  fastF = testCoreEval (specification (WordJet Low16))

assert_low_32 :: Assertion
assert_low_32 = fastF () @=? C.low_32 ()
 where
  fastF = testCoreEval (specification (WordJet Low32))

assert_low_64 :: Assertion
assert_low_64 = fastF () @=? C.low_64 ()
 where
  fastF = testCoreEval (specification (WordJet Low64))

assert_high_1 :: Assertion
assert_high_1 = fastF () @=? C.high_1 ()
 where
  fastF = testCoreEval (specification (WordJet High1))

assert_high_8 :: Assertion
assert_high_8 = fastF () @=? C.high_8 ()
 where
  fastF = testCoreEval (specification (WordJet High8))

assert_high_16 :: Assertion
assert_high_16 = fastF () @=? C.high_16 ()
 where
  fastF = testCoreEval (specification (WordJet High16))

assert_high_32 :: Assertion
assert_high_32 = fastF () @=? C.high_32 ()
 where
  fastF = testCoreEval (specification (WordJet High32))

assert_high_64 :: Assertion
assert_high_64 = fastF () @=? C.high_64 ()
 where
  fastF = testCoreEval (specification (WordJet High64))

prop_complement_1 :: Bool -> Bool
prop_complement_1 = \x -> let input = toBit x
                       in fastF input == C.complement_1 input
 where
  fastF = testCoreEval (specification (WordJet Complement1))

prop_complement_8 :: W.Word8 -> Bool
prop_complement_8 = \x -> let input = toW8 x
                       in fastF input == C.complement_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement8))

prop_complement_16 :: W.Word16 -> Bool
prop_complement_16 = \x -> let input = toW16 x
                        in fastF input == C.complement_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement16))

prop_complement_32 :: W.Word32 -> Bool
prop_complement_32 = \x -> let input = toW32 x
                        in fastF input == C.complement_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement32))

prop_complement_64 :: W.Word64 -> Bool
prop_complement_64 = \x -> let input = toW64 x
                        in fastF input == C.complement_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Complement64))

prop_and_1 :: Bool -> Bool -> Bool
prop_and_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == C.and_1 input
 where
  fastF = testCoreEval (specification (WordJet And1))

prop_and_8 :: W.Word8 -> W.Word8 -> Bool
prop_and_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.and_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet And8))

prop_and_16 :: W.Word16 -> W.Word16 -> Bool
prop_and_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.and_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet And16))

prop_and_32 :: W.Word32 -> W.Word32 -> Bool
prop_and_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.and_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet And32))

prop_and_64 :: W.Word64 -> W.Word64 -> Bool
prop_and_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.and_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet And64))

prop_or_1 :: Bool -> Bool -> Bool
prop_or_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == C.or_1 input
 where
  fastF = testCoreEval (specification (WordJet Or1))

prop_or_8 :: W.Word8 -> W.Word8 -> Bool
prop_or_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.or_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or8))

prop_or_16 :: W.Word16 -> W.Word16 -> Bool
prop_or_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.or_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or16))

prop_or_32 :: W.Word32 -> W.Word32 -> Bool
prop_or_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.or_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or32))

prop_or_64 :: W.Word64 -> W.Word64 -> Bool
prop_or_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.or_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Or64))

prop_xor_1 :: Bool -> Bool -> Bool
prop_xor_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == C.xor_1 input
 where
  fastF = testCoreEval (specification (WordJet Xor1))

prop_xor_8 :: W.Word8 -> W.Word8 -> Bool
prop_xor_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.xor_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor8))

prop_xor_16 :: W.Word16 -> W.Word16 -> Bool
prop_xor_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.xor_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor16))

prop_xor_32 :: W.Word32 -> W.Word32 -> Bool
prop_xor_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.xor_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor32))

prop_xor_64 :: W.Word64 -> W.Word64 -> Bool
prop_xor_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.xor_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Xor64))

prop_maj_1 :: Bool -> Bool -> Bool -> Bool
prop_maj_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == C.maj_1 input
 where
  fastF = testCoreEval (specification (WordJet Maj1))

prop_maj_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_maj_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == C.maj_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj8))

prop_maj_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_maj_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == C.maj_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj16))

prop_maj_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_maj_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == C.maj_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj32))

prop_maj_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_maj_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == C.maj_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Maj64))

prop_xor_xor_1 :: Bool -> Bool -> Bool -> Bool
prop_xor_xor_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == C.xor_xor_1 input
 where
  fastF = testCoreEval (specification (WordJet XorXor1))

prop_xor_xor_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_xor_xor_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == C.xor_xor_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor8))

prop_xor_xor_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_xor_xor_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == C.xor_xor_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor16))

prop_xor_xor_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_xor_xor_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == C.xor_xor_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor32))

prop_xor_xor_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_xor_xor_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == C.xor_xor_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet XorXor64))

prop_ch_1 :: Bool -> Bool -> Bool -> Bool
prop_ch_1 = \x y z -> let input = (toBit x, (toBit y, toBit z))
                     in fastF input == C.ch_1 input
 where
  fastF = testCoreEval (specification (WordJet Ch1))

prop_ch_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_ch_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == C.ch_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch8))

prop_ch_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_ch_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == C.ch_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch16))

prop_ch_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_ch_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == C.ch_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch32))

prop_ch_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_ch_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == C.ch_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Ch64))

prop_some_1 :: Bool -> Bool
prop_some_1 = \x -> let input = toBit x
                       in fastF input == C.some_1 input
 where
  fastF = testCoreEval (specification (WordJet Some1))

prop_some_8 :: W.Word8 -> Bool
prop_some_8 = \x -> let input = toW8 x
                       in fastF input == C.some_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some8))

prop_some_16 :: W.Word16 -> Bool
prop_some_16 = \x -> let input = toW16 x
                        in fastF input == C.some_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some16))

prop_some_32 :: W.Word32 -> Bool
prop_some_32 = \x -> let input = toW32 x
                        in fastF input == C.some_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some32))

prop_some_64 :: W.Word64 -> Bool
prop_some_64 = \x -> let input = toW64 x
                        in fastF input == C.some_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Some64))

prop_all_8 :: W.Word8 -> Bool
prop_all_8 = \x -> let input = toW8 x
                       in fastF input == C.all_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet All8))

prop_all_16 :: W.Word16 -> Bool
prop_all_16 = \x -> let input = toW16 x
                        in fastF input == C.all_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet All16))

prop_all_32 :: W.Word32 -> Bool
prop_all_32 = \x -> let input = toW32 x
                        in fastF input == C.all_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet All32))

prop_all_64 :: W.Word64 -> Bool
prop_all_64 = \x -> let input = toW64 x
                        in fastF input == C.all_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet All64))

prop_eq_1 :: Bool -> Bool -> Bool
prop_eq_1 = \x y -> let input = (toBit x, toBit y)
                     in fastF input == C.eq_1 input
 where
  fastF = testCoreEval (specification (WordJet Eq1))

prop_eq_8 :: W.Word8 -> W.Word8 -> Bool
prop_eq_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.eq_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq8))

prop_eq_16 :: W.Word16 -> W.Word16 -> Bool
prop_eq_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.eq_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq16))

prop_eq_32 :: W.Word32 -> W.Word32 -> Bool
prop_eq_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.eq_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq32))

prop_eq_64 :: W.Word64 -> W.Word64 -> Bool
prop_eq_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.eq_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq64))

prop_eq_256 :: W.Word256 -> W.Word256 -> Bool
prop_eq_256 = \x y -> let input = (toW256 x, toW256 y)
                       in fastF input == C.eq_256 input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq256))

prop_eq_diag_8 :: W.Word8 -> Bool
prop_eq_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == C.eq_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq8))

prop_eq_diag_16 :: W.Word16 -> Bool
prop_eq_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == C.eq_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq16))

prop_eq_diag_32 :: W.Word32 -> Bool
prop_eq_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == C.eq_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq32))

prop_eq_diag_64 :: W.Word64 -> Bool
prop_eq_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == C.eq_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq64))

prop_eq_diag_256 :: W.Word256 -> Bool
prop_eq_diag_256 = \x -> let input = (toW256 x, toW256 x)
                         in fastF input == C.eq_256 input
 where
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (WordJet Eq256))

prop_full_left_shift_8_1 :: W.Word8 -> Bool -> Bool
prop_full_left_shift_8_1 = \x y -> let input = (toW8 x, toBit y)
                                   in fastF input == C.full_left_shift_8_1 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_1))

prop_full_left_shift_8_2 :: W.Word8 -> W.Word8 -> Bool
prop_full_left_shift_8_2 = \x y -> let input = (toW8 x, toW2 y)
                                   in fastF input == C.full_left_shift_8_2 input
 where
  toW8 = toWord8 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_2))

prop_full_left_shift_8_4 :: W.Word8 -> W.Word8 -> Bool
prop_full_left_shift_8_4 = \x y -> let input = (toW8 x, toW4 y)
                                   in fastF input == C.full_left_shift_8_4 input
 where
  toW8 = toWord8 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift8_4))

prop_full_left_shift_16_1 :: W.Word16 -> Bool -> Bool
prop_full_left_shift_16_1 = \x y -> let input = (toW16 x, toBit y)
                                   in fastF input == C.full_left_shift_16_1 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_1))

prop_full_left_shift_16_2 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_2 = \x y -> let input = (toW16 x, toW2 y)
                                   in fastF input == C.full_left_shift_16_2 input
 where
  toW16 = toWord16 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_2))

prop_full_left_shift_16_4 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_4 = \x y -> let input = (toW16 x, toW4 y)
                                   in fastF input == C.full_left_shift_16_4 input
 where
  toW16 = toWord16 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_4))

prop_full_left_shift_16_8 :: W.Word16 -> W.Word8 -> Bool
prop_full_left_shift_16_8 = \x y -> let input = (toW16 x, toW8 y)
                                   in fastF input == C.full_left_shift_16_8 input
 where
  toW16 = toWord16 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift16_8))

prop_full_left_shift_32_1 :: W.Word32 -> Bool -> Bool
prop_full_left_shift_32_1 = \x y -> let input = (toW32 x, toBit y)
                                   in fastF input == C.full_left_shift_32_1 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_1))

prop_full_left_shift_32_2 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_2 = \x y -> let input = (toW32 x, toW2 y)
                                   in fastF input == C.full_left_shift_32_2 input
 where
  toW32 = toWord32 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_2))

prop_full_left_shift_32_4 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_4 = \x y -> let input = (toW32 x, toW4 y)
                                   in fastF input == C.full_left_shift_32_4 input
 where
  toW32 = toWord32 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_4))

prop_full_left_shift_32_8 :: W.Word32 -> W.Word8 -> Bool
prop_full_left_shift_32_8 = \x y -> let input = (toW32 x, toW8 y)
                                   in fastF input == C.full_left_shift_32_8 input
 where
  toW32 = toWord32 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_8))

prop_full_left_shift_32_16 :: W.Word32 -> W.Word16 -> Bool
prop_full_left_shift_32_16 = \x y -> let input = (toW32 x, toW16 y)
                                   in fastF input == C.full_left_shift_32_16 input
 where
  toW32 = toWord32 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift32_16))

prop_full_left_shift_64_1 :: W.Word64 -> Bool -> Bool
prop_full_left_shift_64_1 = \x y -> let input = (toW64 x, toBit y)
                                   in fastF input == C.full_left_shift_64_1 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_1))

prop_full_left_shift_64_2 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_2 = \x y -> let input = (toW64 x, toW2 y)
                                   in fastF input == C.full_left_shift_64_2 input
 where
  toW64 = toWord64 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_2))

prop_full_left_shift_64_4 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_4 = \x y -> let input = (toW64 x, toW4 y)
                                   in fastF input == C.full_left_shift_64_4 input
 where
  toW64 = toWord64 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_4))

prop_full_left_shift_64_8 :: W.Word64 -> W.Word8 -> Bool
prop_full_left_shift_64_8 = \x y -> let input = (toW64 x, toW8 y)
                                   in fastF input == C.full_left_shift_64_8 input
 where
  toW64 = toWord64 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_8))

prop_full_left_shift_64_16 :: W.Word64 -> W.Word16 -> Bool
prop_full_left_shift_64_16 = \x y -> let input = (toW64 x, toW16 y)
                                   in fastF input == C.full_left_shift_64_16 input
 where
  toW64 = toWord64 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_16))

prop_full_left_shift_64_32 :: W.Word64 -> W.Word32 -> Bool
prop_full_left_shift_64_32 = \x y -> let input = (toW64 x, toW32 y)
                                   in fastF input == C.full_left_shift_64_32 input
 where
  toW64 = toWord64 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullLeftShift64_32))

prop_full_right_shift_8_1 :: W.Word8 -> Bool -> Bool
prop_full_right_shift_8_1 = \x y -> let input = (toBit y, toW8 x)
                                   in fastF input == C.full_right_shift_8_1 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_1))

prop_full_right_shift_8_2 :: W.Word8 -> W.Word8 -> Bool
prop_full_right_shift_8_2 = \x y -> let input = (toW2 y, toW8 x)
                                   in fastF input == C.full_right_shift_8_2 input
 where
  toW8 = toWord8 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_2))

prop_full_right_shift_8_4 :: W.Word8 -> W.Word8 -> Bool
prop_full_right_shift_8_4 = \x y -> let input = (toW4 y, toW8 x)
                                   in fastF input == C.full_right_shift_8_4 input
 where
  toW8 = toWord8 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift8_4))

prop_full_right_shift_16_1 :: W.Word16 -> Bool -> Bool
prop_full_right_shift_16_1 = \x y -> let input = (toBit y, toW16 x)
                                   in fastF input == C.full_right_shift_16_1 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_1))

prop_full_right_shift_16_2 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_2 = \x y -> let input = (toW2 y, toW16 x)
                                   in fastF input == C.full_right_shift_16_2 input
 where
  toW16 = toWord16 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_2))

prop_full_right_shift_16_4 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_4 = \x y -> let input = (toW4 y, toW16 x)
                                   in fastF input == C.full_right_shift_16_4 input
 where
  toW16 = toWord16 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_4))

prop_full_right_shift_16_8 :: W.Word16 -> W.Word8 -> Bool
prop_full_right_shift_16_8 = \x y -> let input = (toW8 y, toW16 x)
                                   in fastF input == C.full_right_shift_16_8 input
 where
  toW16 = toWord16 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift16_8))

prop_full_right_shift_32_1 :: W.Word32 -> Bool -> Bool
prop_full_right_shift_32_1 = \x y -> let input = (toBit y, toW32 x)
                                   in fastF input == C.full_right_shift_32_1 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_1))

prop_full_right_shift_32_2 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_2 = \x y -> let input = (toW2 y, toW32 x)
                                   in fastF input == C.full_right_shift_32_2 input
 where
  toW32 = toWord32 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_2))

prop_full_right_shift_32_4 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_4 = \x y -> let input = (toW4 y, toW32 x)
                                   in fastF input == C.full_right_shift_32_4 input
 where
  toW32 = toWord32 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_4))

prop_full_right_shift_32_8 :: W.Word32 -> W.Word8 -> Bool
prop_full_right_shift_32_8 = \x y -> let input = (toW8 y, toW32 x)
                                   in fastF input == C.full_right_shift_32_8 input
 where
  toW32 = toWord32 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_8))

prop_full_right_shift_32_16 :: W.Word32 -> W.Word16 -> Bool
prop_full_right_shift_32_16 = \x y -> let input = (toW16 y, toW32 x)
                                   in fastF input == C.full_right_shift_32_16 input
 where
  toW32 = toWord32 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift32_16))

prop_full_right_shift_64_1 :: W.Word64 -> Bool -> Bool
prop_full_right_shift_64_1 = \x y -> let input = (toBit y, toW64 x)
                                   in fastF input == C.full_right_shift_64_1 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_1))

prop_full_right_shift_64_2 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_2 = \x y -> let input = (toW2 y, toW64 x)
                                   in fastF input == C.full_right_shift_64_2 input
 where
  toW64 = toWord64 . fromIntegral
  toW2 = toWord2 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_2))

prop_full_right_shift_64_4 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_4 = \x y -> let input = (toW4 y, toW64 x)
                                   in fastF input == C.full_right_shift_64_4 input
 where
  toW64 = toWord64 . fromIntegral
  toW4 = toWord4 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_4))

prop_full_right_shift_64_8 :: W.Word64 -> W.Word8 -> Bool
prop_full_right_shift_64_8 = \x y -> let input = (toW8 y, toW64 x)
                                   in fastF input == C.full_right_shift_64_8 input
 where
  toW64 = toWord64 . fromIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_8))

prop_full_right_shift_64_16 :: W.Word64 -> W.Word16 -> Bool
prop_full_right_shift_64_16 = \x y -> let input = (toW16 y, toW64 x)
                                   in fastF input == C.full_right_shift_64_16 input
 where
  toW64 = toWord64 . fromIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_16))

prop_full_right_shift_64_32 :: W.Word64 -> W.Word32 -> Bool
prop_full_right_shift_64_32 = \x y -> let input = (toW32 y, toW64 x)
                                   in fastF input == C.full_right_shift_64_32 input
 where
  toW64 = toWord64 . fromIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet FullRightShift64_32))

prop_leftmost_8_1 :: W.Word8 -> Bool
prop_leftmost_8_1 = \x -> let input = toW8 x
                            in fastF input == C.leftmost_8_1 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_1))

prop_leftmost_8_2 :: W.Word8 -> Bool
prop_leftmost_8_2 = \x -> let input = toW8 x
                            in fastF input == C.leftmost_8_2 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_2))

prop_leftmost_8_4 :: W.Word8 -> Bool
prop_leftmost_8_4 = \x -> let input = toW8 x
                            in fastF input == C.leftmost_8_4 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost8_4))

prop_leftmost_16_1 :: W.Word16 -> Bool
prop_leftmost_16_1 = \x -> let input = toW16 x
                            in fastF input == C.leftmost_16_1 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_1))

prop_leftmost_16_2 :: W.Word16 -> Bool
prop_leftmost_16_2 = \x -> let input = toW16 x
                            in fastF input == C.leftmost_16_2 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_2))

prop_leftmost_16_4 :: W.Word16 -> Bool
prop_leftmost_16_4 = \x -> let input = toW16 x
                            in fastF input == C.leftmost_16_4 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_4))

prop_leftmost_16_8 :: W.Word16 -> Bool
prop_leftmost_16_8 = \x -> let input = toW16 x
                            in fastF input == C.leftmost_16_8 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost16_8))

prop_leftmost_32_1 :: W.Word32 -> Bool
prop_leftmost_32_1 = \x -> let input = toW32 x
                            in fastF input == C.leftmost_32_1 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_1))

prop_leftmost_32_2 :: W.Word32 -> Bool
prop_leftmost_32_2 = \x -> let input = toW32 x
                            in fastF input == C.leftmost_32_2 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_2))

prop_leftmost_32_4 :: W.Word32 -> Bool
prop_leftmost_32_4 = \x -> let input = toW32 x
                            in fastF input == C.leftmost_32_4 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_4))

prop_leftmost_32_8 :: W.Word32 -> Bool
prop_leftmost_32_8 = \x -> let input = toW32 x
                            in fastF input == C.leftmost_32_8 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_8))

prop_leftmost_32_16 :: W.Word32 -> Bool
prop_leftmost_32_16 = \x -> let input = toW32 x
                            in fastF input == C.leftmost_32_16 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost32_16))

prop_leftmost_64_1 :: W.Word64 -> Bool
prop_leftmost_64_1 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_1 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_1))

prop_leftmost_64_2 :: W.Word64 -> Bool
prop_leftmost_64_2 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_2 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_2))

prop_leftmost_64_4 :: W.Word64 -> Bool
prop_leftmost_64_4 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_4 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_4))

prop_leftmost_64_8 :: W.Word64 -> Bool
prop_leftmost_64_8 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_8 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_8))

prop_leftmost_64_16 :: W.Word64 -> Bool
prop_leftmost_64_16 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_16 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_16))

prop_leftmost_64_32 :: W.Word64 -> Bool
prop_leftmost_64_32 = \x -> let input = toW64 x
                            in fastF input == C.leftmost_64_32 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Leftmost64_32))

prop_rightmost_8_1 :: W.Word8 -> Bool
prop_rightmost_8_1 = \x -> let input = toW8 x
                            in fastF input == C.rightmost_8_1 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_1))

prop_rightmost_8_2 :: W.Word8 -> Bool
prop_rightmost_8_2 = \x -> let input = toW8 x
                            in fastF input == C.rightmost_8_2 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_2))

prop_rightmost_8_4 :: W.Word8 -> Bool
prop_rightmost_8_4 = \x -> let input = toW8 x
                            in fastF input == C.rightmost_8_4 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost8_4))

prop_rightmost_16_1 :: W.Word16 -> Bool
prop_rightmost_16_1 = \x -> let input = toW16 x
                            in fastF input == C.rightmost_16_1 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_1))

prop_rightmost_16_2 :: W.Word16 -> Bool
prop_rightmost_16_2 = \x -> let input = toW16 x
                            in fastF input == C.rightmost_16_2 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_2))

prop_rightmost_16_4 :: W.Word16 -> Bool
prop_rightmost_16_4 = \x -> let input = toW16 x
                            in fastF input == C.rightmost_16_4 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_4))

prop_rightmost_16_8 :: W.Word16 -> Bool
prop_rightmost_16_8 = \x -> let input = toW16 x
                            in fastF input == C.rightmost_16_8 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost16_8))

prop_rightmost_32_1 :: W.Word32 -> Bool
prop_rightmost_32_1 = \x -> let input = toW32 x
                            in fastF input == C.rightmost_32_1 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_1))

prop_rightmost_32_2 :: W.Word32 -> Bool
prop_rightmost_32_2 = \x -> let input = toW32 x
                            in fastF input == C.rightmost_32_2 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_2))

prop_rightmost_32_4 :: W.Word32 -> Bool
prop_rightmost_32_4 = \x -> let input = toW32 x
                            in fastF input == C.rightmost_32_4 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_4))

prop_rightmost_32_8 :: W.Word32 -> Bool
prop_rightmost_32_8 = \x -> let input = toW32 x
                            in fastF input == C.rightmost_32_8 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_8))

prop_rightmost_32_16 :: W.Word32 -> Bool
prop_rightmost_32_16 = \x -> let input = toW32 x
                            in fastF input == C.rightmost_32_16 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost32_16))

prop_rightmost_64_1 :: W.Word64 -> Bool
prop_rightmost_64_1 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_1 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_1))

prop_rightmost_64_2 :: W.Word64 -> Bool
prop_rightmost_64_2 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_2 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_2))

prop_rightmost_64_4 :: W.Word64 -> Bool
prop_rightmost_64_4 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_4 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_4))

prop_rightmost_64_8 :: W.Word64 -> Bool
prop_rightmost_64_8 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_8 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_8))

prop_rightmost_64_16 :: W.Word64 -> Bool
prop_rightmost_64_16 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_16 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_16))

prop_rightmost_64_32 :: W.Word64 -> Bool
prop_rightmost_64_32 = \x -> let input = toW64 x
                            in fastF input == C.rightmost_64_32 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (WordJet Rightmost64_32))

prop_left_pad_low_1_8 :: Bool -> Bool
prop_left_pad_low_1_8 = \x -> let input = toBit x
                                in fastF input == C.left_pad_low_1_8 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_8))

prop_left_pad_low_1_16 :: Bool -> Bool
prop_left_pad_low_1_16 = \x -> let input = toBit x
                                in fastF input == C.left_pad_low_1_16 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_16))

prop_left_pad_low_8_16 :: W.Word8 -> Bool
prop_left_pad_low_8_16 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_low_8_16 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_16))

prop_left_pad_low_1_32 :: Bool -> Bool
prop_left_pad_low_1_32 = \x -> let input = toBit x
                                in fastF input == C.left_pad_low_1_32 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_32))

prop_left_pad_low_8_32 :: W.Word8 -> Bool
prop_left_pad_low_8_32 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_low_8_32 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_32))

prop_left_pad_low_16_32 :: W.Word16 -> Bool
prop_left_pad_low_16_32 = \x -> let input = toW16 x
                                in fastF input == C.left_pad_low_16_32 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow16_32))

prop_left_pad_low_1_64 :: Bool -> Bool
prop_left_pad_low_1_64 = \x -> let input = toBit x
                                in fastF input == C.left_pad_low_1_64 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadLow1_64))

prop_left_pad_low_8_64 :: W.Word8 -> Bool
prop_left_pad_low_8_64 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_low_8_64 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow8_64))

prop_left_pad_low_16_64 :: W.Word16 -> Bool
prop_left_pad_low_16_64 = \x -> let input = toW16 x
                                in fastF input == C.left_pad_low_16_64 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow16_64))

prop_left_pad_low_32_64 :: W.Word32 -> Bool
prop_left_pad_low_32_64 = \x -> let input = toW32 x
                                in fastF input == C.left_pad_low_32_64 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadLow32_64))

prop_left_pad_high_1_8 :: Bool -> Bool
prop_left_pad_high_1_8 = \x -> let input = toBit x
                                in fastF input == C.left_pad_high_1_8 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_8))

prop_left_pad_high_1_16 :: Bool -> Bool
prop_left_pad_high_1_16 = \x -> let input = toBit x
                                in fastF input == C.left_pad_high_1_16 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_16))

prop_left_pad_high_8_16 :: W.Word8 -> Bool
prop_left_pad_high_8_16 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_high_8_16 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_16))

prop_left_pad_high_1_32 :: Bool -> Bool
prop_left_pad_high_1_32 = \x -> let input = toBit x
                                in fastF input == C.left_pad_high_1_32 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_32))

prop_left_pad_high_8_32 :: W.Word8 -> Bool
prop_left_pad_high_8_32 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_high_8_32 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_32))

prop_left_pad_high_16_32 :: W.Word16 -> Bool
prop_left_pad_high_16_32 = \x -> let input = toW16 x
                                in fastF input == C.left_pad_high_16_32 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh16_32))

prop_left_pad_high_1_64 :: Bool -> Bool
prop_left_pad_high_1_64 = \x -> let input = toBit x
                                in fastF input == C.left_pad_high_1_64 input
 where
  fastF = testCoreEval (specification (WordJet LeftPadHigh1_64))

prop_left_pad_high_8_64 :: W.Word8 -> Bool
prop_left_pad_high_8_64 = \x -> let input = toW8 x
                                in fastF input == C.left_pad_high_8_64 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh8_64))

prop_left_pad_high_16_64 :: W.Word16 -> Bool
prop_left_pad_high_16_64 = \x -> let input = toW16 x
                                in fastF input == C.left_pad_high_16_64 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh16_64))

prop_left_pad_high_32_64 :: W.Word32 -> Bool
prop_left_pad_high_32_64 = \x -> let input = toW32 x
                                in fastF input == C.left_pad_high_32_64 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet LeftPadHigh32_64))

prop_right_pad_low_1_8 :: Bool -> Bool
prop_right_pad_low_1_8 = \x -> let input = toBit x
                                in fastF input == C.right_pad_low_1_8 input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_8))

prop_right_pad_low_1_16 :: Bool -> Bool
prop_right_pad_low_1_16 = \x -> let input = toBit x
                                in fastF input == C.right_pad_low_1_16 input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_16))

prop_right_pad_low_8_16 :: W.Word8 -> Bool
prop_right_pad_low_8_16 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_low_8_16 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_16))

prop_right_pad_low_1_32 :: Bool -> Bool
prop_right_pad_low_1_32 = \x -> let input = toBit x
                                in fastF input == C.right_pad_low_1_32 input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_32))

prop_right_pad_low_8_32 :: W.Word8 -> Bool
prop_right_pad_low_8_32 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_low_8_32 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_32))

prop_right_pad_low_16_32 :: W.Word16 -> Bool
prop_right_pad_low_16_32 = \x -> let input = toW16 x
                                in fastF input == C.right_pad_low_16_32 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow16_32))

prop_right_pad_low_1_64 :: Bool -> Bool
prop_right_pad_low_1_64 = \x -> let input = toBit x
                                in fastF input == C.right_pad_low_1_64 input
 where
  fastF = testCoreEval (specification (WordJet RightPadLow1_64))

prop_right_pad_low_8_64 :: W.Word8 -> Bool
prop_right_pad_low_8_64 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_low_8_64 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow8_64))

prop_right_pad_low_16_64 :: W.Word16 -> Bool
prop_right_pad_low_16_64 = \x -> let input = toW16 x
                                in fastF input == C.right_pad_low_16_64 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow16_64))

prop_right_pad_low_32_64 :: W.Word32 -> Bool
prop_right_pad_low_32_64 = \x -> let input = toW32 x
                                in fastF input == C.right_pad_low_32_64 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadLow32_64))

prop_right_pad_high_1_8 :: Bool -> Bool
prop_right_pad_high_1_8 = \x -> let input = toBit x
                                in fastF input == C.right_pad_high_1_8 input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_8))

prop_right_pad_high_1_16 :: Bool -> Bool
prop_right_pad_high_1_16 = \x -> let input = toBit x
                                in fastF input == C.right_pad_high_1_16 input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_16))

prop_right_pad_high_8_16 :: W.Word8 -> Bool
prop_right_pad_high_8_16 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_high_8_16 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_16))

prop_right_pad_high_1_32 :: Bool -> Bool
prop_right_pad_high_1_32 = \x -> let input = toBit x
                                in fastF input == C.right_pad_high_1_32 input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_32))

prop_right_pad_high_8_32 :: W.Word8 -> Bool
prop_right_pad_high_8_32 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_high_8_32 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_32))

prop_right_pad_high_16_32 :: W.Word16 -> Bool
prop_right_pad_high_16_32 = \x -> let input = toW16 x
                                in fastF input == C.right_pad_high_16_32 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh16_32))

prop_right_pad_high_1_64 :: Bool -> Bool
prop_right_pad_high_1_64 = \x -> let input = toBit x
                                in fastF input == C.right_pad_high_1_64 input
 where
  fastF = testCoreEval (specification (WordJet RightPadHigh1_64))

prop_right_pad_high_8_64 :: W.Word8 -> Bool
prop_right_pad_high_8_64 = \x -> let input = toW8 x
                                in fastF input == C.right_pad_high_8_64 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh8_64))

prop_right_pad_high_16_64 :: W.Word16 -> Bool
prop_right_pad_high_16_64 = \x -> let input = toW16 x
                                in fastF input == C.right_pad_high_16_64 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh16_64))

prop_right_pad_high_32_64 :: W.Word32 -> Bool
prop_right_pad_high_32_64 = \x -> let input = toW32 x
                                in fastF input == C.right_pad_high_32_64 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (WordJet RightPadHigh32_64))

assert_one_8 :: Assertion
assert_one_8 = fastF () @=? C.one_8 ()
 where
  fastF = testCoreEval (specification (ArithJet One8))

assert_one_16 :: Assertion
assert_one_16 = fastF () @=? C.one_16 ()
 where
  fastF = testCoreEval (specification (ArithJet One16))

assert_one_32 :: Assertion
assert_one_32 = fastF () @=? C.one_32 ()
 where
  fastF = testCoreEval (specification (ArithJet One32))

assert_one_64 :: Assertion
assert_one_64 = fastF () @=? C.one_64 ()
 where
  fastF = testCoreEval (specification (ArithJet One64))

prop_add_8 :: W.Word8 -> W.Word8 -> Bool
prop_add_8 = \x y -> let input = (toW8 x, toW8 y)
                      in fastF input == C.add_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add8))

prop_add_16 :: W.Word16 -> W.Word16 -> Bool
prop_add_16 = \x y -> let input = (toW16 x, toW16 y)
                       in fastF input == C.add_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add16))

prop_add_32 :: W.Word32 -> W.Word32 -> Bool
prop_add_32 = \x y -> let input = (toW32 x, toW32 y)
                       in fastF input == C.add_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add32))

prop_add_64 :: W.Word64 -> W.Word64 -> Bool
prop_add_64 = \x y -> let input = (toW64 x, toW64 y)
                       in fastF input == C.add_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Add64))

prop_full_add_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_full_add_8 = \c x y -> let input = (toBit c, (toW8 x, toW8 y))
                             in fastF input == C.full_add_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd8))

prop_full_add_16 :: Bool -> W.Word16 -> W.Word16 -> Bool
prop_full_add_16 = \c x y -> let input = (toBit c, (toW16 x, toW16 y))
                              in fastF input == C.full_add_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd16))

prop_full_add_32 :: Bool -> W.Word32 -> W.Word32 -> Bool
prop_full_add_32 = \c x y -> let input = (toBit c, (toW32 x, toW32 y))
                              in fastF input == C.full_add_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd32))

prop_full_add_64 :: Bool -> W.Word64 -> W.Word64 -> Bool
prop_full_add_64 = \c x y -> let input = (toBit c, (toW64 x, toW64 y))
                              in fastF input == C.full_add_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullAdd64))

prop_full_increment_8 :: Bool -> W.Word8 -> Bool
prop_full_increment_8 = \b x -> let input = (toBit b, toW8 x)
                                in fastF input == C.full_increment_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement8))

prop_full_increment_16 :: Bool -> W.Word16 -> Bool
prop_full_increment_16 = \b x -> let input = (toBit b, toW16 x)
                                 in fastF input == C.full_increment_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement16))

prop_full_increment_32 :: Bool -> W.Word32 -> Bool
prop_full_increment_32 = \b x -> let input = (toBit b, toW32 x)
                                 in fastF input == C.full_increment_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement32))

prop_full_increment_64 :: Bool -> W.Word64 -> Bool
prop_full_increment_64 = \b x -> let input = (toBit b, toW64 x)
                                 in fastF input == C.full_increment_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullIncrement64))

assert_full_increment_max_8 :: Assertion
assert_full_increment_max_8 = fastF input @=? C.full_increment_8 input
 where
  input = (toBit True, toWord8 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement8))

assert_full_increment_max_16 :: Assertion
assert_full_increment_max_16 = fastF input @=? C.full_increment_16 input
 where
  input = (toBit True, toWord16 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement16))

assert_full_increment_max_32 :: Assertion
assert_full_increment_max_32 = fastF input @=? C.full_increment_32 input
 where
  input = (toBit True, toWord32 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement32))

assert_full_increment_max_64 :: Assertion
assert_full_increment_max_64 = fastF input @=? C.full_increment_64 input
 where
  input = (toBit True, toWord64 (-1))
  fastF = testCoreEval (specification (ArithJet FullIncrement64))

prop_increment_8 :: W.Word8 -> Bool
prop_increment_8 = \x -> let input = toW8 x
                       in fastF input == C.increment_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment8))

prop_increment_16 :: W.Word16 -> Bool
prop_increment_16 = \x -> let input = toW16 x
                        in fastF input == C.increment_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment16))

prop_increment_32 :: W.Word32 -> Bool
prop_increment_32 = \x -> let input = toW32 x
                        in fastF input == C.increment_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment32))

prop_increment_64 :: W.Word64 -> Bool
prop_increment_64 = \x -> let input = toW64 x
                        in fastF input == C.increment_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Increment64))

assert_increment_max_8 :: Assertion
assert_increment_max_8 = fastF input @=? C.increment_8 input
 where
  input = toWord8 (-1)
  fastF = testCoreEval (specification (ArithJet Increment8))

assert_increment_max_16 :: Assertion
assert_increment_max_16 = fastF input @=? C.increment_16 input
 where
  input = toWord16 (-1)
  fastF = testCoreEval (specification (ArithJet Increment16))

assert_increment_max_32 :: Assertion
assert_increment_max_32 = fastF input @=? C.increment_32 input
 where
  input = toWord32 (-1)
  fastF = testCoreEval (specification (ArithJet Increment32))

assert_increment_max_64 :: Assertion
assert_increment_max_64 = fastF input @=? C.increment_64 input
 where
  input = toWord64 (-1)
  fastF = testCoreEval (specification (ArithJet Increment64))

prop_subtract_8 :: W.Word8 -> W.Word8 -> Bool
prop_subtract_8 = \x y -> let input = (toW8 x, toW8 y)
                           in fastF input == C.subtract_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract8))

prop_subtract_16 :: W.Word16 -> W.Word16 -> Bool
prop_subtract_16 = \x y -> let input = (toW16 x, toW16 y)
                            in fastF input == C.subtract_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract16))

prop_subtract_32 :: W.Word32 -> W.Word32 -> Bool
prop_subtract_32 = \x y -> let input = (toW32 x, toW32 y)
                            in fastF input == C.subtract_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract32))

prop_subtract_64 :: W.Word64 -> W.Word64 -> Bool
prop_subtract_64 = \x y -> let input = (toW64 x, toW64 y)
                            in fastF input == C.subtract_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Subtract64))

prop_full_subtract_8 :: Bool -> W.Word8 -> W.Word8 -> Bool
prop_full_subtract_8 = \c x y -> let input = (toBit c, (toW8 x, toW8 y))
                                  in fastF input == C.full_subtract_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract8))

prop_full_subtract_16 :: Bool -> W.Word16 -> W.Word16 -> Bool
prop_full_subtract_16 = \c x y -> let input = (toBit c, (toW16 x, toW16 y))
                                   in fastF input == C.full_subtract_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract16))

prop_full_subtract_32 :: Bool -> W.Word32 -> W.Word32 -> Bool
prop_full_subtract_32 = \c x y -> let input = (toBit c, (toW32 x, toW32 y))
                                   in fastF input == C.full_subtract_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract32))

prop_full_subtract_64 :: Bool -> W.Word64 -> W.Word64 -> Bool
prop_full_subtract_64 = \c x y -> let input = (toBit c, (toW64 x, toW64 y))
                                   in fastF input == C.full_subtract_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullSubtract64))

prop_full_decrement_8 :: Bool -> W.Word8 -> Bool
prop_full_decrement_8 = \b x -> let input = (toBit b, toW8 x)
                                in fastF input == C.full_decrement_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement8))

prop_full_decrement_16 :: Bool -> W.Word16 -> Bool
prop_full_decrement_16 = \b x -> let input = (toBit b, toW16 x)
                                 in fastF input == C.full_decrement_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement16))

prop_full_decrement_32 :: Bool -> W.Word32 -> Bool
prop_full_decrement_32 = \b x -> let input = (toBit b, toW32 x)
                                 in fastF input == C.full_decrement_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement32))

prop_full_decrement_64 :: Bool -> W.Word64 -> Bool
prop_full_decrement_64 = \b x -> let input = (toBit b, toW64 x)
                                 in fastF input == C.full_decrement_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullDecrement64))

assert_full_decrement_zero_8 :: Assertion
assert_full_decrement_zero_8 = fastF input @=? C.full_decrement_8 input
 where
  input = (toBit True, toWord8 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement8))

assert_full_decrement_zero_16 :: Assertion
assert_full_decrement_zero_16 = fastF input @=? C.full_decrement_16 input
 where
  input = (toBit True, toWord16 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement16))

assert_full_decrement_zero_32 :: Assertion
assert_full_decrement_zero_32 = fastF input @=? C.full_decrement_32 input
 where
  input = (toBit True, toWord32 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement32))

assert_full_decrement_zero_64 :: Assertion
assert_full_decrement_zero_64 = fastF input @=? C.full_decrement_64 input
 where
  input = (toBit True, toWord64 0)
  fastF = testCoreEval (specification (ArithJet FullDecrement64))

prop_decrement_8 :: W.Word8 -> Bool
prop_decrement_8 = \x -> let input = toW8 x
                       in fastF input == C.decrement_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement8))

prop_decrement_16 :: W.Word16 -> Bool
prop_decrement_16 = \x -> let input = toW16 x
                        in fastF input == C.decrement_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement16))

prop_decrement_32 :: W.Word32 -> Bool
prop_decrement_32 = \x -> let input = toW32 x
                        in fastF input == C.decrement_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement32))

prop_decrement_64 :: W.Word64 -> Bool
prop_decrement_64 = \x -> let input = toW64 x
                        in fastF input == C.decrement_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Decrement64))

assert_decrement_zero_8 :: Assertion
assert_decrement_zero_8 = fastF input @=? C.decrement_8 input
 where
  input = toWord8 0
  fastF = testCoreEval (specification (ArithJet Decrement8))

assert_decrement_zero_16 :: Assertion
assert_decrement_zero_16 = fastF input @=? C.decrement_16 input
 where
  input = toWord16 0
  fastF = testCoreEval (specification (ArithJet Decrement16))

assert_decrement_zero_32 :: Assertion
assert_decrement_zero_32 = fastF input @=? C.decrement_32 input
 where
  input = toWord32 0
  fastF = testCoreEval (specification (ArithJet Decrement32))

assert_decrement_zero_64 :: Assertion
assert_decrement_zero_64 = fastF input @=? C.decrement_64 input
 where
  input = toWord64 0
  fastF = testCoreEval (specification (ArithJet Decrement64))

prop_negate_8 :: W.Word8 -> Bool
prop_negate_8 = \x -> let input = toW8 x
                       in fastF input == C.negate_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate8))

prop_negate_16 :: W.Word16 -> Bool
prop_negate_16 = \x -> let input = toW16 x
                        in fastF input == C.negate_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate16))

prop_negate_32 :: W.Word32 -> Bool
prop_negate_32 = \x -> let input = toW32 x
                        in fastF input == C.negate_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate32))

prop_negate_64 :: W.Word64 -> Bool
prop_negate_64 = \x -> let input = toW64 x
                        in fastF input == C.negate_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Negate64))

prop_multiply_8 :: W.Word8 -> W.Word8 -> Bool
prop_multiply_8 = \x y -> let input = (toW8 x, toW8 y)
                           in fastF input == C.multiply_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply8))

prop_multiply_16 :: W.Word16 -> W.Word16 -> Bool
prop_multiply_16 = \x y -> let input = (toW16 x, toW16 y)
                            in fastF input == C.multiply_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply16))

prop_multiply_32 :: W.Word32 -> W.Word32 -> Bool
prop_multiply_32 = \x y -> let input = (toW32 x, toW32 y)
                            in fastF input == C.multiply_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply32))

prop_multiply_64 :: W.Word64 -> W.Word64 -> Bool
prop_multiply_64 = \x y -> let input = (toW64 x, toW64 y)
                            in fastF input == C.multiply_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Multiply64))

prop_full_multiply_8 :: W.Word8 -> W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_full_multiply_8 = \x y z w -> let input = ((toW8 x, toW8 y), (toW8 z, toW8 w))
                                    in fastF input == C.full_multiply_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply8))

prop_full_multiply_16 :: W.Word16 -> W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_full_multiply_16 = \x y z w -> let input = ((toW16 x, toW16 y), (toW16 z, toW16 w))
                                     in fastF input == C.full_multiply_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply16))

prop_full_multiply_32 :: W.Word32 -> W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_full_multiply_32 = \x y z w -> let input = ((toW32 x, toW32 y), (toW32 z, toW32 w))
                                     in fastF input == C.full_multiply_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply32))

prop_full_multiply_64 :: W.Word64 -> W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_full_multiply_64 = \x y z w -> let input = ((toW64 x, toW64 y), (toW64 z, toW64 w))
                                     in fastF input == C.full_multiply_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet FullMultiply64))

prop_is_zero_8 :: W.Word8 -> Bool
prop_is_zero_8 = \x -> let input = toW8 x
                       in fastF input == C.is_zero_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero8))

prop_is_zero_16 :: W.Word16 -> Bool
prop_is_zero_16 = \x -> let input = toW16 x
                        in fastF input == C.is_zero_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero16))

prop_is_zero_32 :: W.Word32 -> Bool
prop_is_zero_32 = \x -> let input = toW32 x
                        in fastF input == C.is_zero_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero32))

prop_is_zero_64 :: W.Word64 -> Bool
prop_is_zero_64 = \x -> let input = toW64 x
                        in fastF input == C.is_zero_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsZero64))

assert_zero_is_zero_8 :: Assertion
assert_zero_is_zero_8 = fastF input @=? C.is_zero_8 input
 where
  input = toWord8 0
  fastF = testCoreEval (specification (ArithJet IsZero8))

assert_zero_is_zero_16 :: Assertion
assert_zero_is_zero_16 = fastF input @=? C.is_zero_16 input
 where
  input = toWord16 0
  fastF = testCoreEval (specification (ArithJet IsZero16))

assert_zero_is_zero_32 :: Assertion
assert_zero_is_zero_32 = fastF input @=? C.is_zero_32 input
 where
  input = toWord32 0
  fastF = testCoreEval (specification (ArithJet IsZero32))

assert_zero_is_zero_64 :: Assertion
assert_zero_is_zero_64 = fastF input @=? C.is_zero_64 input
 where
  input = toWord64 0
  fastF = testCoreEval (specification (ArithJet IsZero64))

prop_is_one_8 :: W.Word8 -> Bool
prop_is_one_8 = \x -> let input = toW8 x
                       in fastF input == C.is_one_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne8))

prop_is_one_16 :: W.Word16 -> Bool
prop_is_one_16 = \x -> let input = toW16 x
                        in fastF input == C.is_one_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne16))

prop_is_one_32 :: W.Word32 -> Bool
prop_is_one_32 = \x -> let input = toW32 x
                        in fastF input == C.is_one_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne32))

prop_is_one_64 :: W.Word64 -> Bool
prop_is_one_64 = \x -> let input = toW64 x
                        in fastF input == C.is_one_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet IsOne64))

assert_one_is_one_8 :: Assertion
assert_one_is_one_8 = fastF input @=? C.is_one_8 input
 where
  input = toWord8 1
  fastF = testCoreEval (specification (ArithJet IsOne8))

assert_one_is_one_16 :: Assertion
assert_one_is_one_16 = fastF input @=? C.is_one_16 input
 where
  input = toWord16 1
  fastF = testCoreEval (specification (ArithJet IsOne16))

assert_one_is_one_32 :: Assertion
assert_one_is_one_32 = fastF input @=? C.is_one_32 input
 where
  input = toWord32 1
  fastF = testCoreEval (specification (ArithJet IsOne32))

assert_one_is_one_64 :: Assertion
assert_one_is_one_64 = fastF input @=? C.is_one_64 input
 where
  input = toWord64 1
  fastF = testCoreEval (specification (ArithJet IsOne64))

prop_le_8 :: W.Word8 -> W.Word8 -> Bool
prop_le_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.le_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le8))

prop_le_16 :: W.Word16 -> W.Word16 -> Bool
prop_le_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.le_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le16))

prop_le_32 :: W.Word32 -> W.Word32 -> Bool
prop_le_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.le_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le32))

prop_le_64 :: W.Word64 -> W.Word64 -> Bool
prop_le_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.le_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le64))

prop_le_diag_8 :: W.Word8 -> Bool
prop_le_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == C.le_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le8))

prop_le_diag_16 :: W.Word16 -> Bool
prop_le_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == C.le_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le16))

prop_le_diag_32 :: W.Word32 -> Bool
prop_le_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == C.le_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le32))

prop_le_diag_64 :: W.Word64 -> Bool
prop_le_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == C.le_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Le64))

prop_lt_8 :: W.Word8 -> W.Word8 -> Bool
prop_lt_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.lt_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt8))

prop_lt_16 :: W.Word16 -> W.Word16 -> Bool
prop_lt_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.lt_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt16))

prop_lt_32 :: W.Word32 -> W.Word32 -> Bool
prop_lt_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.lt_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt32))

prop_lt_64 :: W.Word64 -> W.Word64 -> Bool
prop_lt_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.lt_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt64))

prop_lt_diag_8 :: W.Word8 -> Bool
prop_lt_diag_8 = \x -> let input = (toW8 x, toW8 x)
                         in fastF input == C.lt_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt8))

prop_lt_diag_16 :: W.Word16 -> Bool
prop_lt_diag_16 = \x -> let input = (toW16 x, toW16 x)
                         in fastF input == C.lt_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt16))

prop_lt_diag_32 :: W.Word32 -> Bool
prop_lt_diag_32 = \x -> let input = (toW32 x, toW32 x)
                         in fastF input == C.lt_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt32))

prop_lt_diag_64 :: W.Word64 -> Bool
prop_lt_diag_64 = \x -> let input = (toW64 x, toW64 x)
                         in fastF input == C.lt_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Lt64))

prop_min_8 :: W.Word8 -> W.Word8 -> Bool
prop_min_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.min_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min8))

prop_min_16 :: W.Word16 -> W.Word16 -> Bool
prop_min_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.min_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min16))

prop_min_32 :: W.Word32 -> W.Word32 -> Bool
prop_min_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.min_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min32))

prop_min_64 :: W.Word64 -> W.Word64 -> Bool
prop_min_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.min_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Min64))

prop_max_8 :: W.Word8 -> W.Word8 -> Bool
prop_max_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.max_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max8))

prop_max_16 :: W.Word16 -> W.Word16 -> Bool
prop_max_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.max_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max16))

prop_max_32 :: W.Word32 -> W.Word32 -> Bool
prop_max_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.max_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max32))

prop_max_64 :: W.Word64 -> W.Word64 -> Bool
prop_max_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.max_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Max64))

prop_median_8 :: W.Word8 -> W.Word8 -> W.Word8 -> Bool
prop_median_8 = \x y z -> let input = (toW8 x, (toW8 y, toW8 z))
                     in fastF input == C.median_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median8))

prop_median_16 :: W.Word16 -> W.Word16 -> W.Word16 -> Bool
prop_median_16 = \x y z -> let input = (toW16 x, (toW16 y, toW16 z))
                      in fastF input == C.median_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median16))

prop_median_32 :: W.Word32 -> W.Word32 -> W.Word32 -> Bool
prop_median_32 = \x y z -> let input = (toW32 x, (toW32 y, toW32 z))
                      in fastF input == C.median_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median32))

prop_median_64 :: W.Word64 -> W.Word64 -> W.Word64 -> Bool
prop_median_64 = \x y z -> let input = (toW64 x, (toW64 y, toW64 z))
                      in fastF input == C.median_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Median64))

prop_div_mod_8 :: W.Word8 -> W.Word8 -> Bool
prop_div_mod_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.div_mod_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod8))

prop_div_mod_16 :: W.Word16 -> W.Word16 -> Bool
prop_div_mod_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.div_mod_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod16))

prop_div_mod_32 :: W.Word32 -> W.Word32 -> Bool
prop_div_mod_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.div_mod_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod32))

prop_div_mod_64 :: W.Word64 -> W.Word64 -> Bool
prop_div_mod_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.div_mod_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod64))

prop_divide_8 :: W.Word8 -> W.Word8 -> Bool
prop_divide_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.divide_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide8))

prop_divide_16 :: W.Word16 -> W.Word16 -> Bool
prop_divide_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.divide_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide16))

prop_divide_32 :: W.Word32 -> W.Word32 -> Bool
prop_divide_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.divide_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide32))

prop_divide_64 :: W.Word64 -> W.Word64 -> Bool
prop_divide_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.divide_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide64))

prop_modulo_8 :: W.Word8 -> W.Word8 -> Bool
prop_modulo_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.modulo_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo8))

prop_modulo_16 :: W.Word16 -> W.Word16 -> Bool
prop_modulo_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.modulo_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo16))

prop_modulo_32 :: W.Word32 -> W.Word32 -> Bool
prop_modulo_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.modulo_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo32))

prop_modulo_64 :: W.Word64 -> W.Word64 -> Bool
prop_modulo_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.modulo_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo64))

prop_divides_8 :: W.Word8 -> W.Word8 -> Bool
prop_divides_8 = \x y -> let input = (toW8 x, toW8 y)
                     in fastF input == C.divides_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides8))

prop_divides_16 :: W.Word16 -> W.Word16 -> Bool
prop_divides_16 = \x y -> let input = (toW16 x, toW16 y)
                      in fastF input == C.divides_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides16))

prop_divides_32 :: W.Word32 -> W.Word32 -> Bool
prop_divides_32 = \x y -> let input = (toW32 x, toW32 y)
                      in fastF input == C.divides_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides32))

prop_divides_64 :: W.Word64 -> W.Word64 -> Bool
prop_divides_64 = \x y -> let input = (toW64 x, toW64 y)
                      in fastF input == C.divides_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides64))

prop_div_mod_zero_8 :: W.Word8 -> Bool
prop_div_mod_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == C.div_mod_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod8))

prop_div_mod_zero_16 :: W.Word16 -> Bool
prop_div_mod_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == C.div_mod_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod16))

prop_div_mod_zero_32 :: W.Word32 -> Bool
prop_div_mod_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == C.div_mod_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod32))

prop_div_mod_zero_64 :: W.Word64 -> Bool
prop_div_mod_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == C.div_mod_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet DivMod64))

prop_divide_zero_8 :: W.Word8 -> Bool
prop_divide_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == C.divide_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide8))

prop_divide_zero_16 :: W.Word16 -> Bool
prop_divide_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == C.divide_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide16))

prop_divide_zero_32 :: W.Word32 -> Bool
prop_divide_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == C.divide_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide32))

prop_divide_zero_64 :: W.Word64 -> Bool
prop_divide_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == C.divide_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divide64))

prop_modulo_zero_8 :: W.Word8 -> Bool
prop_modulo_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == C.modulo_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo8))

prop_modulo_zero_16 :: W.Word16 -> Bool
prop_modulo_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == C.modulo_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo16))

prop_modulo_zero_32 :: W.Word32 -> Bool
prop_modulo_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == C.modulo_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo32))

prop_modulo_zero_64 :: W.Word64 -> Bool
prop_modulo_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == C.modulo_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Modulo64))

prop_divides_zero_8 :: W.Word8 -> Bool
prop_divides_zero_8 = \x -> let input = (toW8 x, toW8 0)
                     in fastF input == C.divides_8 input
 where
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides8))

prop_divides_zero_16 :: W.Word16 -> Bool
prop_divides_zero_16 = \x -> let input = (toW16 x, toW16 0)
                      in fastF input == C.divides_16 input
 where
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides16))

prop_divides_zero_32 :: W.Word32 -> Bool
prop_divides_zero_32 = \x -> let input = (toW32 x, toW32 0)
                      in fastF input == C.divides_32 input
 where
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides32))

prop_divides_zero_64 :: W.Word64 -> Bool
prop_divides_zero_64 = \x -> let input = (toW64 x, toW64 0)
                      in fastF input == C.divides_64 input
 where
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (ArithJet Divides64))

assert_sha_256_iv :: Assertion
assert_sha_256_iv = fastF () @=? C.sha_256_iv ()
 where
  fastF = testCoreEval (specification (HashJet Sha256Iv))

prop_sha_256_block :: HashElement -> HashElement -> HashElement -> Bool
prop_sha_256_block = \h b1 b2 -> fastF (heAsTy h, (heAsTy b1, heAsTy b2)) == C.sha_256_block (heAsTy h, (heAsTy b1, heAsTy b2))
 where
  fastF = testCoreEval (specification (HashJet Sha256Block))

assert_sha_256_ctx_8_init :: Assertion
assert_sha_256_ctx_8_init = fastF () @=? C.sha_256_ctx_8_init ()
 where
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Init))

prop_sha_256_ctx_8_add_1 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_1 = \ctx ->
                           forAll arbitraryW8 $ \w8 ->
                           let input = (ctxAsTy ctx, toW8 w8)
                           in fastF input == C.sha_256_ctx_8_add_1 input
 where
  arbitraryW8 :: Gen W.Word8
  arbitraryW8 = arbitraryBoundedIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add1))

prop_sha_256_ctx_8_add_2 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_2 = \ctx ->
                           forAll arbitraryW16 $ \w16 ->
                           let input = (ctxAsTy ctx, toW16 w16)
                           in fastF input == C.sha_256_ctx_8_add_2 input
 where
  arbitraryW16 :: Gen W.Word16
  arbitraryW16 = arbitraryBoundedIntegral
  toW16 = toWord16 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add2))

prop_sha_256_ctx_8_add_4 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_4 = \ctx ->
                           forAll arbitraryW32 $ \w32 ->
                           let input = (ctxAsTy ctx, toW32 w32)
                           in fastF input == C.sha_256_ctx_8_add_4 input
 where
  arbitraryW32 :: Gen W.Word32
  arbitraryW32 = arbitraryBoundedIntegral
  toW32 = toWord32 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add4))

prop_sha_256_ctx_8_add_8 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_8 = \ctx ->
                           forAll arbitraryW64 $ \w64 ->
                           let input = (ctxAsTy ctx, toW64 w64)
                           in fastF input == C.sha_256_ctx_8_add_8 input
 where
  arbitraryW64 :: Gen W.Word64
  arbitraryW64 = arbitraryBoundedIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add8))

prop_sha_256_ctx_8_add_16 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_16 = \ctx ->
                           forAll arbitraryW64 $ \w64a ->
                           forAll arbitraryW64 $ \w64b ->
                           let input = (ctxAsTy ctx, (toW64 w64a, toW64 w64b))
                           in fastF input == C.sha_256_ctx_8_add_16 input
 where
  arbitraryW64 :: Gen W.Word64
  arbitraryW64 = arbitraryBoundedIntegral
  toW64 = toWord64 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add16))

prop_sha_256_ctx_8_add_32 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_32 = \ctx ->
                           forAll arbitraryW256 $ \w256 ->
                           let input = (ctxAsTy ctx, toW256 w256)
                           in fastF input == C.sha_256_ctx_8_add_32 input
 where
  arbitraryW256 :: Gen W.Word256
  arbitraryW256 = arbitraryBoundedIntegral
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add32))

prop_sha_256_ctx_8_add_64 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_64 = \ctx ->
                           forAll arbitraryW256 $ \w256a ->
                           forAll arbitraryW256 $ \w256b ->
                           let input = (ctxAsTy ctx, (toW256 w256a, toW256 w256b))
                           in fastF input == C.sha_256_ctx_8_add_64 input
 where
  arbitraryW256 :: Gen W.Word256
  arbitraryW256 = arbitraryBoundedIntegral
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add64))

prop_sha_256_ctx_8_add_128 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_128 = \ctx ->
                           forAll arbitraryW256 $ \w256a ->
                           forAll arbitraryW256 $ \w256b ->
                           forAll arbitraryW256 $ \w256c ->
                           forAll arbitraryW256 $ \w256d ->
                           let input = (ctxAsTy ctx, ((toW256 w256a, toW256 w256b), (toW256 w256c, toW256 w256d)))
                           in fastF input == C.sha_256_ctx_8_add_128 input
 where
  arbitraryW256 :: Gen W.Word256
  arbitraryW256 = arbitraryBoundedIntegral
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add128))

prop_sha_256_ctx_8_add_256 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_256 = \ctx ->
                           forAll arbitraryW256 $ \w256a ->
                           forAll arbitraryW256 $ \w256b ->
                           forAll arbitraryW256 $ \w256c ->
                           forAll arbitraryW256 $ \w256d ->
                           forAll arbitraryW256 $ \w256e ->
                           forAll arbitraryW256 $ \w256f ->
                           forAll arbitraryW256 $ \w256g ->
                           forAll arbitraryW256 $ \w256h ->
                           let input = (ctxAsTy ctx, (((toW256 w256a, toW256 w256b), (toW256 w256c, toW256 w256d)),
                                                      ((toW256 w256e, toW256 w256f), (toW256 w256g, toW256 w256h))))
                           in fastF input == C.sha_256_ctx_8_add_256 input
 where
  arbitraryW256 :: Gen W.Word256
  arbitraryW256 = arbitraryBoundedIntegral
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add256))

prop_sha_256_ctx_8_add_512 :: Sha256CtxElement -> Property
prop_sha_256_ctx_8_add_512 = \ctx ->
                           forAll arbitraryW256 $ \w256a ->
                           forAll arbitraryW256 $ \w256b ->
                           forAll arbitraryW256 $ \w256c ->
                           forAll arbitraryW256 $ \w256d ->
                           forAll arbitraryW256 $ \w256e ->
                           forAll arbitraryW256 $ \w256f ->
                           forAll arbitraryW256 $ \w256g ->
                           forAll arbitraryW256 $ \w256h ->
                           forAll arbitraryW256 $ \w256i ->
                           forAll arbitraryW256 $ \w256j ->
                           forAll arbitraryW256 $ \w256k ->
                           forAll arbitraryW256 $ \w256l ->
                           forAll arbitraryW256 $ \w256m ->
                           forAll arbitraryW256 $ \w256n ->
                           forAll arbitraryW256 $ \w256o ->
                           forAll arbitraryW256 $ \w256p ->
                           let input = (ctxAsTy ctx, ((((toW256 w256a, toW256 w256b), (toW256 w256c, toW256 w256d)),
                                                       ((toW256 w256e, toW256 w256f), (toW256 w256g, toW256 w256h))),
                                                      (((toW256 w256i, toW256 w256j), (toW256 w256k, toW256 w256l)),
                                                       ((toW256 w256m, toW256 w256n), (toW256 w256o, toW256 w256p)))))
                           in fastF input == C.sha_256_ctx_8_add_512 input
 where
  arbitraryW256 :: Gen W.Word256
  arbitraryW256 = arbitraryBoundedIntegral
  toW256 = toWord256 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Add512))

prop_sha_256_ctx_8_add_buffer_511 :: Sha256CtxElement -> Int -> Property
prop_sha_256_ctx_8_add_buffer_511 = \ctx preLen ->
                           forAll (vectorOf (preLen `mod` 512) arbitraryW8) $ \w8s ->
                           let input = (ctxAsTy ctx, fst $ bufferFill buffer511 (toW8 <$> w8s))
                           in fastF input == C.sha_256_ctx_8_add_buffer_511 input
 where
  arbitraryW8 :: Gen W.Word8
  arbitraryW8 = arbitraryBoundedIntegral
  toW8 = toWord8 . fromIntegral
  fastF = testCoreEval (specification (HashJet Sha256Ctx8AddBuffer511))

prop_sha_256_ctx_8_finalize :: Sha256CtxElement -> Bool
prop_sha_256_ctx_8_finalize = \ctx -> fastF (ctxAsTy ctx) == C.sha_256_ctx_8_finalize (ctxAsTy ctx)
 where
  fastF = testCoreEval (specification (HashJet Sha256Ctx8Finalize))

prop_parse_lock = forAll arbitraryLock $ \a -> fastF (toWord32 (fromIntegral a)) == C.parse_lock (toWord32 (fromIntegral a))
 where
  fastF = testCoreEval (specification (BitcoinJet ParseLock))

prop_parse_sequence = forAll arbitraryLock $ \a -> fastF (toWord32 (fromIntegral a)) == C.parse_sequence (toWord32 (fromIntegral a))
 where
  fastF = testCoreEval (specification (BitcoinJet ParseSequence))

fe_unary_prop f g = \a -> fastF (feAsTy a) == g (feAsTy a)
 where
  fastF = testCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == g (feAsTy a, feAsTy b)
 where
  fastF = testCoreEval f

prop_fe_normalize :: FieldElement -> Bool
prop_fe_normalize = fe_unary_prop Prog.fe_normalize C.fe_normalize

prop_fe_negate :: FieldElement -> Bool
prop_fe_negate = fe_unary_prop Prog.fe_negate C.fe_negate

prop_fe_add :: FieldElement -> FieldElement -> Bool
prop_fe_add = fe_binary_prop Prog.fe_add C.fe_add

prop_fe_square :: FieldElement -> Bool
prop_fe_square = fe_unary_prop Prog.fe_square C.fe_square

prop_fe_multiply :: FieldElement -> FieldElement -> Bool
prop_fe_multiply = fe_binary_prop Prog.fe_multiply C.fe_multiply

prop_fe_multiply_beta :: FieldElement -> Bool
prop_fe_multiply_beta = fe_unary_prop Prog.fe_multiply_beta C.fe_multiply_beta

prop_fe_invert :: FieldElement -> Bool
prop_fe_invert = fe_unary_prop Prog.fe_invert C.fe_invert

prop_fe_square_root :: FieldElement -> Bool
prop_fe_square_root = fe_unary_prop Prog.fe_square_root C.fe_square_root

prop_fe_is_zero :: FieldElement -> Bool
prop_fe_is_zero = fe_unary_prop Prog.fe_is_zero C.fe_is_zero

prop_fe_is_odd :: FieldElement -> Bool
prop_fe_is_odd = fe_unary_prop Prog.fe_is_odd C.fe_is_odd

scalar_unary_prop f g = \a -> fastF (scalarAsTy a) == g (scalarAsTy a)
 where
  fastF = testCoreEval f

scalar_binary_prop f g = \a b -> fastF (scalarAsTy a, scalarAsTy b) == g (scalarAsTy a, scalarAsTy b)
 where
  fastF = testCoreEval f

prop_scalar_normalize :: ScalarElement -> Bool
prop_scalar_normalize = scalar_unary_prop Prog.scalar_normalize C.scalar_normalize

prop_scalar_negate :: ScalarElement -> Bool
prop_scalar_negate = scalar_unary_prop Prog.scalar_negate C.scalar_negate

prop_scalar_add :: ScalarElement -> ScalarElement -> Bool
prop_scalar_add = scalar_binary_prop Prog.scalar_add C.scalar_add

prop_scalar_square :: ScalarElement -> Bool
prop_scalar_square = scalar_unary_prop Prog.scalar_square C.scalar_square

prop_scalar_multiply :: ScalarElement -> ScalarElement -> Bool
prop_scalar_multiply = scalar_binary_prop Prog.scalar_multiply C.scalar_multiply

prop_scalar_multiply_lambda :: ScalarElement -> Bool
prop_scalar_multiply_lambda = scalar_unary_prop Prog.scalar_multiply_lambda C.scalar_multiply_lambda

prop_scalar_invert :: ScalarElement -> Bool
prop_scalar_invert = scalar_unary_prop Prog.scalar_invert C.scalar_invert

prop_scalar_is_zero :: ScalarElement -> Bool
prop_scalar_is_zero = scalar_unary_prop Prog.scalar_is_zero C.scalar_is_zero

assert_gej_infinity :: Assertion
assert_gej_infinity =  fast_gej_infinity () @=? C.gej_infinity ()
 where
  fast_gej_infinity = testCoreEval Prog.gej_infinity

prop_gej_rescale :: GroupElementJacobian -> FieldElement -> Bool
prop_gej_rescale = \a c -> fast_gej_rescale (gejAsTy a, feAsTy c) == C.gej_rescale (gejAsTy a, feAsTy c)
 where
  fast_gej_rescale = testCoreEval Prog.gej_rescale

prop_gej_rescale_inf :: FieldElement -> Property
prop_gej_rescale_inf c = forAll gen_inf $ flip prop_gej_rescale c

prop_gej_normalize :: GroupElementJacobian -> Bool
prop_gej_normalize = \a -> fast_gej_normalize (gejAsTy a) == C.gej_normalize (gejAsTy a)
 where
  fast_gej_normalize = testCoreEval Prog.gej_normalize

prop_gej_normalize_inf :: Property
prop_gej_normalize_inf = forAll gen_inf $ prop_gej_normalize

prop_gej_negate :: GroupElementJacobian -> Bool
prop_gej_negate = \a -> fast_gej_negate (gejAsTy a) == C.gej_negate (gejAsTy a)
 where
  fast_gej_negate = testCoreEval Prog.gej_negate

prop_gej_negate_inf :: Property
prop_gej_negate_inf = forAll gen_inf $ prop_gej_negate

prop_ge_negate :: GroupElement -> Bool
prop_ge_negate = \a -> fast_ge_negate (geAsTy a) == C.ge_negate (geAsTy a)
 where
  fast_ge_negate = testCoreEval Prog.ge_negate

prop_gej_double :: GroupElementJacobian -> Bool
prop_gej_double = \a -> fast_gej_double (gejAsTy a) == C.gej_double (gejAsTy a)
 where
  fast_gej_double = testCoreEval Prog.gej_double

prop_gej_double_inf :: Property
prop_gej_double_inf = forAll gen_inf $ prop_gej_double

prop_gej_double_zero :: FieldElement -> FieldElement -> Bool
prop_gej_double_zero x z = prop_gej_double a
 where
  x' = feAsSpec x
  z' = feAsSpec z
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x')
                           (FieldElement . Spec.fe_pack $ Spec.fe_zero)
                           (FieldElement . Spec.fe_pack $ z')

prop_gej_add :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add = \a b -> fast_gej_add (gejAsTy a, gejAsTy b) == C.gej_add (gejAsTy a, gejAsTy b)
 where
  fast_gej_add = testCoreEval Prog.gej_add

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
prop_gej_ge_add_ex = \a b -> fast_gej_ge_add_ex (gejAsTy a, geAsTy b) == C.gej_ge_add_ex (gejAsTy a, geAsTy b)
 where
  fast_gej_ge_add_ex = testCoreEval Prog.gej_ge_add_ex

prop_gej_ge_add_ex_double z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           z
prop_gej_ge_add_ex_opp z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           z
prop_gej_ge_add_ex_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b

prop_gej_ge_add :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_add = \a b -> fast_gej_ge_add (gejAsTy a, geAsTy b) == C.gej_ge_add (gejAsTy a, geAsTy b)
 where
  fast_gej_ge_add = testCoreEval Prog.gej_ge_add

prop_gej_is_infinity :: GroupElementJacobian -> Bool
prop_gej_is_infinity = \a -> fast_gej_is_infinity (gejAsTy a) == C.gej_is_infinity (gejAsTy a)
 where
  fast_gej_is_infinity = testCoreEval Prog.gej_is_infinity

prop_gej_x_equiv :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_x_equiv = \a b -> fast_gej_x_equiv (feAsTy a, gejAsTy b) == C.gej_x_equiv (feAsTy a, gejAsTy b)
 where
  fast_gej_x_equiv = testCoreEval Prog.gej_x_equiv

prop_gej_x_equiv_inf x0 = forAll gen_inf $ prop_gej_x_equiv x0
prop_gej_x_equiv_true y z x0 = prop_gej_x_equiv x0 a
  where
   z' = feAsSpec z
   x0' = feAsSpec x0
   a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x0' .*. z' .^. 2) y z

prop_gej_x_equiv_inf_zero = prop_gej_x_equiv_inf (FieldElement 0)

prop_gej_y_is_odd :: GroupElementJacobian -> Bool
prop_gej_y_is_odd = \a -> fast_gej_y_is_odd (gejAsTy a) == C.gej_y_is_odd (gejAsTy a)
 where
  fast_gej_y_is_odd = testCoreEval Prog.gej_y_is_odd

prop_gej_is_on_curve :: GroupElementJacobian -> Bool
prop_gej_is_on_curve = \a -> fast_gej_is_on_curve (gejAsTy a) == C.gej_is_on_curve (gejAsTy a)
 where
  fast_gej_is_on_curve = testCoreEval Prog.gej_is_on_curve

prop_ge_is_on_curve :: GroupElement -> Bool

prop_gej_is_on_curve_inf = forAll gen_inf prop_gej_is_on_curve
prop_gej_is_on_curve_inf_half = forAll gen_half_curve_inf prop_gej_is_on_curve
prop_gej_is_on_curve_half = forAll gen_half_curve_jacobian prop_gej_is_on_curve

prop_ge_is_on_curve = \a -> fast_ge_is_on_curve (geAsTy a) == C.ge_is_on_curve (geAsTy a)
 where
  fast_ge_is_on_curve = testCoreEval Prog.ge_is_on_curve

prop_ge_is_on_curve_half = forAll gen_half_curve prop_ge_is_on_curve

prop_generate = \ng -> fast_generate (scalarAsTy ng)
                    == C.generate (scalarAsTy ng)
 where
  fast_generate = testCoreEval Prog.generate

prop_scale = \na a -> fast_scale (scalarAsTy na, gejAsTy a)
                   == C.scale (scalarAsTy na, gejAsTy a)
 where
  fast_scale = testCoreEval Prog.scale
prop_scale_0 a = prop_scale na a
 where
  na = ScalarElement 0
prop_scale_inf na = forAll gen_inf $ \a -> prop_scale na a

prop_linear_combination_1 = \na a ng -> fast_linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
                                     == C.linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
 where
  fast_linear_combination_1 = testCoreEval Prog.linear_combination_1
prop_linear_combination_1_0 a ng = prop_linear_combination_1 na a ng
 where
  na = ScalarElement 0

prop_linear_combination_1_inf na ng = forAll gen_inf $ \a -> prop_linear_combination_1 na a ng

-- :TODO: expand test coverage on low-order (off-curve) points.
-- This particular test case will fail if the gej_double_var function in the C implementation isn't "fixed" to handle
-- setting the infinity flag for off-curve points of order 2.
assert_linear_combination_1_order_6 :: Assertion
assert_linear_combination_1_order_6 = True @=? prop_linear_combination_1 na a ng
 where
  na = ScalarElement 6
  a = GroupElementJacobian (FieldElement 106586213356003376052770626926523423124273824193112332847656463919061591657353)
                           (FieldElement 26101920679609057376888884124959740524626979187904654689991505285331895977061)
                           (FieldElement 1)
  ng = ScalarElement 1

prop_linear_verify_1 = \na a ng r -> fast_linear_verify_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
                                 == C.linear_verify_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
 where
  fast_linear_verify_1 = testCoreEval Prog.linear_verify_1

prop_linear_verify_1_0 a ng = prop_linear_verify_1 na a ng
 where
  na = ScalarElement 0

prop_linear_verify_1_true_half na ng = forAll gen_half_curve $ \a -> prop_linear_verify_1_true na a ng
 where
  prop_linear_verify_1_true na a ng | Just (GE rx' ry') <- r' = property $ prop_linear_verify_1 na a ng (mkGE rx' ry')
                                    | otherwise = property Discard
   where
    na' = scalarAsSpec na
    a' = geAsSpec a
    ng' = scalarAsSpec ng
    toGEJ (GE x y) = (GEJ x y Spec.fe_one)
    r' = Spec.gej_normalize $ Spec.linear_combination [(na', toGEJ a')] ng'
    mkGE rx' ry' = GroupElement (FieldElement (Spec.fe_pack rx')) (FieldElement (Spec.fe_pack ry'))

prop_point_verify_1 = \na a ng r -> fast_point_verify_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
                                 == C.point_verify_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
 where
  fast_point_verify_1 = testCoreEval Prog.point_verify_1

prop_point_verify_1_true na p ng | Just a' <- Spec.decompress p' = property $ prop a'
                                 | otherwise = property Discard
 where
  na' = scalarAsSpec na
  ng' = scalarAsSpec ng
  p' = pointAsSpec p
  prop a' = prop_point_verify_1 na p ng r
   where
    toGEJ (GE x y) = (GEJ x y Spec.fe_one)
    Just (GE rx' ry') = Spec.gej_normalize $ Spec.linear_combination [(na', toGEJ a')] ng'
    r = PointElement (Spec.fe_is_odd ry') (FieldElement (Spec.fe_pack rx'))

prop_decompress = \a -> fast_decompress (pointAsTy a)
                     == C.decompress (pointAsTy a)
 where
  fast_decompress = testCoreEval Prog.decompress

prop_bip_0340_verify = \pk m sig -> fast_bip_0340_verify ((pk, m), sig)
                                 == C.bip_0340_verify ((pk, m), sig)
 where
  fast_bip_0340_verify = testCoreEval Prog.bip_0340_verify

assert_bip_0340_verify_vector tv = True @=? prop_bip_0340_verify pk m sig
 where
  ((pk, m), sig) = (bip0340TestAsTy tv)

case_bip_0340_verify_vector n tv = testCase name (assert_bip_0340_verify_vector tv)
 where
  name = "bip_0340_vector_" ++ show n

prop_check_sig_verify :: FieldElement -> HashElement -> HashElement -> FieldElement -> ScalarElement -> Bool
prop_check_sig_verify = \pk m1 m2 r s ->
   let input = ((feAsTy pk, (heAsTy m1, heAsTy m2)), (feAsTy r, scalarAsTy s))
   in fast_check_sig_verify input == C.check_sig_verify input
 where
  fast_check_sig_verify = testCoreEval (specification (SignatureJet CheckSigVerify))

prop_check_sig_verify_true :: HashElement -> HashElement -> Property
prop_check_sig_verify_true = \m1 m2 ->
   let msg = sigHash (heAsSpec m1) (heAsSpec m2)
   in forAll (genSignature msg) $ \(PubKey pk, Sig r s) ->
     let input = ((toW256 pk, (heAsTy m1, heAsTy m2)), (toW256 r, toW256 s))
     in Just () == C.check_sig_verify input
     && Just () == fast_check_sig_verify input
 where
  toW256 = toWord256 . fromIntegral
  fast_check_sig_verify = testCoreEval (specification (SignatureJet CheckSigVerify))

