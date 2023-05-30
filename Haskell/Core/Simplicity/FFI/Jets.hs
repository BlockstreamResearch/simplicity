-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Jets
 ( verify
 , low_8, low_16, low_32, low_64
 , one_8, one_16, one_32, one_64
 , eq_8, eq_16, eq_32, eq_64, eq_256
 , add_8, add_16, add_32, add_64
 , full_add_8, full_add_16, full_add_32, full_add_64
 , full_increment_8, full_increment_16, full_increment_32, full_increment_64
 , increment_8, increment_16, increment_32, increment_64
 , subtract_8, subtract_16, subtract_32, subtract_64
 , full_subtract_8, full_subtract_16, full_subtract_32, full_subtract_64
 , negate_8, negate_16, negate_32, negate_64
 , full_decrement_8, full_decrement_16, full_decrement_32, full_decrement_64
 , decrement_8, decrement_16, decrement_32, decrement_64
 , multiply_8, multiply_16, multiply_32, multiply_64
 , full_multiply_8, full_multiply_16, full_multiply_32, full_multiply_64
 , is_zero_8, is_zero_16, is_zero_32, is_zero_64
 , is_one_8, is_one_16, is_one_32, is_one_64
 , le_8, le_16, le_32, le_64
 , lt_8, lt_16, lt_32, lt_64
 , min_8, min_16, min_32, min_64
 , max_8, max_16, max_32, max_64
 , median_8, median_16, median_32, median_64
 , sha_256_iv, sha_256_block
 , sha_256_ctx_8_init
 , sha_256_ctx_8_add_1
 , sha_256_ctx_8_add_2
 , sha_256_ctx_8_add_4
 , sha_256_ctx_8_add_8
 , sha_256_ctx_8_add_16
 , sha_256_ctx_8_add_32
 , sha_256_ctx_8_add_64
 , sha_256_ctx_8_add_128
 , sha_256_ctx_8_add_256
 , sha_256_ctx_8_add_512
 , sha_256_ctx_8_add_buffer_511
 , sha_256_ctx_8_finalize
 , fe_normalize, fe_negate, fe_add, fe_square, fe_multiply, fe_multiply_beta, fe_invert, fe_square_root, fe_is_zero, fe_is_odd
 , scalar_normalize, scalar_negate, scalar_add, scalar_square, scalar_multiply, scalar_multiply_lambda, scalar_invert, scalar_is_zero
 , gej_infinity, gej_rescale, gej_normalize, gej_negate, ge_negate, gej_double, gej_add, gej_ge_add_ex, gej_ge_add, gej_is_infinity, gej_x_equiv, gej_y_is_odd, gej_is_on_curve, ge_is_on_curve
 , scale, generate, linear_combination_1, linear_verify_1
 , decompress, point_verify_1
 , check_sig_verify
 , bip_0340_verify
 , parse_lock, parse_sequence
 ) where

import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..))

import Simplicity.FFI.Frame
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Programs.LibSecp256k1.Lib (FE, Scalar, GE, GEJ, Point, PubKey, Sig)
import qualified Simplicity.Programs.LibSecp256k1.Lib as LibSecp256k1
import Simplicity.Ty.Word

foreign import ccall unsafe "" c_verify :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_low_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_low_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_low_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_low_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_one_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_one_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_one_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_one_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_eq_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_eq_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_eq_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_eq_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_eq_256 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_add_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_add_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_add_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_add_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_add_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_add_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_increment_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_increment_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_increment_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_increment_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_increment_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_increment_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_increment_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_increment_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_subtract_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_subtract_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_subtract_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_subtract_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_subtract_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_subtract_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_negate_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_negate_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_negate_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_negate_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_decrement_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_decrement_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_decrement_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_decrement_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_decrement_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_decrement_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_decrement_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_decrement_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_multiply_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_multiply_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_multiply_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_multiply_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_multiply_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_full_multiply_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_zero_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_zero_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_zero_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_zero_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_one_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_one_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_one_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_is_one_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_le_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_le_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_le_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_le_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_lt_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_lt_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_lt_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_lt_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_min_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_min_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_min_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_min_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_max_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_max_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_max_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_max_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_median_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_median_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_median_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_median_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool

foreign import ccall unsafe "" c_sha_256_iv :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_block :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_init :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_2 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_4 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_8 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_16 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_64 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_128 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_256 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_512 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_add_buffer_511 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_sha_256_ctx_8_finalize :: Ptr FrameItem -> Ptr FrameItem -> IO CBool

foreign import ccall unsafe "" c_fe_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_negate :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_add :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_square :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_multiply :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_multiply_beta :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_invert :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_square_root :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_is_zero :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_fe_is_odd :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_negate :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_add :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_square :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_multiply :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_multiply_lambda :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_invert :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scalar_is_zero :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_infinity :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_rescale :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_negate :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_ge_negate :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_double :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_add :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_ge_add_ex :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_ge_add :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_is_infinity :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_x_equiv :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_y_is_odd :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_gej_is_on_curve :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_ge_is_on_curve :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_scale :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_generate :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_linear_combination_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_linear_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_decompress :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_point_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_check_sig_verify :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bip_0340_verify :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_parse_lock :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_parse_sequence :: Ptr FrameItem -> Ptr FrameItem -> IO CBool

verify :: Bit -> Maybe ()
verify = unsafeLocalCoreJet c_verify

low_8 :: () -> Maybe Word8
low_8 = unsafeLocalCoreJet c_low_8

low_16 :: () -> Maybe Word16
low_16 = unsafeLocalCoreJet c_low_16

low_32 :: () -> Maybe Word32
low_32 = unsafeLocalCoreJet c_low_32

low_64 :: () -> Maybe Word64
low_64 = unsafeLocalCoreJet c_low_64

one_8 :: () -> Maybe Word8
one_8 = unsafeLocalCoreJet c_one_8

one_16 :: () -> Maybe Word16
one_16 = unsafeLocalCoreJet c_one_16

one_32 :: () -> Maybe Word32
one_32 = unsafeLocalCoreJet c_one_32

one_64 :: () -> Maybe Word64
one_64 = unsafeLocalCoreJet c_one_64

eq_8 :: (Word8, Word8) -> Maybe Bit
eq_8 = unsafeLocalCoreJet c_eq_8

eq_16 :: (Word16, Word16) -> Maybe Bit
eq_16 = unsafeLocalCoreJet c_eq_16

eq_32 :: (Word32, Word32) -> Maybe Bit
eq_32 = unsafeLocalCoreJet c_eq_32

eq_64 :: (Word64, Word64) -> Maybe Bit
eq_64 = unsafeLocalCoreJet c_eq_64

eq_256 :: (Word256, Word256) -> Maybe Bit
eq_256 = unsafeLocalCoreJet c_eq_256

add_8 :: (Word8, Word8) -> Maybe (Bit, Word8)
add_8 = unsafeLocalCoreJet c_add_8

add_16 :: (Word16, Word16) -> Maybe (Bit, Word16)
add_16 = unsafeLocalCoreJet c_add_16

add_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
add_32 = unsafeLocalCoreJet c_add_32

add_64 :: (Word64, Word64) -> Maybe (Bit, Word64)
add_64 = unsafeLocalCoreJet c_add_64

full_add_8 :: (Bit, (Word8, Word8)) -> Maybe (Bit, Word8)
full_add_8 = unsafeLocalCoreJet c_full_add_8

full_add_16 :: (Bit, (Word16, Word16)) -> Maybe (Bit, Word16)
full_add_16 = unsafeLocalCoreJet c_full_add_16

full_add_32 :: (Bit, (Word32, Word32)) -> Maybe (Bit, Word32)
full_add_32 = unsafeLocalCoreJet c_full_add_32

full_add_64 :: (Bit, (Word64, Word64)) -> Maybe (Bit, Word64)
full_add_64 = unsafeLocalCoreJet c_full_add_64

full_increment_8 :: (Bit, Word8) -> Maybe (Bit, Word8)
full_increment_8 = unsafeLocalCoreJet c_full_increment_8

full_increment_16 :: (Bit, Word16) -> Maybe (Bit, Word16)
full_increment_16 = unsafeLocalCoreJet c_full_increment_16

full_increment_32 :: (Bit, Word32) -> Maybe (Bit, Word32)
full_increment_32 = unsafeLocalCoreJet c_full_increment_32

full_increment_64 :: (Bit, Word64) -> Maybe (Bit, Word64)
full_increment_64 = unsafeLocalCoreJet c_full_increment_64

increment_8 :: Word8 -> Maybe (Bit, Word8)
increment_8 = unsafeLocalCoreJet c_increment_8

increment_16 :: Word16 -> Maybe (Bit, Word16)
increment_16 = unsafeLocalCoreJet c_increment_16

increment_32 :: Word32 -> Maybe (Bit, Word32)
increment_32 = unsafeLocalCoreJet c_increment_32

increment_64 :: Word64 -> Maybe (Bit, Word64)
increment_64 = unsafeLocalCoreJet c_increment_64

subtract_8 :: (Word8, Word8) -> Maybe (Bit, Word8)
subtract_8 = unsafeLocalCoreJet c_subtract_8

subtract_16 :: (Word16, Word16) -> Maybe (Bit, Word16)
subtract_16 = unsafeLocalCoreJet c_subtract_16

subtract_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
subtract_32 = unsafeLocalCoreJet c_subtract_32

subtract_64 :: (Word64, Word64) -> Maybe (Bit, Word64)
subtract_64 = unsafeLocalCoreJet c_subtract_64

full_subtract_8 :: (Bit, (Word8, Word8)) -> Maybe (Bit, Word8)
full_subtract_8 = unsafeLocalCoreJet c_full_subtract_8

full_subtract_16 :: (Bit, (Word16, Word16)) -> Maybe (Bit, Word16)
full_subtract_16 = unsafeLocalCoreJet c_full_subtract_16

full_subtract_32 :: (Bit, (Word32, Word32)) -> Maybe (Bit, Word32)
full_subtract_32 = unsafeLocalCoreJet c_full_subtract_32

full_subtract_64 :: (Bit, (Word64, Word64)) -> Maybe (Bit, Word64)
full_subtract_64 = unsafeLocalCoreJet c_full_subtract_64

negate_8 :: Word8 -> Maybe (Bit, Word8)
negate_8 = unsafeLocalCoreJet c_negate_8

negate_16 :: Word16 -> Maybe (Bit, Word16)
negate_16 = unsafeLocalCoreJet c_negate_16

negate_32 :: Word32 -> Maybe (Bit, Word32)
negate_32 = unsafeLocalCoreJet c_negate_32

negate_64 :: Word64 -> Maybe (Bit, Word64)
negate_64 = unsafeLocalCoreJet c_negate_64

full_decrement_8 :: (Bit, Word8) -> Maybe (Bit, Word8)
full_decrement_8 = unsafeLocalCoreJet c_full_decrement_8

full_decrement_16 :: (Bit, Word16) -> Maybe (Bit, Word16)
full_decrement_16 = unsafeLocalCoreJet c_full_decrement_16

full_decrement_32 :: (Bit, Word32) -> Maybe (Bit, Word32)
full_decrement_32 = unsafeLocalCoreJet c_full_decrement_32

full_decrement_64 :: (Bit, Word64) -> Maybe (Bit, Word64)
full_decrement_64 = unsafeLocalCoreJet c_full_decrement_64

decrement_8 :: Word8 -> Maybe (Bit, Word8)
decrement_8 = unsafeLocalCoreJet c_decrement_8

decrement_16 :: Word16 -> Maybe (Bit, Word16)
decrement_16 = unsafeLocalCoreJet c_decrement_16

decrement_32 :: Word32 -> Maybe (Bit, Word32)
decrement_32 = unsafeLocalCoreJet c_decrement_32

decrement_64 :: Word64 -> Maybe (Bit, Word64)
decrement_64 = unsafeLocalCoreJet c_decrement_64

multiply_8 :: (Word8, Word8) -> Maybe Word16
multiply_8 = unsafeLocalCoreJet c_multiply_8

multiply_16 :: (Word16, Word16) -> Maybe Word32
multiply_16 = unsafeLocalCoreJet c_multiply_16

multiply_32 :: (Word32, Word32) -> Maybe Word64
multiply_32 = unsafeLocalCoreJet c_multiply_32

multiply_64 :: (Word64, Word64) -> Maybe Word128
multiply_64 = unsafeLocalCoreJet c_multiply_64

full_multiply_8 :: ((Word8, Word8), (Word8, Word8)) -> Maybe Word16
full_multiply_8 = unsafeLocalCoreJet c_full_multiply_8

full_multiply_16 :: ((Word16, Word16), (Word16, Word16)) -> Maybe Word32
full_multiply_16 = unsafeLocalCoreJet c_full_multiply_16

full_multiply_32 :: ((Word32, Word32), (Word32, Word32)) -> Maybe Word64
full_multiply_32 = unsafeLocalCoreJet c_full_multiply_32

full_multiply_64 :: ((Word64, Word64), (Word64, Word64)) -> Maybe Word128
full_multiply_64 = unsafeLocalCoreJet c_full_multiply_64

is_zero_8 :: Word8 -> Maybe Bit
is_zero_8 = unsafeLocalCoreJet c_is_zero_8

is_zero_16 :: Word16 -> Maybe Bit
is_zero_16 = unsafeLocalCoreJet c_is_zero_16

is_zero_32 :: Word32 -> Maybe Bit
is_zero_32 = unsafeLocalCoreJet c_is_zero_32

is_zero_64 :: Word64 -> Maybe Bit
is_zero_64 = unsafeLocalCoreJet c_is_zero_64

is_one_8 :: Word8 -> Maybe Bit
is_one_8 = unsafeLocalCoreJet c_is_one_8

is_one_16 :: Word16 -> Maybe Bit
is_one_16 = unsafeLocalCoreJet c_is_one_16

is_one_32 :: Word32 -> Maybe Bit
is_one_32 = unsafeLocalCoreJet c_is_one_32

is_one_64 :: Word64 -> Maybe Bit
is_one_64 = unsafeLocalCoreJet c_is_one_64

le_8 :: (Word8, Word8) -> Maybe Bit
le_8 = unsafeLocalCoreJet c_le_8

le_16 :: (Word16, Word16) -> Maybe Bit
le_16 = unsafeLocalCoreJet c_le_16

le_32 :: (Word32, Word32) -> Maybe Bit
le_32 = unsafeLocalCoreJet c_le_32

le_64 :: (Word64, Word64) -> Maybe Bit
le_64 = unsafeLocalCoreJet c_le_64

lt_8 :: (Word8, Word8) -> Maybe Bit
lt_8 = unsafeLocalCoreJet c_lt_8

lt_16 :: (Word16, Word16) -> Maybe Bit
lt_16 = unsafeLocalCoreJet c_lt_16

lt_32 :: (Word32, Word32) -> Maybe Bit
lt_32 = unsafeLocalCoreJet c_lt_32

lt_64 :: (Word64, Word64) -> Maybe Bit
lt_64 = unsafeLocalCoreJet c_lt_64

min_8 :: (Word8, Word8) -> Maybe Word8
min_8 = unsafeLocalCoreJet c_min_8

min_16 :: (Word16, Word16) -> Maybe Word16
min_16 = unsafeLocalCoreJet c_min_16

min_32 :: (Word32, Word32) -> Maybe Word32
min_32 = unsafeLocalCoreJet c_min_32

min_64 :: (Word64, Word64) -> Maybe Word64
min_64 = unsafeLocalCoreJet c_min_64

max_8 :: (Word8, Word8) -> Maybe Word8
max_8 = unsafeLocalCoreJet c_max_8

max_16 :: (Word16, Word16) -> Maybe Word16
max_16 = unsafeLocalCoreJet c_max_16

max_32 :: (Word32, Word32) -> Maybe Word32
max_32 = unsafeLocalCoreJet c_max_32

max_64 :: (Word64, Word64) -> Maybe Word64
max_64 = unsafeLocalCoreJet c_max_64

median_8 :: (Word8, (Word8, Word8)) -> Maybe Word8
median_8 = unsafeLocalCoreJet c_median_8

median_16 :: (Word16, (Word16, Word16)) -> Maybe Word16
median_16 = unsafeLocalCoreJet c_median_16

median_32 :: (Word32, (Word32, Word32)) -> Maybe Word32
median_32 = unsafeLocalCoreJet c_median_32

median_64 :: (Word64, (Word64, Word64)) -> Maybe Word64
median_64 = unsafeLocalCoreJet c_median_64

sha_256_iv :: () -> Maybe Sha256.Hash
sha_256_iv = unsafeLocalCoreJet c_sha_256_iv

sha_256_block :: (Sha256.Hash, Sha256.Block) -> Maybe Sha256.Hash
sha_256_block = unsafeLocalCoreJet c_sha_256_block

sha_256_ctx_8_init :: () -> Maybe Sha256.Ctx8
sha_256_ctx_8_init = unsafeLocalCoreJet c_sha_256_ctx_8_init

sha_256_ctx_8_add_1 :: (Sha256.Ctx8, Word8) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_1 = unsafeLocalCoreJet c_sha_256_ctx_8_add_1

sha_256_ctx_8_add_2 :: (Sha256.Ctx8, Word16) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_2 = unsafeLocalCoreJet c_sha_256_ctx_8_add_2

sha_256_ctx_8_add_4 :: (Sha256.Ctx8, Word32) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_4 = unsafeLocalCoreJet c_sha_256_ctx_8_add_4

sha_256_ctx_8_add_8 :: (Sha256.Ctx8, Word64) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_8 = unsafeLocalCoreJet c_sha_256_ctx_8_add_8

sha_256_ctx_8_add_16 :: (Sha256.Ctx8, Word128) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_16 = unsafeLocalCoreJet c_sha_256_ctx_8_add_16

sha_256_ctx_8_add_32 :: (Sha256.Ctx8, Word256) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_32 = unsafeLocalCoreJet c_sha_256_ctx_8_add_32

sha_256_ctx_8_add_64 :: (Sha256.Ctx8, Word512) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_64 = unsafeLocalCoreJet c_sha_256_ctx_8_add_64

sha_256_ctx_8_add_128 :: (Sha256.Ctx8, Word1024) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_128 = unsafeLocalCoreJet c_sha_256_ctx_8_add_128

sha_256_ctx_8_add_256 :: (Sha256.Ctx8, Word2048) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_256 = unsafeLocalCoreJet c_sha_256_ctx_8_add_256

sha_256_ctx_8_add_512 :: (Sha256.Ctx8, Word4096) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_512 = unsafeLocalCoreJet c_sha_256_ctx_8_add_512

sha_256_ctx_8_add_buffer_511 :: (Sha256.Ctx8, Buffer511 Word8) -> Maybe Sha256.Ctx8
sha_256_ctx_8_add_buffer_511 = unsafeLocalCoreJet c_sha_256_ctx_8_add_buffer_511

sha_256_ctx_8_finalize :: Sha256.Ctx8 -> Maybe Sha256.Hash
sha_256_ctx_8_finalize = unsafeLocalCoreJet c_sha_256_ctx_8_finalize

fe_normalize :: FE -> Maybe FE
fe_normalize = unsafeLocalCoreJet c_fe_normalize

fe_negate :: FE -> Maybe FE
fe_negate = unsafeLocalCoreJet c_fe_negate

fe_add :: (FE, FE) -> Maybe FE
fe_add = unsafeLocalCoreJet c_fe_add

fe_square :: FE -> Maybe FE
fe_square = unsafeLocalCoreJet c_fe_square

fe_multiply :: (FE, FE) -> Maybe FE
fe_multiply = unsafeLocalCoreJet c_fe_multiply

fe_multiply_beta :: FE -> Maybe FE
fe_multiply_beta = unsafeLocalCoreJet c_fe_multiply_beta

fe_invert :: FE -> Maybe FE
fe_invert = unsafeLocalCoreJet c_fe_invert

fe_square_root :: FE -> Maybe (Either () FE)
fe_square_root = unsafeLocalCoreJet c_fe_square_root

fe_is_zero :: FE -> Maybe Bit
fe_is_zero = unsafeLocalCoreJet c_fe_is_zero

fe_is_odd :: FE -> Maybe Bit
fe_is_odd = unsafeLocalCoreJet c_fe_is_odd

scalar_normalize :: Scalar -> Maybe Scalar
scalar_normalize = unsafeLocalCoreJet c_scalar_normalize

scalar_negate :: Scalar -> Maybe Scalar
scalar_negate = unsafeLocalCoreJet c_scalar_negate

scalar_add :: (Scalar, Scalar) -> Maybe Scalar
scalar_add = unsafeLocalCoreJet c_scalar_add

scalar_square :: Scalar -> Maybe Scalar
scalar_square = unsafeLocalCoreJet c_scalar_square

scalar_multiply :: (Scalar, Scalar) -> Maybe Scalar
scalar_multiply = unsafeLocalCoreJet c_scalar_multiply

scalar_multiply_lambda :: Scalar -> Maybe Scalar
scalar_multiply_lambda = unsafeLocalCoreJet c_scalar_multiply_lambda

scalar_invert :: Scalar -> Maybe Scalar
scalar_invert = unsafeLocalCoreJet c_scalar_invert

scalar_is_zero :: Scalar -> Maybe Bit
scalar_is_zero = unsafeLocalCoreJet c_scalar_is_zero

gej_infinity :: () -> Maybe GEJ
gej_infinity = unsafeLocalCoreJet c_gej_infinity

gej_rescale :: (GEJ, FE) -> Maybe GEJ
gej_rescale = unsafeLocalCoreJet c_gej_rescale

gej_normalize :: GEJ -> Maybe (Either () GE)
gej_normalize = unsafeLocalCoreJet c_gej_normalize

gej_negate :: GEJ -> Maybe GEJ
gej_negate = unsafeLocalCoreJet c_gej_negate

ge_negate :: GE -> Maybe GE
ge_negate = unsafeLocalCoreJet c_ge_negate

gej_double :: GEJ -> Maybe GEJ
gej_double = unsafeLocalCoreJet c_gej_double

gej_add :: (GEJ, GEJ) -> Maybe GEJ
gej_add = unsafeLocalCoreJet c_gej_add

gej_ge_add_ex :: (GEJ, GE) -> Maybe (FE, GEJ)
gej_ge_add_ex = unsafeLocalCoreJet c_gej_ge_add_ex

gej_ge_add :: (GEJ, GE) -> Maybe GEJ
gej_ge_add = unsafeLocalCoreJet c_gej_ge_add

gej_is_infinity :: GEJ -> Maybe Bit
gej_is_infinity = unsafeLocalCoreJet c_gej_is_infinity

gej_x_equiv :: (FE, GEJ) -> Maybe Bit
gej_x_equiv = unsafeLocalCoreJet c_gej_x_equiv

gej_y_is_odd :: GEJ -> Maybe Bit
gej_y_is_odd = unsafeLocalCoreJet c_gej_y_is_odd

gej_is_on_curve :: GEJ -> Maybe Bit
gej_is_on_curve = unsafeLocalCoreJet c_gej_is_on_curve

ge_is_on_curve :: GE -> Maybe Bit
ge_is_on_curve = unsafeLocalCoreJet c_ge_is_on_curve

scale :: (Scalar, GEJ) -> Maybe GEJ
scale = unsafeLocalCoreJet c_scale

generate :: Scalar -> Maybe GEJ
generate = unsafeLocalCoreJet c_generate

linear_combination_1 :: ((Scalar, GEJ), Scalar) -> Maybe GEJ
linear_combination_1 = unsafeLocalCoreJet c_linear_combination_1

linear_verify_1 :: (((Scalar, GE), Scalar), GE) -> Maybe ()
linear_verify_1 = unsafeLocalCoreJet c_linear_verify_1

decompress :: Point -> Maybe (Either () GE)
decompress = unsafeLocalCoreJet c_decompress

point_verify_1 :: (((Scalar, Point), Scalar), Point) -> Maybe ()
point_verify_1 = unsafeLocalCoreJet c_point_verify_1

check_sig_verify :: ((PubKey, Word512), Sig) -> Maybe ()
check_sig_verify = unsafeLocalCoreJet c_check_sig_verify

bip_0340_verify :: ((PubKey, Word256), Sig) -> Maybe ()
bip_0340_verify = unsafeLocalCoreJet c_bip_0340_verify

parse_lock :: Word32 -> Maybe (Either Word32 Word32)
parse_lock = unsafeLocalCoreJet c_parse_lock

parse_sequence :: Word32 -> Maybe (Either () (Either Word16 Word16))
parse_sequence = unsafeLocalCoreJet c_parse_sequence
