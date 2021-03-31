-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Jets
 ( add_32, full_add_32
 , subtract_32, full_subtract_32
 , multiply_32, full_multiply_32
 , sha_256_block
 ) where

import Foreign.Ptr (Ptr)

import Simplicity.FFI.Frame
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import qualified Simplicity.Programs.LibSecp256k1.Lib as LibSecp256k1
import Simplicity.Ty.Word

foreign import ccall unsafe "" c_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_sha_256_block :: Ptr FrameItem -> Ptr FrameItem -> IO Bool

add_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
add_32 = unsafeLocalCoreJet c_add_32

full_add_32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
full_add_32 = unsafeLocalCoreJet c_full_add_32

subtract_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
subtract_32 = unsafeLocalCoreJet c_subtract_32

full_subtract_32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
full_subtract_32 = unsafeLocalCoreJet c_full_subtract_32

multiply_32 :: (Word32, Word32) -> Maybe Word64
multiply_32 = unsafeLocalCoreJet c_multiply_32

full_multiply_32 :: ((Word32, Word32), (Word32, Word32)) -> Maybe Word64
full_multiply_32 = unsafeLocalCoreJet c_full_multiply_32

sha_256_block :: (Sha256.Hash, Sha256.Block) -> Maybe Sha256.Hash
sha_256_block = unsafeLocalCoreJet c_sha_256_block
