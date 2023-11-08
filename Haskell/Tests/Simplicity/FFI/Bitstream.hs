{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Bitstream
  ( Bitstream
  , initializeBitstream
  ) where

import qualified Data.ByteString as BS
import Data.Serialize (decode)
import Data.Serialize.Put (runPut)
import Foreign.C.Types (CSize(..), CChar(..))
import Foreign.Ptr (Ptr)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Storable (Storable(..))

import Simplicity.Serialization

-- Abstract representative for our C structures.
newtype Bitstream = Bitstream Bitstream

foreign import ccall unsafe "&" c_sizeof_bitstream :: Ptr CSize

foreign import ccall unsafe "" c_initializeBitstream :: Ptr Bitstream -> Ptr CChar -> CSize -> IO ()

sizeof_bitstream :: Int
sizeof_bitstream = fromIntegral . unsafeLocalState $ peek c_sizeof_bitstream

initializeBitstream :: [Bool] -> (Ptr Bitstream -> IO a) -> IO a
initializeBitstream stream k =
  allocaBytes sizeof_bitstream $ \pstream ->
  BS.useAsCString bs $ \pbs -> do
   c_initializeBitstream pstream pbs (fromIntegral len)
   k pstream
 where
  bs = runPut $ putBitStream stream
  len = length stream
