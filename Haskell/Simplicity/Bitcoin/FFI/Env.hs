-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.Bitcoin.FFI.Env
 ( CTransaction, CTapEnv, CTxEnv
 , marshallTransaction, marshallTapEnv
 , withEnv, withPrimEnv
 ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Foldable (toList)
import Data.Serialize (Serialize, encode, runPut)
import Data.Vector (Vector)
import Data.Word (Word32)
import Foreign.C.Types (CSize(..), CChar(..), CUChar(..), CUInt(..), CULong(..))
import Foreign.ForeignPtr (ForeignPtr, newForeignPtr, withForeignPtr)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Array (withArray, withArrayLen)
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Ptr (FunPtr, Ptr, nullPtr, plusPtr)
import Foreign.Storable (Storable(..))
import Lens.Family2 ((^.), under)

import Simplicity.Digest
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive

-- Abstract representative for the C txEnv types.
newtype RawBuffer = RawBuffer RawBuffer
newtype RawOutput = RawOutput RawOutput
newtype RawInput = RawInput RawInput
newtype RawTransaction = RawTransaction RawTransaction
newtype RawTapEnv = RawTapEnv RawTapEnv
newtype CTransaction = CTransaction CTransaction
newtype CTapEnv = CTapEnv CTapEnv
newtype CTxEnv = CTxEnv CTxEnv

foreign import ccall unsafe "&" c_sizeof_rawBitcoinBuffer :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawBitcoinOutput :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawBitcoinInput :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawBitcoinTransaction :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawBitcoinTapEnv :: Ptr CSize
foreign import ccall unsafe "&" c_bitcoin_sizeof_txEnv :: Ptr CSize

foreign import ccall unsafe "" c_set_rawBitcoinBuffer :: Ptr RawBuffer -> Ptr CChar -> CUInt -> IO ()
foreign import ccall unsafe "" c_set_rawBitcoinOutput :: Ptr RawOutput -> CULong -> Ptr RawBuffer -> IO ()
foreign import ccall unsafe "" c_set_rawBitcoinInput :: Ptr RawInput -> Ptr RawBuffer -> Ptr RawBuffer
                                                              -> Ptr CChar -> CUInt
                                                              -> CULong -> Ptr RawBuffer
                                                              -> CUInt -> IO ()
foreign import ccall unsafe "" c_set_rawBitcoinTransaction :: Ptr RawTransaction -> Ptr CChar -> CUInt
                                                                          -> Ptr RawInput -> CUInt
                                                                          -> Ptr RawOutput -> CUInt
                                                                          -> CUInt -> IO ()
foreign import ccall unsafe "" c_set_rawBitcoinTapEnv :: Ptr RawTapEnv -> Ptr CChar -> CUChar -> Ptr CChar -> IO ()
foreign import ccall unsafe "" c_bitcoin_set_txEnv :: Ptr CTxEnv -> Ptr CTransaction -> Ptr CTapEnv -> CUInt -> IO ()

foreign import ccall unsafe "" simplicity_bitcoin_mallocTransaction :: Ptr RawTransaction -> IO (Ptr CTransaction)
foreign import ccall unsafe "&" simplicity_bitcoin_freeTransaction :: FunPtr (Ptr CTransaction -> IO ())
foreign import ccall unsafe "" simplicity_bitcoin_mallocTapEnv :: Ptr RawTapEnv -> IO (Ptr CTapEnv)
foreign import ccall unsafe "&" simplicity_bitcoin_freeTapEnv :: FunPtr (Ptr CTapEnv -> IO ())

sizeof_rawBuffer :: Int
sizeof_rawBuffer = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBitcoinBuffer

sizeof_rawOutput :: Int
sizeof_rawOutput = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBitcoinOutput

sizeof_rawInput :: Int
sizeof_rawInput = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBitcoinInput

sizeof_rawTransaction :: Int
sizeof_rawTransaction = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBitcoinTransaction

sizeof_rawTapEnv :: Int
sizeof_rawTapEnv = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBitcoinTapEnv

sizeof_txEnv :: Int
sizeof_txEnv = fromIntegral . unsafeLocalState $ peek c_bitcoin_sizeof_txEnv

withRawBuffer :: BSL.ByteString -> (Ptr RawBuffer -> IO b) -> IO b
withRawBuffer str k =
  allocaBytes sizeof_rawBuffer $ \pRawBuffer ->
  BS.useAsCStringLen (BSL.toStrict str) $ \(pCharStr, len) -> do
    c_set_rawBitcoinBuffer pRawBuffer pCharStr (fromIntegral len)
    k pRawBuffer

withRawOutputs :: Vector TxOutput -> (Ptr RawOutput -> IO b) -> IO b
withRawOutputs txos k =
  allocaBytes (len * sizeof_rawOutput) $ \pRawOutput ->
   foldr ($) (k pRawOutput) [pokeRawOutput txo (pRawOutput `plusPtr` (i*sizeof_rawOutput)) | (i, txo) <- zip [0..] (toList txos)]
 where
  len = fromIntegral $ length txos
  pokeRawOutput :: TxOutput -> Ptr RawOutput -> IO b -> IO b
  pokeRawOutput txo pRawOutput k =
    withRawBuffer (txoScript txo) $ \pScript -> do
      c_set_rawBitcoinOutput pRawOutput (fromIntegral $ txoValue txo) pScript
      k

withRawInputs :: Vector SigTxInput -> (Ptr RawInput -> IO b) -> IO b
withRawInputs txis k =
  allocaBytes (len * sizeof_rawInput) $ \pRawInput -> do
   foldr ($) (k pRawInput) [pokeRawInput txo (pRawInput `plusPtr` (i*sizeof_rawInput)) | (i, txo) <- zip [0..] (toList txis)]
 where
  len = fromIntegral $ length txis
  withMaybeRawBuffer Nothing = ($ nullPtr)
  withMaybeRawBuffer (Just buf) = withRawBuffer buf
  pokeRawInput :: SigTxInput -> Ptr RawInput -> IO b -> IO b
  pokeRawInput txi pRawInput k =
    withMaybeRawBuffer (sigTxiAnnex txi) $ \pAnnex ->
    withRawBuffer (sigTxiScriptSig txi) $ \pScriptSig ->
    BS.useAsCString (encode . opHash $ sigTxiPreviousOutpoint txi) $ \pPrevTxid ->
    withRawBuffer (txoScript $ sigTxiTxo txi) $ \pScript -> do
      c_set_rawBitcoinInput pRawInput pAnnex pScriptSig
                               pPrevTxid (fromIntegral . opIndex . sigTxiPreviousOutpoint $ txi)
                               (fromIntegral . txoValue $ sigTxiTxo txi) pScript
                               (fromIntegral . sigTxiSequence $ txi)
      k

withRawTransaction :: SigTx -> (Ptr RawTransaction -> IO b) -> IO b
withRawTransaction tx k =
  allocaBytes sizeof_rawTransaction $ \pRawTransaction ->
  withRawInputs (sigTxIn tx) $ \pInput ->
  withRawOutputs (sigTxOut tx) $ \pOutput -> do
  BS.useAsCString (encode $ txid tx) $ \pTxid -> do
   c_set_rawBitcoinTransaction pRawTransaction pTxid version pInput numInputs pOutput numOutputs lockTime
   k pRawTransaction
 where
  version = fromIntegral (sigTxVersion tx)
  numInputs = fromIntegral $ length (sigTxIn tx)
  numOutputs = fromIntegral $ length (sigTxOut tx)
  lockTime = fromIntegral (sigTxLock tx)

withRawTapEnv :: TapEnv -> (Ptr RawTapEnv -> IO b) -> IO b
withRawTapEnv tapEnv k | length (tappath tapEnv) <= 128 =
  allocaBytes sizeof_rawTapEnv $ \pRawTapEnv ->
  BS.useAsCString encodePath $ \pControlBlock -> do
  BS.useAsCString (encode $ tapScriptCMR tapEnv) $ \pCmr -> do
   c_set_rawBitcoinTapEnv pRawTapEnv pControlBlock (fromIntegral . length $ tappath tapEnv) pCmr
   k pRawTapEnv
 where
  encodePath = BS.cons (tapleafVersion tapEnv) (BS.concat (encode (tapInternalKey tapEnv) : map encode (tappath tapEnv)))

marshallTransaction :: SigTx -> IO (ForeignPtr CTransaction)
marshallTransaction tx = withRawTransaction tx
                       $ \pRawTransaction -> simplicity_bitcoin_mallocTransaction pRawTransaction >>= newForeignPtr simplicity_bitcoin_freeTransaction

marshallTapEnv :: TapEnv -> IO (ForeignPtr CTapEnv)
marshallTapEnv env = withRawTapEnv env
                   $ \pRawTapEnv -> simplicity_bitcoin_mallocTapEnv pRawTapEnv >>= newForeignPtr simplicity_bitcoin_freeTapEnv

withEnv :: ForeignPtr CTransaction -> Word32 -> ForeignPtr CTapEnv -> (Ptr CTxEnv -> IO b) -> IO b
withEnv cTransaction ix cTapEnv k =
  allocaBytes sizeof_txEnv $ \pTxEnv ->
  withForeignPtr cTransaction $ \pTransaction ->
  withForeignPtr cTapEnv $ \pTapEnv -> do
   c_bitcoin_set_txEnv pTxEnv pTransaction pTapEnv (fromIntegral ix)
   k pTxEnv

withPrimEnv :: PrimEnv -> (Ptr CTxEnv -> IO b) -> IO b
withPrimEnv env k = do
  cTransaction <- marshallTransaction (envTx env)
  cTapEnv <- marshallTapEnv (envTap env)
  withEnv cTransaction (envIx env) cTapEnv k
