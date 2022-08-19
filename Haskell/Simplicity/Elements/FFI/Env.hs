-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.Elements.FFI.Env
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
import Foreign.C.Types (CSize(..), CChar(..), CUChar(..), CUInt(..))
import Foreign.ForeignPtr (ForeignPtr, newForeignPtr, withForeignPtr)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Array (withArray, withArrayLen)
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Ptr (FunPtr, Ptr, nullPtr, plusPtr)
import Foreign.Storable (Storable(..))
import Lens.Family2 ((^.), under)

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Primitive

-- Abstract representative for the C txEnv types.
newtype RawBuffer = RawBuffer RawBuffer
newtype RawOutput = RawOutput RawOutput
newtype RawInput = RawInput RawInput
newtype RawTransaction = RawTransaction RawTransaction
newtype RawTapEnv = RawTapEnv RawTapEnv
newtype CTransaction = CTransaction CTransaction
newtype CTapEnv = CTapEnv CTapEnv
newtype CTxEnv = CTxEnv CTxEnv

foreign import ccall unsafe "&" c_sizeof_rawBuffer :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawOutput :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawInput :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawTransaction :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_rawTapEnv :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_txEnv :: Ptr CSize

foreign import ccall unsafe "" c_set_rawBuffer :: Ptr RawBuffer -> Ptr CChar -> CUInt -> IO ()
foreign import ccall unsafe "" c_set_rawOutput :: Ptr RawOutput -> Ptr CChar -> Ptr CChar -> Ptr CChar -> Ptr RawBuffer -> Ptr RawBuffer -> Ptr RawBuffer -> IO ()
foreign import ccall unsafe "" c_set_rawInput :: Ptr RawInput -> Ptr RawBuffer -> Ptr CChar -> Ptr RawBuffer
                                                              -> Ptr CChar -> CUInt
                                                              -> Ptr CChar -> Ptr CChar -> Ptr RawBuffer
                                                              -> CUInt
                                                              -> Ptr CChar -> Ptr CChar -> Ptr CChar -> Ptr CChar
                                                              -> Ptr RawBuffer -> Ptr RawBuffer -> IO ()
foreign import ccall unsafe "" c_set_rawTransaction :: Ptr RawTransaction -> CUInt
                                                                          -> Ptr RawInput -> CUInt
                                                                          -> Ptr RawOutput -> CUInt
                                                                          -> CUInt -> IO ()
foreign import ccall unsafe "" c_set_rawTapEnv :: Ptr RawTapEnv -> Ptr RawBuffer -> Ptr CChar -> CUChar -> Ptr CChar -> IO ()
foreign import ccall unsafe "" c_set_txEnv :: Ptr CTxEnv -> Ptr CTransaction -> Ptr CTapEnv -> Ptr CChar -> CUInt -> IO ()

foreign import ccall unsafe "&" c_free_transaction :: FunPtr (Ptr CTransaction -> IO ())
foreign import ccall unsafe "&" c_free_tapEnv :: FunPtr (Ptr CTapEnv -> IO ())

foreign import ccall unsafe "" elements_simplicity_mallocTransaction :: Ptr RawTransaction -> IO (Ptr CTransaction)
foreign import ccall unsafe "" elements_simplicity_mallocTapEnv :: Ptr RawTapEnv -> IO (Ptr CTapEnv)

sizeof_rawBuffer :: Int
sizeof_rawBuffer = fromIntegral . unsafeLocalState $ peek c_sizeof_rawBuffer

sizeof_rawOutput :: Int
sizeof_rawOutput = fromIntegral . unsafeLocalState $ peek c_sizeof_rawOutput

sizeof_rawInput :: Int
sizeof_rawInput = fromIntegral . unsafeLocalState $ peek c_sizeof_rawInput

sizeof_rawTransaction :: Int
sizeof_rawTransaction = fromIntegral . unsafeLocalState $ peek c_sizeof_rawTransaction

sizeof_rawTapEnv :: Int
sizeof_rawTapEnv = fromIntegral . unsafeLocalState $ peek c_sizeof_rawTapEnv

sizeof_txEnv :: Int
sizeof_txEnv = fromIntegral . unsafeLocalState $ peek c_sizeof_txEnv

withRawBuffer :: BSL.ByteString -> (Ptr RawBuffer -> IO b) -> IO b
withRawBuffer str k =
  allocaBytes sizeof_rawBuffer $ \pRawBuffer ->
  BS.useAsCStringLen (BSL.toStrict str) $ \(pCharStr, len) -> do
    c_set_rawBuffer pRawBuffer pCharStr (fromIntegral len)
    k pRawBuffer

withIssuance :: Maybe Issuance -> (Ptr CChar -> Ptr CChar -> Ptr CChar -> Ptr CChar -> Ptr RawBuffer -> Ptr RawBuffer -> IO b) -> IO b
withIssuance Nothing k =
  withArray (replicate 32 0) $ \pZero ->
  withRawBuffer mempty $ \pEmpty ->
  k pZero pZero nullPtr nullPtr pEmpty pEmpty
withIssuance (Just (Left newIssue)) k =
  withArray (replicate 32 0) $ \pZero ->
  BS.useAsCString (encode (newIssuanceContractHash newIssue)) $ \pContract ->
  maybeAmount issueAmount $ \pAmount ->
  maybeAmount tokenAmount $ \pToken ->
  withRawBuffer (issueAmount ^. (under amount.prf_)) $ \pAmountRangeProof ->
  withRawBuffer (tokenAmount ^. (under amount.prf_)) $ \pTokenRangeProof ->
  k pZero pContract pAmount pToken pAmountRangeProof pTokenRangeProof
 where
  issueAmount = newIssuanceAmount newIssue
  tokenAmount = newIssuanceTokenAmount newIssue
  maybeAmount (Amount (Explicit 0)) k = k nullPtr
  maybeAmount amt k = BS.useAsCString (runPut . putAmount $ clearAmountPrf amt) k

withIssuance (Just (Right reIssue)) k =
  BS.useAsCString (encode (reissuanceBlindingNonce reIssue)) $ \pBlinding ->
  BS.useAsCString (encode (reissuanceEntropy reIssue)) $ \pEntropy ->
  BS.useAsCString (runPut . putAmount $ clearAmountPrf issueAmount) $ \pAmount ->
  withRawBuffer (issueAmount ^. (under amount.prf_)) $ \pAmountRangeProof ->
  withRawBuffer mempty $ \pEmpty ->
  k pBlinding pEntropy pAmount nullPtr pAmountRangeProof pEmpty
 where
  issueAmount = reissuanceAmount reIssue

withRawOutputs :: Vector TxOutput -> (Ptr RawOutput -> IO b) -> IO b
withRawOutputs txos k =
  allocaBytes (len * sizeof_rawOutput) $ \pRawOutput ->
   foldr ($) (k pRawOutput) [pokeRawOutput txo (pRawOutput `plusPtr` (i*sizeof_rawOutput)) | (i, txo) <- zip [0..] (toList txos)]
 where
  len = fromIntegral $ length txos
  pokeRawOutput :: TxOutput -> Ptr RawOutput -> IO b -> IO b
  pokeRawOutput txo pRawOutput k =
    BS.useAsCString (runPut . putAsset . clearAssetPrf $ txoAsset txo) $ \pAsset ->
    BS.useAsCString (runPut . putAmount . clearAmountPrf $ txoAmount txo) $ \pAmount ->
    withMaybe (txoNonce txo) $ \pNonce ->
    withRawBuffer (txoScript txo) $ \pScript ->
    withRawBuffer (txoAsset txo ^. (under asset.prf_)) $ \pSurjectionProof ->
    withRawBuffer (txoAmount txo ^. (under amount.prf_)) $ \pRangeProof -> do
      c_set_rawOutput pRawOutput pAsset pAmount pNonce pScript pSurjectionProof pRangeProof
      k
  withMaybe Nothing = ($ nullPtr)
  withMaybe (Just x) = BS.useAsCString (encode x)

withRawInputs :: Vector SigTxInput -> (Ptr RawInput -> IO b) -> IO b
withRawInputs txis k =
  allocaBytes (len * sizeof_rawInput) $ \pRawInput -> do
   foldr ($) (k pRawInput) [pokeRawInput txo (pRawInput `plusPtr` (i*sizeof_rawInput)) | (i, txo) <- zip [0..] (toList txis)]
 where
  len = fromIntegral $ length txis
  withMaybe Nothing = ($ nullPtr)
  withMaybe (Just x) = BS.useAsCString (encode x)
  withMaybeRawBuffer Nothing = ($ nullPtr)
  withMaybeRawBuffer (Just buf) = withRawBuffer buf
  pokeRawInput :: SigTxInput -> Ptr RawInput -> IO b -> IO b
  pokeRawInput txi pRawInput k =
    withMaybeRawBuffer (sigTxiAnnex txi) $ \pAnnex ->
    withMaybe (sigTxiPegin txi) $ \pPegin ->
    withRawBuffer (sigTxiScriptSig txi) $ \pScriptSig ->
    BS.useAsCString (encode . opHash $ sigTxiPreviousOutpoint txi) $ \pPrevTxid ->
    BS.useAsCString (runPut . putAsset . utxoAsset $ sigTxiTxo txi) $ \pAsset ->
    BS.useAsCString (runPut . putAmount . utxoAmount $ sigTxiTxo txi) $ \pValue ->
    withRawBuffer (utxoScript $ sigTxiTxo txi) $ \pScript ->
    withIssuance (sigTxiIssuance txi) $ \pBlindingNonce pAssetEntropy pAmount pInflationKeys pAmountRangeProof pInflationKeysRangeProof -> do
      c_set_rawInput pRawInput pAnnex pPegin pScriptSig
                               pPrevTxid (fromIntegral . opIndex . sigTxiPreviousOutpoint $ txi)
                               pAsset pValue pScript
                               (fromIntegral . sigTxiSequence $ txi)
                               pBlindingNonce pAssetEntropy pAmount pInflationKeys
                               pAmountRangeProof pInflationKeysRangeProof
      k

withRawTransaction :: SigTx -> (Ptr RawTransaction -> IO b) -> IO b
withRawTransaction tx k =
  allocaBytes sizeof_rawTransaction $ \pRawTransaction ->
  withRawInputs (sigTxIn tx) $ \pInput ->
  withRawOutputs (sigTxOut tx) $ \pOutput -> do
   c_set_rawTransaction pRawTransaction version pInput numInputs pOutput numOutputs lockTime
   k pRawTransaction
 where
  version = fromIntegral (sigTxVersion tx)
  numInputs = fromIntegral $ length (sigTxIn tx)
  numOutputs = fromIntegral $ length (sigTxOut tx)
  lockTime = fromIntegral (sigTxLock tx)

withRawTapEnv :: TapEnv -> (Ptr RawTapEnv -> IO b) -> IO b
withRawTapEnv tapEnv k | length (tapbranch tapEnv) <= 128 =
  allocaBytes sizeof_rawTapEnv $ \pRawTapEnv ->
  withMaybeAnnex (tapAnnex tapEnv) $ \pAnnex ->
  BS.useAsCString encodeBranch $ \pControlBlock -> do
  BS.useAsCString (encode $ tapScriptCMR tapEnv) $ \pCmr -> do
   c_set_rawTapEnv pRawTapEnv pAnnex pControlBlock (fromIntegral . length $ tapbranch tapEnv) pCmr
   k pRawTapEnv
 where
  withMaybeAnnex Nothing = ($ nullPtr)
  withMaybeAnnex (Just annex) = withRawBuffer annex
  encodeBranch = BS.cons (tapleafVersion tapEnv) (BS.concat (encode (tapInternalKey tapEnv) : map encode (tapbranch tapEnv)))

marshallTransaction :: SigTx -> IO (ForeignPtr CTransaction)
marshallTransaction tx = withRawTransaction tx
                       $ \pRawTransaction -> elements_simplicity_mallocTransaction pRawTransaction >>= newForeignPtr c_free_transaction

marshallTapEnv :: TapEnv -> IO (ForeignPtr CTapEnv)
marshallTapEnv env = withRawTapEnv env
                   $ \pRawTapEnv -> elements_simplicity_mallocTapEnv pRawTapEnv >>= newForeignPtr c_free_tapEnv

withEnv :: ForeignPtr CTransaction -> Word32 -> ForeignPtr CTapEnv -> Hash256 -> (Ptr CTxEnv -> IO b) -> IO b
withEnv cTransaction ix cTapEnv genesisHash k =
  allocaBytes sizeof_txEnv $ \pTxEnv ->
  withForeignPtr cTransaction $ \pTransaction ->
  withForeignPtr cTapEnv $ \pTapEnv ->
  BS.useAsCString (encode genesisHash) $ \pGenesis -> do
   c_set_txEnv pTxEnv pTransaction pTapEnv pGenesis (fromIntegral ix)
   k pTxEnv

withPrimEnv :: PrimEnv -> (Ptr CTxEnv -> IO b) -> IO b
withPrimEnv env k = do
  cTransaction <- marshallTransaction (envTx env)
  cTapEnv <- marshallTapEnv (envTap env)
  withEnv cTransaction (envIx env) cTapEnv (envGenesisBlock env) k
