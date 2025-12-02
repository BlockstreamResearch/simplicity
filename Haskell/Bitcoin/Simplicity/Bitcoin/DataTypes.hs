-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Bitcoin.DataTypes
  ( Script, Lock, Value
  , Outpoint(Outpoint), opHash, opIndex, putOutpointBE
  , SigTxInput(SigTxInput), sigTxiPreviousOutpoint, sigTxiTxo, sigTxiSequence, sigTxiAnnex, sigTxiScriptSig, sigTxiValue, sigTxiScript
  , TxOutput(TxOutput), txoValue, txoScript
  , SigTx(SigTx), sigTxVersion, sigTxIn, sigTxOut, sigTxLock
  , putNoWitnessTx, txid
  , TapEnv(..)
  , txTotalInputValue, txTotalOutputValue, txFee
  , txIsFinal, txLockDistance, txLockDuration
  , outputValuesHash, outputScriptsHash
  , outputsHash, outputHash
  , inputOutpointsHash, inputValuesHash, inputScriptsHash, inputUtxosHash
  , inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash, inputHash
  , txHash
  , tapleafHash, tappathHash, tapEnvHash
  , taptweak
  , module Simplicity.Bitcoin
  ) where

import Control.Monad (guard)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Semigroup (Max(Max,getMax), Sum(Sum,getSum))
import Data.Word (Word64, Word32, Word16, Word8)
import Data.Serialize ( Serialize
                      , Get, get, getWord8, getWord16le, getWord32le, getWord64le, getLazyByteString
                      , Putter, put, putWord8, putWord16le, putWord32be, putWord32le, putWord64be, putWord64le, putLazyByteString, runPutLazy
                      )
import Data.String (fromString)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Simplicity.Bitcoin
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec
import Simplicity.LibSecp256k1.Schnorr

{-
getVarInteger :: Get Word64
getVarInteger = go =<< getWord8
 where
  go 0xff = getWord64le
  go 0xfe = fromIntegral `fmap` getWord32le
  go 0xfd = fromIntegral `fmap` getWord16le
  go x = return (fromIntegral x)

putVarInteger :: Word64 -> Put
putVarInteger x | x < 0xfd = putWord8 (fromIntegral x)
                | x <= 0xffff = putWord8 0xfd >> putWord16le (fromIntegral x)
                | x <= 0xffffffff = putWord8 0xfe >> putWord32le (fromIntegral x)
                | otherwise = putWord8 0xff >> putWord64le (fromIntegral x)

getVarByteString :: Get BSL.ByteString
getVarByteString = do l <- getVarInteger
                      let l' = fromIntegral l :: Word32 -- length must be strictly less than 2^32.
                                                        -- This is how Bitcoin Core reads bytestrings.
                      getLazyByteString (fromIntegral l')
  where

putVarByteString :: BSL.ByteString -> Put
putVarByteString s | len < 2^32 = putVarInteger len >> putLazyByteString s
 where
  len :: Word64
  len = BSL.foldlChunks (\a c -> a + fromIntegral (BS.length c)) 0 s
-}

-- | Unparsed Bitcoin Script.
-- Script in transactions outputs do not have to be parsable, so we encode this as a raw 'Data.ByteString.ByteString'.
type Script = BSL.ByteString

-- | Transaction locktime.
-- This represents either a block height or a block time.
-- It is encoded as a 32-bit value.
type Lock = Word32

-- | A type for Bitcoin amounts measured in units of satoshi.
type Value = Word64 -- bitcoin uses an Int64, but it doesn't really matter.

moneyRange :: Value -> Bool
moneyRange v = v <= 21000000 * 10^8

getValue :: Get Value
getValue = do
  v <- getWord64le
  guard $ moneyRange v
  return v

-- | An outpoint is an index into the TXO set.
data Outpoint = Outpoint { opHash :: Hash256
                         , opIndex :: Word32
                         } deriving Show

instance Serialize Outpoint where
  get = Outpoint <$> get <*> getWord32le
  put (Outpoint h i) = put h >> putWord32le i

-- | Big endian serialization of an 'Outpoint'
putOutpointBE :: Putter Outpoint
putOutpointBE op = put (opHash op)
                >> putWord32be (opIndex op)

-- | The data type for signed transaction inputs.
-- Note that signed transaction inputs for BIP 143 include the value of the input, which doesn't appear in the serialized transaction input format.
data SigTxInput = SigTxInput { sigTxiPreviousOutpoint :: Outpoint
                             , sigTxiTxo :: TxOutput
                             , sigTxiSequence :: Word32
                             , sigTxiAnnex :: Maybe BSL.ByteString
                             , sigTxiScriptSig :: Script -- length must be strictly less than 2^32.
                             } deriving Show

-- | The value of the input being spent.
sigTxiValue :: SigTxInput -> Value
sigTxiValue = txoValue . sigTxiTxo

-- | The value of the input being spent.
sigTxiScript :: SigTxInput -> Script
sigTxiScript = txoScript . sigTxiTxo

{-
instance Serialize SigTxInput where
  get = SigTxInput <$> get <*> getValue <*> getWord32le
  put (SigTxInput p v sq) = put p >> putWord64le v >> putWord32le sq
-}

-- | The data type for transaction outputs.
-- The signed transactin output format is identical to the serialized transaction output format.
data TxOutput = TxOutput { txoValue :: Value
                         , txoScript :: Script -- length must be strictly less than 2^32.
                         } deriving Show

{-
instance Serialize TxOutput where
  get = TxOutput <$> getValue <*> getVarByteString
  put (TxOutput v s) = putWord64le v >> putVarByteString s
-}

-- | The data type for transactions in the context of signatures.
-- The data signed in a BIP 143 directly covers input values.
data SigTx = SigTx { sigTxVersion :: Word32
                   , sigTxIn :: Vector SigTxInput
                   , sigTxOut :: Vector TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

{-
instance Serialize Tx where
  get = Tx <$> getWord32le <*> getList <*> getList <*> get
  put (Tx v is os t) = putWord32le v >> putList is >> putList os >> put t
-}

-- | Taproot specific environment data about the input being spent.
data TapEnv = TapEnv { tapleafVersion :: Word8
                     , tapInternalKey :: PubKey
                     , tappath :: [Hash256]
                     , tapScriptCMR :: Hash256
                     } deriving Show

txTotalInputValue :: SigTx -> Value
txTotalInputValue tx = getSum . foldMap (Sum . sigTxiValue) $ sigTxIn tx

txTotalOutputValue :: SigTx -> Value
txTotalOutputValue tx = getSum . foldMap (Sum . txoValue) $ sigTxOut tx

txFee :: SigTx -> Value
txFee tx = txTotalInputValue tx - txTotalOutputValue tx

txIsFinal :: SigTx -> Bool
txIsFinal tx = all finalSequence (sigTxIn tx)
 where
  finalSequence sigin = sigTxiSequence sigin == maxBound

txLockDistance :: SigTx -> Word16
txLockDistance tx | sigTxVersion tx < 2 = 0
                  | otherwise = getMax . foldMap distance $ sigTxIn tx
 where
  distance sigin = case parseSequence (sigTxiSequence sigin) of
                     Just (Left x) -> Max x
                     _ -> mempty

txLockDuration :: SigTx -> Word16
txLockDuration tx | sigTxVersion tx < 2 = 0
                  | otherwise = getMax . foldMap duration $ sigTxIn tx
 where
  duration sigin = case parseSequence (sigTxiSequence sigin) of
                     Just (Right x) -> Max x
                     _ -> mempty

-- | A hash of all 'txoValues's.
outputValuesHash :: SigTx -> Hash256
outputValuesHash tx = bslHash . runPutLazy $ mapM_ (putWord64be . txoValue) (sigTxOut tx)

-- | A hash of all 'txoScript' hashes.
outputScriptsHash :: SigTx -> Hash256
outputScriptsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . txoScript) (sigTxOut tx)

-- | A hash of
--
-- * 'outputValuesHash'
-- * 'outputScriptsHash'
outputsHash :: SigTx -> Hash256
outputsHash tx = bslHash . runPutLazy $ do
                   put $ outputValuesHash tx
                   put $ outputScriptsHash tx

-- | A hash of one output's
--
-- * value
-- * hash of its script
outputHash :: TxOutput -> Hash256
outputHash txo = bslHash . runPutLazy $ do
                   putWord64be $ txoValue txo
                   put . bslHash $ txoScript txo

-- | Serialize an input's previous output including whether the previous input is from an pegin or not, and which parent chain if it is a pegin.
putOutpoint :: Putter SigTxInput
putOutpoint txi = putOutpointBE (sigTxiPreviousOutpoint txi)

-- | A hash of all 'sigTxiPreviousOutpoint's.
inputOutpointsHash :: SigTx -> Hash256
inputOutpointsHash tx = bslHash . runPutLazy $ mapM_ putOutpoint (sigTxIn tx)

-- | A hash of all 'utxoValue's.
inputValuesHash :: SigTx -> Hash256
inputValuesHash tx = bslHash . runPutLazy $ mapM_ (putWord64be . sigTxiValue) (sigTxIn tx)

-- | A hash of all 'utxoScript' hashes.
inputScriptsHash :: SigTx -> Hash256
inputScriptsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . sigTxiScript) (sigTxIn tx)

-- | A hash of
--
-- * 'inputValuesHash'
-- * 'inputScriptsHash'
inputUtxosHash :: SigTx -> Hash256
inputUtxosHash tx = bslHash . runPutLazy $ do
                      put $ inputValuesHash tx
                      put $ inputScriptsHash tx

-- | A hash of all 'sigTxiSequence's.
inputSequencesHash :: SigTx -> Hash256
inputSequencesHash tx = bslHash . runPutLazy $ mapM_ (putWord32be . sigTxiSequence) (sigTxIn tx)

putAnnex :: Putter (Maybe BSL.ByteString)
putAnnex Nothing = putWord8 0x00
putAnnex (Just annex) = putWord8 0x01 >> put (bslHash annex)

-- | A hash of all 'sigTxiAnnex' hashes.
inputAnnexesHash :: SigTx -> Hash256
inputAnnexesHash tx = bslHash . runPutLazy $ mapM_ (putAnnex . sigTxiAnnex) (sigTxIn tx)

-- | A hash of all 'sigTxiScriptSig' hashes.
inputScriptSigsHash :: SigTx -> Hash256
inputScriptSigsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . sigTxiScriptSig) (sigTxIn tx)

-- | A hash of
--
-- * 'inputOutpointsHash'
-- * 'inputSequencesHash'
-- * 'inputAnnexesHash'
--
-- Note that 'inputScriptSigsHash' is excluded.
inputsHash :: SigTx -> Hash256
inputsHash tx = bslHash . runPutLazy $ do
                  put $ inputOutpointsHash tx
                  put $ inputSequencesHash tx
                  put $ inputAnnexesHash tx

-- | A hash of
--
-- * The inputs's outpoint (including if and where the pegin came from)
-- * The inputs's sequence number
-- * Whether or not the input has an annex and the hash of that annex.
inputHash :: SigTxInput -> Hash256
inputHash txi = bslHash . runPutLazy $ do
                  putOutpoint txi
                  putWord32be $ sigTxiSequence txi
                  putAnnex $ sigTxiAnnex txi

-- | A hash of
--
-- * 'sigTxVersion'
-- * 'sigTxLock'
-- * 'inputsHash'
-- * 'outputsHash'
-- * 'inputUtxosHash'
txHash :: SigTx -> Hash256
txHash tx = bslHash . runPutLazy $ do
              putWord32be $ sigTxVersion tx
              putWord32be $ sigTxLock tx
              put $ inputsHash tx
              put $ outputsHash tx
              put $ inputUtxosHash tx

-- | Serialize transaction data without witness data.
-- Mainly suitable for computing a 'txid'.
putNoWitnessTx :: Putter SigTx
putNoWitnessTx tx = do
  putWord32le $ sigTxVersion tx
  putVarInt (V.length (sigTxIn tx))
  mapM_ putInput (sigTxIn tx)
  putVarInt (V.length (sigTxOut tx))
  mapM_ putOutput (sigTxOut tx)
  putWord32le $ sigTxLock tx
 where
  putVarInt x | x < 0 = error "putVarInt: negative value"
              | x <= 0xFC = putWord8 (fromIntegral x)
              | x <= 0xFFFF = putWord8 0xFD >> putWord16le (fromIntegral x)
              | x <= 0xFFFFFFFF = putWord8 0xFE >> putWord32le (fromIntegral x)
              | x <= 0xFFFFFFFFFFFFFFFF = putWord8 0xFF >> putWord64le (fromIntegral x)
  putInput txi = do
    put (opHash (sigTxiPreviousOutpoint txi))
    putWord32le (opIndex (sigTxiPreviousOutpoint txi))
    putVarInt (BSL.length (sigTxiScriptSig txi))
    putLazyByteString (sigTxiScriptSig txi)
    putWord32le (sigTxiSequence txi)

  putOutput txo = do
    putWord64le (txoValue txo)
    putVarInt (BSL.length (txoScript txo))
    putLazyByteString (txoScript txo)

-- | Return the txid of the transaction.
txid :: SigTx -> Hash256
txid = bslDoubleHash . runPutLazy . putNoWitnessTx

-- | A hash of
--
-- * 'tapleafVersion'
-- * 'tapScriptCMR'
tapleafHash :: TapEnv -> Hash256
tapleafHash tapEnv = bslHash . runPutLazy $ do
  put tag
  put tag
  putWord8 $ tapleafVersion tapEnv
  putWord8 32
  put $ tapScriptCMR tapEnv
 where
  tag = bsHash (fromString "TapLeaf")

-- | A hash of 'tappath's.
tappathHash :: TapEnv -> Hash256
tappathHash tapEnv = bslHash . runPutLazy $ mapM_ put (tappath tapEnv)

-- | A hash of
--
-- * 'tapleafHash'
-- * 'tappathHash'
-- * 'tapInternalKey'
tapEnvHash :: TapEnv -> Hash256
tapEnvHash tapEnv = bslHash . runPutLazy $ do
              put $ tapleafHash tapEnv
              put $ tappathHash tapEnv
              put $ tapInternalKey tapEnv

-- | Implementation of BIP-0341's taptweak function.
taptweak :: PubKey -> Hash256 -> Maybe PubKey
taptweak (PubKey internalKey) h = do
  guard $ toInteger internalKey < fieldOrder
  guard $ h0 < groupOrder
  a <- scale (scalar h0) g
  b <- decompress (Point False xkey)
  GE x y <- gej_normalize . snd $ gej_ge_add_ex a b
  return $ PubKey (fe_pack x)
 where
  xkey = fe (toInteger internalKey)
  h0 = integerHash256 . bslHash . runPutLazy $ do
    put tag
    put tag
    put (fe_pack xkey)
    put h
  tag = bsHash (fromString "TapTweak")
