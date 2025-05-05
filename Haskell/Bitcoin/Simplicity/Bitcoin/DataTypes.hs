-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Bitcoin.DataTypes
  ( Script, Lock, Value
  , Outpoint(Outpoint), opHash, opIndex
  , SigTxInput(SigTxInput), sigTxiPreviousOutpoint, sigTxiTxo, sigTxiSequence, sigTxiAnnex, sigTxiScriptSig, sigTxiValue
  , TxOutput(TxOutput), txoValue, txoScript
  , SigTx(SigTx), sigTxVersion, sigTxIn, sigTxOut, sigTxLock
  , TapEnv(..)
  , txIsFinal, txLockDistance, txLockDuration
  , module Simplicity.Bitcoin
  ) where

import Control.Monad (guard)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Semigroup (Max(Max,getMax))
import Data.Word (Word64, Word32, Word16, Word8)
import Data.Serialize ( Serialize
                      , Get, get, getWord8, getWord16le, getWord32le, getWord64le, getLazyByteString
                      , Put, put, putWord8, putWord16le, putWord32le, putWord64le, putLazyByteString, runPutLazy
                      )
import Data.Vector (Vector)

import Simplicity.Bitcoin
import Simplicity.Digest
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
