-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Primitive.Bitcoin.DataTypes where

-- import Control.Applicative ((<$>),(<*>))
import Data.Array (Array)
import Data.ByteString (ByteString)
import Data.Word (Word64, Word32, Word8)
{-
import Bitcoin.Serialize ( Serialize, Get
                         , get, getWord32le, getWord64le, getVarInteger, getList
                         , put, putWord32le, putWord64le, putVarInteger, putList
                         , encodeLazy, runPut )
-}

import Simplicity.Digest

-- | Unparsed Bitcoin Script.
-- Script in transactions outputs do not have to be parsable, so we encode this as a raw 'Data.ByteString.ByteString'.
type Script = ByteString

-- | Transaction locktime.
-- This represents either a block height or a block time.
-- It is encoded as a 32-bit value.
type Lock = Word32

-- | A type for Bitcoin amounts measured in units of satoshi.
type Value = Word64 -- bitcoin uses an Int64, but it doesn't really matter.

-- | An outpoint is an index into the TXO set.
data OutPoint = OutPoint { opHash :: Hash256
                         , opIndex :: Word32
                         } deriving Show
{-
instance Serialize OutPoint where
  get = do h <- get
           i <- getWord32le
           return (OutPoint h i)
  put (OutPoint h i) = put h >> putWord32le i
-}

-- | The data type for signed transaction inputs.
-- Note that signed transaction inputs for BIP 143 include the value of the input, which doesn't appear in the serialized transaction input format.
data SigTxInput = SigTxInput { sigTxiPreviousOutput :: OutPoint
                             , sigTxiValue :: Value
                             , sigTxiSequence :: Word32
                             } deriving Show

{-
instance Serialize TxInput where
  get = TxInput <$> get <*> get <*> getWord32le
  put (TxInput p s sq) = put p >> put s >> putWord32le sq
-}

-- | The data type for transaction outputs.
-- The signed transactin output format is identical to the serialized transaction output format.
data TxOutput = TxOutput { txoValue :: Value
                         , txoScript :: Script
                         } deriving Show
{-
instance Serialize TxOutput where
  get = TxOutput <$> getWord64le <*> get
  put (TxOutput v s) = putWord64le v >> put s
-}

-- | The data type for transactions in the context of signatures.
-- The data signed in a BIP 143 directly covers input values.
data SigTx = SigTx { sigTxVersion :: Word32
                   , sigTxIn :: Array Word32 SigTxInput
                   , sigTxOut :: Array Word32 TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

{-
instance Serialize Tx where
  get = Tx <$> getWord32le <*> getList <*> getList <*> get
  put (Tx v is os t) = putWord32le v >> putList is >> putList os >> put t
-}
