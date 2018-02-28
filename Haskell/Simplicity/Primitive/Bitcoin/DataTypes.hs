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

type Script = ByteString
type Lock = Word32
type Value = Word64 -- bitcoin uses an Int64, but it doesn't really matter.

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

data SigTxInput = SigTxInput { sigTxiPreviousOutput :: OutPoint
                             , sigTxiValue :: Value
                             , sigTxiSequence :: Word32
                             } deriving Show

{-
instance Serialize TxInput where
  get = TxInput <$> get <*> get <*> getWord32le
  put (TxInput p s sq) = put p >> put s >> putWord32le sq
-}

data TxOutput = TxOutput { txoValue :: Value
                         , txoScript :: Script
                         } deriving Show
{-
instance Serialize TxOutput where
  get = TxOutput <$> getWord64le <*> get
  put (TxOutput v s) = putWord64le v >> put s
-}

data SigTx = SigTx { sigTxVersion :: Word32 -- I think the txVersion should be restricted to 1, but this isn't how bitcoin works.
                   , sigTxIn :: Array Word32 SigTxInput
                   , sigTxOut :: Array Word32 TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

{-
instance Serialize Tx where
  get = Tx <$> getWord32le <*> getList <*> getList <*> get
  put (Tx v is os t) = putWord32le v >> putList is >> putList os >> put t
-}
