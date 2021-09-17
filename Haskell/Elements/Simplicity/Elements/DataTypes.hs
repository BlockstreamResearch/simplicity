{-# LANGUAGE DeriveTraversable #-}
-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Elements.DataTypes
  ( Point(..)
  , Script
  , TxNullDatumF(..), TxNullDatum, TxNullData, txNullData
  , Lock, Value
  , Confidential(..)
  , Asset(..), Amount(..), TokenAmount, Nonce(..)
  , putNonce, getNonce
  , putIssuance, getIssuance
  , NewIssuance, newIssuanceContractHash, newIssuanceAmount, newIssuanceTokenAmount
  , Reissuance, reissuanceBlindingNonce, reissuanceEntropy, reissuanceAmount
  , Issuance
  , Outpoint(Outpoint), opHash, opIndex
  , UTXO(UTXO), utxoAsset, utxoAmount, utxoScript
  , SigTxInput(SigTxInput), sigTxiIsPegin, sigTxiPreviousOutpoint, sigTxiTxo, sigTxiSequence, sigTxiIssuance
  , TxOutput(TxOutput), txoAsset, txoAmount, txoNonce, txoScript
  , SigTx(SigTx), sigTxVersion, sigTxIn, sigTxOut, sigTxLock, sigTxInputsHash, sigTxOutputsHash
  , TapEnv(..)
  ) where

import Control.Monad (guard, mzero)
import Data.Array (Array, elems)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Word (Word64, Word32)
import Data.Serialize ( Serialize
                      , Get, get, runGetLazy, lookAhead, getWord8, getWord16le, getWord32le, getLazyByteString, isEmpty
                      , Putter, put, putWord8, putWord32le, putWord64be, putLazyByteString, runPutLazy
                      )

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

data Point = Point Bool PubKey deriving Show

-- | Unparsed Bitcoin Script.
-- Script in transactions outputs do not have to be parsable, so we encode this as a raw 'Data.ByteString.ByteString'.
type Script = BSL.ByteString

data TxNullDatumF a = Immediate a
                    | PushData a
                    | PushData2 a
                    | PushData4 a
                    | OP1Negate
                    | OPReserved
                    | OP1
                    | OP2
                    | OP3
                    | OP4
                    | OP5
                    | OP6
                    | OP7
                    | OP8
                    | OP9
                    | OP10
                    | OP11
                    | OP12
                    | OP13
                    | OP14
                    | OP15
                    | OP16
                    deriving (Functor, Foldable, Traversable, Show)

type TxNullDatum = TxNullDatumF BSL.ByteString
type TxNullData = [TxNullDatum]

getTxNullDatum :: Get TxNullDatum
getTxNullDatum = getWord8 >>= go
 where
  go 0x60 = return OP16
  go 0x5f = return OP15
  go 0x5e = return OP14
  go 0x5d = return OP13
  go 0x5c = return OP12
  go 0x5b = return OP11
  go 0x5a = return OP10
  go 0x59 = return OP9
  go 0x58 = return OP8
  go 0x57 = return OP7
  go 0x56 = return OP6
  go 0x55 = return OP5
  go 0x54 = return OP4
  go 0x53 = return OP3
  go 0x52 = return OP2
  go 0x51 = return OP1
  go 0x50 = return OPReserved
  go 0x4f = return OP1Negate
  go 0x4e = do
    n <- getWord32le
    PushData4 <$> getLazyByteString (fromIntegral n)
  go 0x4d = do
    n <- getWord16le
    PushData2 <$> getLazyByteString (fromIntegral n)
  go 0x4c = do
    n <- getWord8
    PushData <$> getLazyByteString (fromIntegral n)
  go op | op < 0x4c = Immediate <$> getLazyByteString (fromIntegral op)
        | otherwise = fail $ "Serialize.get{getTxNullDatum}: " ++ show op ++ "is not a push-data opcode."

txNullData :: Script -> Maybe TxNullData
txNullData = either (const Nothing) Just . runGetLazy prog
 where
  prog = do
    0x6a <- getWord8
    go
  go = do
    emp <- isEmpty
    if emp then return [] else ((:) <$> getTxNullDatum <*> go)

-- | Transaction locktime.
-- This represents either a block height or a block time.
-- It is encoded as a 32-bit value.
type Lock = Word32

type Value = Word64

data Confidential a = Explicit a
                    | Confidential Point
                    deriving Show

newtype Asset = Asset { asset :: Confidential Hash256 } deriving Show

instance Serialize Asset where
  put (Asset (Explicit h)) = putWord8 0x01 >> put h
  put (Asset (Confidential (Point by x))) = putWord8 (if by then 0x0b else 0x0a) >> put x
  get = getWord8 >>= go
   where
    go 0x01 = Asset . Explicit <$> get
    go 0x0a = Asset . Confidential . Point False <$> get
    go 0x0b = Asset . Confidential . Point True <$> get
    go _ = fail "Serialize.get{Simplicity.Primitive.Elements.DataTypes.Asset}: bad prefix."

newtype Amount = Amount { amount :: Confidential Value } deriving Show
type TokenAmount = Amount

instance Serialize Amount where
  put (Amount (Explicit v)) = putWord8 0x01 >> putWord64be v
  put (Amount (Confidential (Point by x))) = putWord8 (if by then 0x09 else 0x08) >> put x
  get = getWord8 >>= go
   where
    go 0x01 = Amount . Explicit <$> get
    go 0x08 = Amount . Confidential . Point False <$> get
    go 0x09 = Amount . Confidential . Point True <$> get
    go _ = fail "Serialize.get{Simplicity.Primitive.Elements.DataTypes.Amount}: bad prefix."

newtype Nonce = Nonce { nonce :: Confidential Hash256 } deriving Show

instance Serialize Nonce where
  put (Nonce (Explicit h)) = putWord8 0x01 >> put h
  put (Nonce (Confidential (Point by x))) = putWord8 (if by then 0x03 else 0x02) >> put x
  get = lookAhead getWord8 >>= go
   where
    go 0x01 = getWord8 *> (Nonce . Explicit <$> get)
    go 0x02 = Nonce . Confidential . Point False <$> get
    go 0x03 = Nonce . Confidential . Point True <$> get
    go _ = fail "Serialize.get{Simplicity.Primitive.Elements.DataTypes.Nonce}: bad prefix."

putMaybeConfidential :: Putter a -> Putter (Maybe a)
putMaybeConfidential _ Nothing = putWord8 0x00
putMaybeConfidential p (Just a) = p a

getMaybeConfidential :: Get a -> Get (Maybe a)
getMaybeConfidential g = lookAhead getWord8 >>= go
 where
  go 0x00 = getWord8 *> pure Nothing
  go _ = Just <$> g

putNonce :: Putter (Maybe Nonce)
putNonce = putMaybeConfidential put

getNonce :: Get (Maybe Nonce)
getNonce = getMaybeConfidential get

data NewIssuance = NewIssuance { newIssuanceContractHash :: Hash256
                               , newIssuanceAmount :: Amount
                               , newIssuanceTokenAmount :: TokenAmount
                               } deriving Show

data Reissuance = Reissuance { reissuanceBlindingNonce :: Hash256
                             , reissuanceEntropy :: Hash256
                             , reissuanceAmount :: Amount
                             } deriving Show

type Issuance = Either NewIssuance Reissuance

putIssuance :: Putter (Maybe Issuance)
putIssuance Nothing = putWord8 0x00 >> putWord8 0x00
putIssuance (Just x) = go x
 where
  maybeZero (Amount (Explicit 0)) = Nothing
  maybeZero x = Just x
  go (Left new) = putMaybeConfidential put (maybeZero $ newIssuanceAmount new)
               >> putMaybeConfidential put (maybeZero $ newIssuanceTokenAmount new)
               >> put (0 :: Word256)
               >> put (newIssuanceContractHash new)
  go (Right re) = put (reissuanceAmount re)
               >> putWord8 0x00
               >> put (reissuanceBlindingNonce re)
               >> put (reissuanceEntropy re)

getIssuance :: Get (Maybe Issuance)
getIssuance = do
  amt <- zeroAmt =<< getMaybeConfidential get
  tokenAmt <- zeroAmt =<< getMaybeConfidential get
  go amt tokenAmt
 where
  zeroAmt Nothing = return . Amount $ Explicit 0
  zeroAmt (Just (Amount (Explicit 0))) = fail "Simplicity.Primitive.Elements.DataTypes.getIssuance: illegal explicit zero"
  zeroAmt (Just x) = return x
  go (Amount (Explicit 0)) (Amount (Explicit 0)) = return Nothing
  go amt tokenAmt = Just <$> do
    blinding <- get
    entropy <- get
    mkIssuance blinding entropy
   where
    mkIssuance blinding entropy | blinding == hash0 = return (Left (NewIssuance entropy amt tokenAmt))
                                | Amount (Explicit 0) <- tokenAmt = return (Right (Reissuance blinding entropy amt))
                                | otherwise = fail "Simplicity.Primitive.Elements.DataTypes.getIssuance: reissuance attempting to reissue tokens"

-- | An outpoint is an index into the TXO set.
data Outpoint = Outpoint { opHash :: Hash256
                         , opIndex :: Word32
                         } deriving Show

instance Serialize Outpoint where
  get = Outpoint <$> get <*> getWord32le
  put (Outpoint h i) = put h >> putWord32le i

-- | The data type for unspent transaction outputs.
data UTXO = UTXO { utxoAsset :: Asset
                 , utxoAmount :: Amount
                 , utxoScript :: Script -- length must be strictly less than 2^32.
                 } deriving Show

-- | The data type for signed transaction inputs, including a copy of the TXO being spent.
-- For pegins, the TXO data in 'sigTxiTxo' is synthesized.
data SigTxInput = SigTxInput { sigTxiIsPegin :: Bool
                             , sigTxiPreviousOutpoint :: Outpoint
                             , sigTxiTxo :: UTXO
                             , sigTxiSequence :: Word32
                             , sigTxiIssuance :: Maybe Issuance
                             } deriving Show

-- | The data type for transaction outputs.
-- The signed transactin output format is identical to the serialized transaction output format.
data TxOutput = TxOutput { txoAsset :: Asset
                         , txoAmount :: Amount
                         , txoNonce :: Maybe Nonce
                         , txoScript :: Script -- length must be strictly less than 2^32.
                         } deriving Show

-- | The data type for transactions in the context of signatures.
-- The data signed in a BIP 143 directly covers input values.
data SigTx = SigTx { sigTxVersion :: Word32
                   , sigTxIn :: Array Word32 SigTxInput
                   , sigTxOut :: Array Word32 TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

sigTxInputsHash tx = bslHash . runPutLazy $ mapM_ go (elems (sigTxIn tx))
 where
  go txi = put (sigTxiPreviousOutpoint txi)
        >> putWord32le (sigTxiSequence txi)
        >> putIssuance (sigTxiIssuance txi)

sigTxOutputsHash tx = bslHash . runPutLazy $ mapM_ go (elems (sigTxOut tx))
 where
  go txo = put (txoAsset txo) >> put (txoAmount txo)
        >> putNonce (txoNonce txo)
        >> put (bslHash (txoScript txo))

-- | Taproot specific environment data about the input being spent.
data TapEnv = TapEnv { tapAnnex :: Maybe BSL.ByteString
                     , tapLeafVersion :: Word8
                     , tapInternalKey :: PubKey
                     , tapBranch :: [Hash256]
                     }
