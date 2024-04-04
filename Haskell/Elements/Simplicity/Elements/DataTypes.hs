{-# LANGUAGE DeriveTraversable, TupleSections #-}
-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Elements.DataTypes
  ( Point(..)
  , Script
  , TxNullDatumF(..), TxNullDatum, TxNullData, txNullData
  , Lock, Value, Entropy
  , Confidential(..), prf_
  , AssetWith(..), AssetWithWitness, Asset, asset, clearAssetPrf, putAsset
  , AmountWith(..), AmountWithWitness, Amount, amount, clearAmountPrf, putAmount
  , TokenAmountWith, TokenAmountWithWitness, TokenAmount
  , Nonce(..)
  , putNonce, getNonce
  , putIssuance
  , NewIssuance(..)
  , Reissuance(..)
  , Issuance
  , Outpoint(Outpoint), opHash, opIndex, putOutpointBE
  , UTXO(UTXO), utxoAsset, utxoAmount, utxoScript
  , SigTxInput(SigTxInput), sigTxiPegin, sigTxiPreviousOutpoint, sigTxiTxo, sigTxiSequence, sigTxiIssuance, sigTxiAnnex, sigTxiScriptSig
  , sigTxiIssuanceEntropy, sigTxiIssuanceAsset, sigTxiIssuanceToken
  , TxOutput(TxOutput), txoAsset, txoAmount, txoNonce, txoScript
  , SigTx(SigTx), sigTxVersion, sigTxIn, sigTxOut, sigTxLock
  , putNoWitnessTx, txid
  , TapEnv(..)
  , txIsFinal, txLockDistance, txLockDuration
  , calculateIssuanceEntropy, calculateAsset, calculateToken
  , outputAmountsHash, outputNoncesHash, outputScriptsHash
  , outputRangeProofsHash, outputSurjectionProofsHash, outputsHash, outputHash
  , inputOutpointsHash, inputAmountsHash, inputScriptsHash, inputUtxosHash, inputUtxoHash
  , inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash, inputHash
  , issuanceAssetAmountsHash, issuanceTokenAmountsHash, issuanceRangeProofsHash, issuancesHash, issuanceHash, issuanceBlindingEntropyHash
  , txHash
  , tapleafHash, tappathHash, tapEnvHash
  , outputFee, totalFee
  , module Simplicity.Bitcoin
  ) where

import Control.Monad (guard, mzero)
import Data.Bits ((.|.))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isJust)
import Data.Semigroup (Max(Max,getMax))
import Data.Serialize ( Serialize, encode
                      , Get, get, runGetLazy, lookAhead, getWord8, getWord16le, getWord32le, getLazyByteString, isEmpty
                      , Putter, put, putWord8, putWord64be, putWord64le, putWord32be, putWord32le, putWord16le, putLazyByteString, runPutLazy
                      )
import Data.String (fromString)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word64, Word32, Word16, Word8)
import Lens.Family2 ((&), (.~), (^.), over, review, to, under, view)
import Lens.Family2.Stock (some_)
import Lens.Family2.Unchecked (Adapter, adapter, Traversal)

import Simplicity.Bitcoin
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

just_ f = some_ f

-- | Unparsed Bitcoin Script.
-- Script in transactions outputs do not have to be parsable, so we encode this as a raw 'Data.ByteString.ByteString'.
type Script = BSL.ByteString
type SurjectionProof = BSL.ByteString
type RangeProof = BSL.ByteString

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

getFE :: Get FE
getFE = fmap fe_unpack get >>= maybe mzero return

putFE :: Putter FE
putFE = put . fe_pack

-- | Transaction locktime.
-- This represents either a block height or a block time.
-- It is encoded as a 32-bit value.
type Lock = Word32

type Value = Word64

type Entropy = Hash256

data Confidential prf a = Explicit a
                        | Confidential Point prf
                        deriving Show

prf_ :: Traversal (Confidential prfA a) (Confidential prfB a) prfA prfB
prf_ f (Confidential pt prf) = Confidential pt <$> f prf
prf_ f (Explicit x) = pure (Explicit x)

newtype AssetWith prf = Asset (Confidential prf Hash256) deriving Show
type Asset = AssetWith ()
type AssetWithWitness = AssetWith SurjectionProof

asset :: Adapter (AssetWith prfA) (AssetWith prfB) (Confidential prfA Hash256) (Confidential prfB Hash256)
asset = adapter to fro
 where
  to (Asset x) = x
  fro x = (Asset x)

clearAssetPrf :: AssetWith prf -> Asset
clearAssetPrf x = x & under asset . prf_ .~ ()

putAsset :: Putter Asset
putAsset (Asset (Explicit h)) = putWord8 0x01 >> put h
putAsset (Asset (Confidential (Point by x) _)) = putWord8 (if by then 0x0b else 0x0a) >> putFE x

newtype AmountWith prf = Amount (Confidential prf Value) deriving Show
type Amount = AmountWith ()
type AmountWithWitness = AmountWith RangeProof

type TokenAmountWith prf = AmountWith prf
type TokenAmount = Amount
type TokenAmountWithWitness = AmountWithWitness

amount :: Adapter (AmountWith prfA) (AmountWith prfB) (Confidential prfA Value) (Confidential prfB Value)
amount = adapter to fro
 where
  to (Amount x) = x
  fro x = (Amount x)

clearAmountPrf :: AmountWith prf -> Amount
clearAmountPrf x = x & under amount . prf_ .~ ()

putAmount :: Putter Amount
putAmount (Amount (Explicit v)) = putWord8 0x01 >> putWord64be v
putAmount (Amount (Confidential (Point by x) _)) = putWord8 (if by then 0x09 else 0x08) >> putFE x

newtype Nonce = Nonce { nonce :: Either (Bool, Word256) Hash256 } deriving Show

instance Serialize Nonce where
  put (Nonce (Right h)) = putWord8 0x01 >> put h
  put (Nonce (Left (by, x))) = putWord8 (if by then 0x03 else 0x02) >> put x
  get = lookAhead getWord8 >>= go
   where
    go 0x01 = getWord8 *> (Nonce . Right <$> get)
    go 0x02 = Nonce . Left . (False,) <$> get
    go 0x03 = Nonce . Left . (True,) <$> get
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
                               , newIssuanceAmount :: AmountWithWitness
                               , newIssuanceTokenAmount :: TokenAmountWithWitness
                               } deriving Show

data Reissuance = Reissuance { reissuanceBlindingNonce :: Hash256
                             , reissuanceEntropy :: Entropy
                             , reissuanceAmount :: AmountWithWitness
                             } deriving Show

type Issuance = Either NewIssuance Reissuance

putIssuance :: Putter (Maybe Issuance)
putIssuance Nothing = putWord8 0x00 >> putWord8 0x00
putIssuance (Just x) = go x
 where
  maybeZero (Amount (Explicit 0)) = Nothing
  maybeZero x = Just x
  -- We serialize the range/surjection proofs separately.
  go (Left new) = putMaybeConfidential putAmount (maybeZero . clearAmountPrf $ newIssuanceAmount new)
               >> putMaybeConfidential putAmount (maybeZero . clearAmountPrf $ newIssuanceTokenAmount new)
               >> put (0 :: Word256)
               >> put (newIssuanceContractHash new)
               >> put (bslHash (newIssuanceAmount new ^. (under amount.prf_)))
               >> put (bslHash (newIssuanceTokenAmount new ^. (under amount.prf_)))
  go (Right re) = putAmount (clearAmountPrf $ reissuanceAmount re)
               >> putWord8 0x00
               >> put (reissuanceBlindingNonce re)
               >> put (reissuanceEntropy re)
               >> put (bslHash (reissuanceAmount re ^. (under amount.prf_)))
               >> put (bslHash mempty)

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

-- | The data type for unspent transaction outputs.
data UTXO = UTXO { utxoAsset :: Asset
                 , utxoAmount :: Amount
                 , utxoScript :: Script -- length must be strictly less than 2^32.
                 } deriving Show

-- | The data type for signed transaction inputs, including a copy of the TXO being spent.
-- For pegins, the TXO data in 'sigTxiTxo' is synthesized.
data SigTxInput = SigTxInput { sigTxiPegin :: Maybe Hash256
                             , sigTxiPreviousOutpoint :: Outpoint
                             , sigTxiTxo :: UTXO
                             , sigTxiSequence :: Word32
                             , sigTxiIssuance :: Maybe Issuance
                             , sigTxiAnnex :: Maybe BSL.ByteString
                             , sigTxiScriptSig :: Script -- length must be strictly less than 2^32.
                             } deriving Show

-- | The data type for transaction outputs.
-- The signed transactin output format is identical to the serialized transaction output format.
data TxOutput = TxOutput { txoAsset :: AssetWithWitness
                         , txoAmount :: AmountWithWitness
                         , txoNonce :: Maybe Nonce
                         , txoScript :: Script -- length must be strictly less than 2^32.
                         } deriving Show

-- | The data type for transactions in the context of signatures.
-- The data signed in a BIP 143 directly covers input values.
data SigTx = SigTx { sigTxVersion :: Word32
                   , sigTxIn :: Vector SigTxInput
                   , sigTxOut :: Vector TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

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

-- | An implementation of GenerateIssuanceEntropy from Element's 'issuance.cpp'.
calculateIssuanceEntropy :: Outpoint -> Hash256 -> Entropy
calculateIssuanceEntropy op contract = ivHash $ compress noTagIv (bsHash (encode (bsHash (encode op))), contract)

-- | An implementation of CalculateAsset from Element's 'issuance.cpp'.
calculateAsset :: Entropy -> Hash256
calculateAsset entropy = ivHash $ compress noTagIv (entropy, review (over le256) 0)

-- | An implementation of CalculateToken from Element's 'issuance.cpp'.
calculateToken :: AmountWith prf -> Entropy -> Hash256
calculateToken amt entropy = ivHash $ compress noTagIv (entropy, review (over le256) tag)
 where
  tag | Amount (Explicit _) <- amt = 1
      | Amount (Confidential _ _) <- amt = 2

-- | The entropy value of an issuance there is one, either given by a reissuance, or derived from a new issuance.
sigTxiIssuanceEntropy :: SigTxInput -> Maybe Entropy
sigTxiIssuanceEntropy txi = either mkEntropy reissuanceEntropy <$> sigTxiIssuance txi
 where
  mkEntropy = calculateIssuanceEntropy (sigTxiPreviousOutpoint txi) . newIssuanceContractHash

-- | The issued asset ID if there is an issuance.
sigTxiIssuanceAsset :: SigTxInput -> Maybe Hash256
sigTxiIssuanceAsset = fmap calculateAsset . sigTxiIssuanceEntropy

-- | The issued token ID if there is an issuance.
sigTxiIssuanceToken :: SigTxInput -> Maybe Hash256
sigTxiIssuanceToken txi = calculateToken <$> amount <*> entropy
 where
  amount = either newIssuanceAmount reissuanceAmount <$> sigTxiIssuance txi
  entropy = sigTxiIssuanceEntropy txi

-- | A hash of all 'txoAsset's and 'txoAmount's.
outputAmountsHash :: SigTx -> Hash256
outputAmountsHash tx = bslHash . runPutLazy $ mapM_ go (sigTxOut tx)
 where
  go txo = putAsset (clearAssetPrf $ txoAsset txo)
        >> putAmount (clearAmountPrf $ txoAmount txo)

-- | A hash of all 'txoNonce's.
outputNoncesHash :: SigTx -> Hash256
outputNoncesHash tx = bslHash . runPutLazy $ mapM_ (putNonce . txoNonce) (sigTxOut tx)

-- | A hash of all 'txoScript' hashes.
outputScriptsHash :: SigTx -> Hash256
outputScriptsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . txoScript) (sigTxOut tx)

-- | A hash of all output range proof hashes.
outputRangeProofsHash :: SigTx -> Hash256
outputRangeProofsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . view (to txoAmount.under amount.prf_)) (sigTxOut tx)

-- | A hash of all output surjection proof hashes.
outputSurjectionProofsHash :: SigTx -> Hash256
outputSurjectionProofsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . view (to txoAsset.under asset.prf_)) (sigTxOut tx)

-- | A hash of
--
-- * 'outputAmountsHash'
-- * 'outputNoncesHash'
-- * 'outputScriptsHash'
-- * 'outputRangeProofsHash'
--
-- Note that 'outputSurjectionProofsHash' is excluded.
outputsHash :: SigTx -> Hash256
outputsHash tx = bslHash . runPutLazy $ do
                   put $ outputAmountsHash tx
                   put $ outputNoncesHash tx
                   put $ outputScriptsHash tx
                   put $ outputRangeProofsHash tx
                   -- outputSurjectionProofsHash omitted

-- | A hash of one output's
--
-- * asset and amount
-- * nonce
-- * hash of its script
-- * hash of its rangeproof.
--
-- Note that surjection proof is excluded.
outputHash :: TxOutput -> Hash256
outputHash txo = bslHash . runPutLazy $ do
                   putAsset . clearAssetPrf $ txoAsset txo
                   putAmount . clearAmountPrf $ txoAmount txo
                   putNonce $ txoNonce txo
                   put . bslHash $ txoScript txo
                   put . bslHash $ view (to txoAmount.under amount.prf_) txo
                   -- outputSurjectionProof omitted

-- | Serialize an input's previous output including whether the previous input is from an pegin or not, and which parent chain if it is a pegin.
putOutpoint :: Putter SigTxInput
putOutpoint txi = maybePut put (sigTxiPegin txi) >> putOutpointBE (sigTxiPreviousOutpoint txi)
 where
  maybePut _ Nothing = putWord8 0x00
  maybePut putter (Just x) = putWord8 0x01 >> putter x

-- | A hash of all 'sigTxiPegin's and 'sigTxiPreviousOutpoint's.
inputOutpointsHash :: SigTx -> Hash256
inputOutpointsHash tx = bslHash . runPutLazy $ mapM_ putOutpoint (sigTxIn tx)

-- | A hash of all 'utxoAsset's and 'utxoAmount's.
inputAmountsHash :: SigTx -> Hash256
inputAmountsHash tx = bslHash . runPutLazy $ mapM_ go (sigTxIn tx)
 where
  go txi = putAsset (clearAssetPrf . utxoAsset $ sigTxiTxo txi)
        >> putAmount (clearAmountPrf . utxoAmount $ sigTxiTxo txi)

-- | A hash of all 'utxoScript' hashs.
inputScriptsHash :: SigTx -> Hash256
inputScriptsHash tx = bslHash . runPutLazy $ mapM_ (put . bslHash . utxoScript . sigTxiTxo) (sigTxIn tx)

-- | A hash of
--
-- * 'inputAmountsHash'
-- * 'inputScriptsHash'
inputUtxosHash :: SigTx -> Hash256
inputUtxosHash tx = bslHash . runPutLazy $ do
                      put $ inputAmountsHash tx
                      put $ inputScriptsHash tx

-- | A hash of one utxo's
--
-- * asset and amount
-- * hash of its script
inputUtxoHash :: UTXO -> Hash256
inputUtxoHash utxo = bslHash . runPutLazy $ do
                   putAsset . clearAssetPrf $ utxoAsset utxo
                   putAmount . clearAmountPrf $ utxoAmount utxo
                   put . bslHash $ utxoScript utxo

-- | A hash of all 'sigTxiSequence's.
inputSequencesHash :: SigTx -> Hash256
inputSequencesHash tx = bslHash . runPutLazy $ mapM_ (putWord32be . sigTxiSequence) (sigTxIn tx)

putAnnex :: Putter (Maybe BSL.ByteString)
putAnnex Nothing = putWord8 0x00
putAnnex (Just annex) = putWord8 0x01 >> put (bslHash annex)

-- | A hash of all 'sigTxiAnnex' hashs.
inputAnnexesHash :: SigTx -> Hash256
inputAnnexesHash tx = bslHash . runPutLazy $ mapM_ (putAnnex . sigTxiAnnex) (sigTxIn tx)

-- | A hash of all 'sigTxiScriptSig' hashs.
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

putIssuanceAssetAmount :: Putter SigTxInput
putIssuanceAssetAmount txi = maybeConfPut putAsset (Asset . Explicit <$> sigTxiIssuanceAsset txi)
                          >> maybeConfPut putAmount (clearAmountPrf . either newIssuanceAmount reissuanceAmount <$> sigTxiIssuance txi)
 where
  maybeConfPut _ Nothing = putWord8 0x00
  maybeConfPut putter (Just x) = putter x

-- | A hash of 'sigTxiIssuanceAsset' and either 'newIssuanceAmount' or 'reissuanceAmount' pairs as an asset-amount hash.
--
-- Note that "null" amount is hashed as if it were an explicit zero.
--
-- When an input has no issuance, a pair of zero bytes, @0x00 0x00@ are hashed.
issuanceAssetAmountsHash :: SigTx -> Hash256
issuanceAssetAmountsHash tx = bslHash . runPutLazy $ mapM_ putIssuanceAssetAmount (sigTxIn tx)


putIssuanceTokenAmount :: Putter SigTxInput
putIssuanceTokenAmount txi = maybeConfPut putAsset (Asset . Explicit <$> sigTxiIssuanceToken txi)
                          >> maybeConfPut putAmount (clearAmountPrf . either newIssuanceTokenAmount (const (Amount (Explicit 0))) <$> sigTxiIssuance txi)
 where
  maybeConfPut _ Nothing = putWord8 0x00
  maybeConfPut putter (Just x) = putter x

-- | A hash of 'sigTxiIssuanceToken' and 'newIssuanceTokenAmount' pairs as an asset-amount hash.
--
-- Note that "null" amount is hashed as if it were an explicit zero.
--
-- When an input has no issuance, a pair of zero bytes, @0x00 0x00@ are hashed.
issuanceTokenAmountsHash :: SigTx -> Hash256
issuanceTokenAmountsHash tx = bslHash . runPutLazy $ mapM_ putIssuanceTokenAmount (sigTxIn tx)

putIssuanceRangeProof :: Putter (Maybe Issuance)
putIssuanceRangeProof issuance = put (bslHash . view (just_.under amount.prf_) $ either newIssuanceAmount reissuanceAmount <$> issuance)
                             >> put (bslHash . view (just_.under amount.prf_) $ either newIssuanceTokenAmount (const (Amount (Explicit 0))) <$> issuance)

-- | A hash of all issuance range proof hashes.
issuanceRangeProofsHash :: SigTx -> Hash256
issuanceRangeProofsHash tx = bslHash . runPutLazy $ mapM_ (putIssuanceRangeProof . sigTxiIssuance) (sigTxIn tx)

putIssuanceBlindingEntropy :: Putter (Maybe Issuance)
putIssuanceBlindingEntropy Nothing = putWord8 0x00
putIssuanceBlindingEntropy (Just issuance) = do putWord8 0x01
                                                put (either (const $ review (over be256) 0) reissuanceBlindingNonce $ issuance)
                                                put (either newIssuanceContractHash reissuanceEntropy $ issuance)

-- | A hash of all 'reissuanceBlindingNonce' and either 'newIssuanceContractHash' or 'reissuanceEntropy' values.
issuanceBlindingEntropyHash :: SigTx -> Hash256
issuanceBlindingEntropyHash tx = bslHash . runPutLazy $ mapM_ (putIssuanceBlindingEntropy . sigTxiIssuance) (sigTxIn tx)

-- | A hash of
--
-- * 'issuanceAssetAmountsHash'
-- * 'issuanceTokenAmountsHash'
-- * 'issuanceRangeProofsHash'
-- * 'issuanceBlindingEntropyHash'
issuancesHash :: SigTx -> Hash256
issuancesHash tx = bslHash . runPutLazy $ do
                     put $ issuanceAssetAmountsHash tx
                     put $ issuanceTokenAmountsHash tx
                     put $ issuanceRangeProofsHash tx
                     put $ issuanceBlindingEntropyHash tx

-- | A hash of
--
-- * If there is an issuance, the issued asset id and amount
-- * If there is an issuance, the issued token id and amount
-- * A hash of each of the rangeproofs
-- * If there is an issuance, the contract hash and blinding/entropy fields
issuanceHash :: SigTxInput -> Hash256
issuanceHash txi = bslHash . runPutLazy $ do
                     putIssuanceAssetAmount txi
                     putIssuanceTokenAmount txi
                     putIssuanceRangeProof (sigTxiIssuance txi)
                     putIssuanceBlindingEntropy (sigTxiIssuance txi)

-- | A hash of
--
-- * 'sigTxVersion'
-- * 'sigTxLock'
-- * 'inputsHash'
-- * 'outputsHash'
-- * 'issuancesHash'
-- * 'outputSurjectionProofsHash'
-- * 'inputUtxosHash'
txHash :: SigTx -> Hash256
txHash tx = bslHash . runPutLazy $ do
              putWord32be $ sigTxVersion tx
              putWord32be $ sigTxLock tx
              put $ inputsHash tx
              put $ outputsHash tx
              put $ issuancesHash tx
              put $ outputSurjectionProofsHash tx
              put $ inputUtxosHash tx

-- | Serialize transaction data without witness data.
-- Mainly suitable for computing a 'txid'.
putNoWitnessTx :: Putter SigTx
putNoWitnessTx tx = do
  putWord32le $ sigTxVersion tx
  putWord8 0
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
    putWord32le (flags .|. opIndex (sigTxiPreviousOutpoint txi))
    putVarInt (BSL.length (sigTxiScriptSig txi))
    putLazyByteString (sigTxiScriptSig txi)
    putWord32le (sigTxiSequence txi)
    putIssuance (sigTxiIssuance txi)
   where
    issuanceFlag | isJust (sigTxiIssuance txi) = 0x80000000
                 | otherwise = 0
    peginFlag | isJust (sigTxiPegin txi) = 0x40000000
              | otherwise = 0
    flags = issuanceFlag .|. peginFlag
    putIssuance Nothing = return ()
    putIssuance (Just (Left new)) = do
      put (0 :: Word256)
      put (newIssuanceContractHash new)
      putIssuanceAmount (clearAmountPrf (newIssuanceAmount new))
      putIssuanceAmount (clearAmountPrf (newIssuanceTokenAmount new))
    putIssuance (Just (Right re)) = do
      put (reissuanceBlindingNonce re)
      put (reissuanceEntropy re)
      putIssuanceAmount (clearAmountPrf (reissuanceAmount re))
      putWord8 0
    putIssuanceAmount (Amount (Explicit 0)) = putWord8 0
    putIssuanceAmount amt = putAmount amt

  putOutput txo = do
    putAsset (clearAssetPrf (txoAsset txo))
    putAmount (clearAmountPrf (txoAmount txo))
    putNonce (txoNonce txo)
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
  tag = bsHash (fromString "TapLeaf/elements")

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

-- | Decides if an output is a fee output.
-- If so, the (explicit) assetId and (explicit) value is returned.
outputFee :: TxOutput -> Maybe (Hash256, Value)
outputFee txo = do
  guard $ BSL.null (txoScript txo)
  Explicit assetId <- Just . view (under asset) $ txoAsset txo
  Explicit value <- Just . view (under amount) $ txoAmount txo
  return (assetId, value)

-- | Adds up all 'outputFee's to build a map from (explicit) assetId to total value.
totalFee :: SigTx -> Map.Map Hash256 Value
totalFee tx = Map.fromListWith (+) . catMaybes . map outputFee . toList $ sigTxOut tx
