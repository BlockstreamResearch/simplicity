{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Elements sidechain applications.
module Simplicity.Elements.Primitive
  ( Prim(..), primPrefix, primName
  , PrimEnv, primEnv, envTx, envIx, envTap, envGenesisBlock
  , primEnvHash
  , primSem
  -- * Re-exported Types
  , S, Conf, PubKey
  ) where

import Control.Arrow ((***), (+++))
import Control.Monad ((<=<), guard)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as List
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Monoid as Monoid
import Data.Serialize (Get, getWord8,
                       Putter, put, putWord8, putWord32be, putWord32le, putWord64le, runPutLazy)
import qualified Data.Word
import Data.Vector as Vector ((!?), length)
import Lens.Family2 (to, view, under)
import Lens.Family2.Stock (some_)

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.Programs.Elements
import Simplicity.Programs.LibSecp256k1
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word

just_ f = some_ f

data Prim a b where
  Version :: Prim () Word32
  LockTime :: Prim () Word32
  InputPegin :: Prim Word32 (S (S Word256))
  InputPrevOutpoint :: Prim Word32 (S (Word256,Word32))
  InputAsset :: Prim Word32 (S (Conf Word256))
  InputAmount :: Prim Word32 (S (Conf Word64))
  InputScriptHash :: Prim Word32 (S Word256)
  InputSequence :: Prim Word32 (S Word32)
  InputAnnexHash :: Prim Word32 (S (S Word256))
  InputScriptSigHash :: Prim Word32 (S Word256)
  ReissuanceBlinding :: Prim Word32 (S (S Word256))
  NewIssuanceContract :: Prim Word32 (S (S Word256))
  ReissuanceEntropy :: Prim Word32 (S (S Word256))
  IssuanceAssetAmount :: Prim Word32 (S (S (Conf Word64)))
  IssuanceTokenAmount :: Prim Word32 (S (S (Conf Word64)))
  IssuanceAssetProof :: Prim Word32 (S Word256)
  IssuanceTokenProof :: Prim Word32 (S Word256)
  CurrentIndex :: Prim () Word32
  TapleafVersion :: Prim () Word8
  Tappath :: Prim Word8 (S Word256)
  InternalKey :: Prim () PubKey
  OutputAsset :: Prim Word32 (S (Conf Word256))
  OutputAmount :: Prim Word32 (S (Conf Word64))
  OutputNonce :: Prim Word32 (S (S (Conf Word256)))
  OutputScriptHash :: Prim Word32 (S Word256)
  OutputNullDatum :: Prim (Word32, Word32) (S (S (Either (Word2, Word256) (Either Bit Word4))))
  OutputSurjectionProof :: Prim Word32 (S Word256)
  OutputRangeProof :: Prim Word32 (S Word256)
  GenesisBlockHash :: Prim () Word256
  ScriptCMR :: Prim () Word256

instance Eq (Prim a b) where
  Version == Version = True
  LockTime == LockTime = True
  InputPegin == InputPegin = True
  InputPrevOutpoint == InputPrevOutpoint = True
  InputAsset == InputAsset = True
  InputAmount == InputAmount = True
  InputScriptHash == InputScriptHash = True
  InputSequence == InputSequence = True
  InputAnnexHash == InputAnnexHash = True
  InputScriptSigHash == InputScriptSigHash = True
  ReissuanceBlinding == ReissuanceBlinding = True
  NewIssuanceContract == NewIssuanceContract = True
  ReissuanceEntropy == ReissuanceEntropy = True
  IssuanceAssetAmount == IssuanceAssetAmount = True
  IssuanceTokenAmount == IssuanceTokenAmount = True
  IssuanceAssetProof == IssuanceAssetProof = True
  IssuanceTokenProof == IssuanceTokenProof = True
  CurrentIndex == CurrentIndex = True
  TapleafVersion == TapleafVersion = True
  Tappath == Tappath = True
  InternalKey == InternalKey = True
  OutputAsset == OutputAsset = True
  OutputAmount == OutputAmount = True
  OutputNonce == OutputNonce = True
  OutputScriptHash == OutputScriptHash = True
  OutputNullDatum == OutputNullDatum = True
  OutputSurjectionProof == OutputSurjectionProof = True
  OutputRangeProof == OutputRangeProof = True
  GenesisBlockHash == GenesisBlockHash = True
  ScriptCMR == ScriptCMR = True
  _ == _ = False

primPrefix :: String
primPrefix = "Elements"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName Version = "version"
primName LockTime = "lockTime"
primName InputPegin = "inputPegin"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputAsset = "inputAsset"
primName InputAmount = "inputAmount"
primName InputScriptHash = "inputScriptHash"
primName InputSequence = "inputSequence"
primName InputAnnexHash = "inputAnnexHash"
primName InputScriptSigHash = "inputScriptSigHash"
primName ReissuanceBlinding = "reissuanceBlinding"
primName NewIssuanceContract = "newIssuanceContract"
primName ReissuanceEntropy = "reissuanceEntropy"
primName IssuanceAssetAmount = "issuanceAssetAmount"
primName IssuanceTokenAmount = "issuanceTokenAmount"
primName IssuanceAssetProof = "issuanceAssetProof"
primName IssuanceTokenProof = "issuanceTokenProof"
primName CurrentIndex = "currentIndex"
primName TapleafVersion = "tapleafVersion"
primName Tappath = "tappath"
primName InternalKey = "internalKey"
primName OutputAsset = "outputAsset"
primName OutputAmount = "outputAmount"
primName OutputNonce = "outputNonce"
primName OutputScriptHash = "outputScriptHash"
primName OutputNullDatum = "outputNullDatum"
primName OutputSurjectionProof = "outputSurjectionProof"
primName OutputRangeProof = "outputRangeProof"
primName GenesisBlockHash = "genesisBlockHash"
primName ScriptCMR = "scriptCMR"

data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envTap :: TapEnv
                       , envGenesisBlock :: Hash256
                       }

instance Show PrimEnv where
  showsPrec d env = showParen (d > 10)
                  $ showString "primEnv "
                  . showsPrec 11 (envTx env)
                  . showString " "
                  . showsPrec 11 (envIx env)
                  . showString " "
                  . showsPrec 11 (envTap env)

primEnv :: SigTx -> Data.Word.Word32 -> TapEnv -> Hash256 -> Maybe PrimEnv
primEnv tx ix tap gen | cond = Just $ PrimEnv { envTx = tx
                                              , envIx = ix
                                              , envTap = tap
                                              , envGenesisBlock = gen
                                              }
                      | otherwise = Nothing
 where
  cond = fromIntegral ix < Vector.length (sigTxIn tx)

-- | A hash of
--
-- * 'envGenesisBlock' twice (this effictively makes a tagged hash).
-- * 'txHash'
-- * 'tapEnvHash'
-- * 'envIx'
--
-- Note: this is the hash used for the "sig-all" hash.
primEnvHash :: PrimEnv -> Hash256
primEnvHash env = bslHash . runPutLazy $ do
                    put $ envGenesisBlock env
                    put $ envGenesisBlock env
                    put $ txHash (envTx env)
                    put $ tapEnvHash (envTap env)
                    putWord32be $ envIx env

primSem :: Prim a b -> a -> PrimEnv -> Maybe b
primSem p a env = interpret p a
 where
  tx = envTx env
  ix = envIx env
  lookupInput = (sigTxIn tx !?) . fromIntegral
  lookupOutput = (sigTxOut tx !?) . fromIntegral
  cast :: Maybe a -> Either () a
  cast (Just x) = Right x
  cast Nothing = Left ()
  element :: a -> () -> a
  element = const
  atInput :: (SigTxInput -> a) -> Word32 -> Either () a
  atInput f = cast . fmap f . lookupInput . fromInteger . fromWord32
  atOutput :: (TxOutput -> a) -> Word32 -> Either () a
  atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord32
  encodeHash = toWord256 . integerHash256
  encodeConfidential enc (Explicit a) = Right (enc a)
  encodeConfidential enc (Confidential (Point by x) ()) = Left (toBit by, toWord256 . Schnorr.fe_repr $ x)
  encodeAsset = encodeConfidential encodeHash . view (under asset)
  encodeAmount = encodeConfidential (toWord64 . toInteger) . view (under amount)
  encodeNonce = cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . nonce)
  encodeOutpoint op = (encodeHash $ opHash op, toWord32 . fromIntegral $ opIndex op)
  encodeKey (Schnorr.PubKey x) = toWord256 . toInteger $ x
  encodeNullDatum (Immediate h) = Left (toWord2 0, encodeHash h)
  encodeNullDatum (PushData h) = Left (toWord2 1, encodeHash h)
  encodeNullDatum (PushData2 h) = Left (toWord2 2, encodeHash h)
  encodeNullDatum (PushData4 h) = Left (toWord2 3, encodeHash h)
  encodeNullDatum OP1Negate = Right (Left (toBit False))
  encodeNullDatum OPReserved = Right (Left (toBit True))
  encodeNullDatum OP1  = Right (Right (toWord4 0x0))
  encodeNullDatum OP2  = Right (Right (toWord4 0x1))
  encodeNullDatum OP3  = Right (Right (toWord4 0x2))
  encodeNullDatum OP4  = Right (Right (toWord4 0x3))
  encodeNullDatum OP5  = Right (Right (toWord4 0x4))
  encodeNullDatum OP6  = Right (Right (toWord4 0x5))
  encodeNullDatum OP7  = Right (Right (toWord4 0x6))
  encodeNullDatum OP8  = Right (Right (toWord4 0x7))
  encodeNullDatum OP9  = Right (Right (toWord4 0x8))
  encodeNullDatum OP10 = Right (Right (toWord4 0x9))
  encodeNullDatum OP11 = Right (Right (toWord4 0xa))
  encodeNullDatum OP12 = Right (Right (toWord4 0xb))
  encodeNullDatum OP13 = Right (Right (toWord4 0xc))
  encodeNullDatum OP14 = Right (Right (toWord4 0xd))
  encodeNullDatum OP15 = Right (Right (toWord4 0xe))
  encodeNullDatum OP16 = Right (Right (toWord4 0xf))
  issuanceAmount = either newIssuanceAmount reissuanceAmount
  issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))
  interpret Version = element . return . toWord32 . toInteger $ sigTxVersion tx
  interpret LockTime = element . return . toWord32 . toInteger $ sigTxLock tx
  interpret InputPegin = return . (atInput $ cast . fmap encodeHash . sigTxiPegin)
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)
  interpret InputAsset = return . (atInput $ encodeAsset . utxoAsset . sigTxiTxo)
  interpret InputAmount = return . (atInput $ encodeAmount . utxoAmount . sigTxiTxo)
  interpret InputScriptHash = return . (atInput $ encodeHash . bslHash . utxoScript . sigTxiTxo)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret InputAnnexHash = return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)
  interpret InputScriptSigHash = return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)
  interpret ReissuanceBlinding = return . (atInput $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceBlindingNonce) <=< sigTxiIssuance))
  interpret NewIssuanceContract = return . (atInput $
      cast . fmap encodeHash . (either (Just . newIssuanceContractHash) (const Nothing) <=< sigTxiIssuance))
  interpret ReissuanceEntropy = return . (atInput $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceEntropy) <=< sigTxiIssuance))
  interpret IssuanceAssetAmount = return . (atInput $
      cast . fmap (encodeAmount . clearAmountPrf . issuanceAmount) . sigTxiIssuance)
  interpret IssuanceTokenAmount = return . (atInput $
      cast . fmap (encodeAmount . clearAmountPrf . issuanceTokenAmount) . sigTxiIssuance)
  interpret IssuanceAssetProof = return . (atInput $ encodeHash . bslHash . view (to sigTxiIssuance.just_.to issuanceAmount.under amount.prf_))
  interpret IssuanceTokenProof = return . (atInput $ encodeHash . bslHash . view (to sigTxiIssuance.just_.to issuanceTokenAmount.under amount.prf_))
  interpret CurrentIndex = element . return . toWord32 . toInteger $ ix
  interpret TapleafVersion = element . return . toWord8 . toInteger . tapleafVersion $ envTap env
  interpret Tappath = return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8
  interpret InternalKey = element . return . encodeKey . tapInternalKey $ envTap env
  interpret OutputAsset = return . (atOutput $ encodeAsset . clearAssetPrf . txoAsset)
  interpret OutputAmount = return . (atOutput $ encodeAmount . clearAmountPrf . txoAmount)
  interpret OutputNonce = return . (atOutput $ encodeNonce . txoNonce)
  interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)
  interpret OutputNullDatum = \(i, j) -> return . cast $ do
    txo <- lookupOutput . fromInteger $ fromWord32 i
    nullData <- txNullData $ txoScript txo
    return . cast . fmap (encodeNullDatum . fmap bslHash) . listToMaybe $ List.drop (fromInteger (fromWord32 j)) nullData
  interpret OutputSurjectionProof = return . (atOutput $ encodeHash . bslHash . view (to txoAsset.under asset.prf_))
  interpret OutputRangeProof = return . (atOutput $ encodeHash . bslHash . view (to txoAmount.under amount.prf_))
  interpret GenesisBlockHash = element . return . encodeHash $ envGenesisBlock env
  interpret ScriptCMR = element . return . encodeHash . tapScriptCMR $ envTap env
