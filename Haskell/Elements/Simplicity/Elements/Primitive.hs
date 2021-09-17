{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Elements sidechain applications.
module Simplicity.Elements.Primitive
  ( Prim(..), primPrefix, primName
  , getPrimBit, putPrimBit
  , PrimEnv, primEnv
  , primSem
  -- * Unimplemented
  , getPrimByte, putPrimByte
  ) where

import Control.Monad ((<=<), guard)
import Data.Array (Array, (!), bounds, elems, inRange)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as List
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Monoid as Monoid
import Data.Serialize (Get, getWord8,
                       Putter, put, putWord8, putWord32le, putWord64le, runPutLazy)
import qualified Data.Word

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.Programs.LibSecp256k1
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word

type Conf a = Either (Bit, Word256) a

type S a = Either () a

data Prim a b where
  Version :: Prim () Word32
  LockTime :: Prim () Word32
  InputsHash :: Prim () Word256
  OutputsHash :: Prim () Word256
  NumInputs :: Prim () Word32
  InputIsPegin :: Prim Word32 (S Bit)
  InputPrevOutpoint :: Prim Word32 (S (Word256,Word32))
  InputAsset :: Prim Word32 (S (Conf Word256))
  InputAmount :: Prim Word32 (S (Conf Word64))
  InputScriptHash :: Prim Word32 (S Word256)
  InputSequence :: Prim Word32 (S Word32)
  InputIssuanceBlinding :: Prim Word32 (S (S Word256))
  InputIssuanceContract :: Prim Word32 (S (S Word256))
  InputIssuanceEntropy :: Prim Word32 (S (S Word256))
  InputIssuanceAssetAmt :: Prim Word32 (S (S (Conf Word64)))
  InputIssuanceTokenAmt :: Prim Word32 (S (S (Conf Word64)))
  CurrentIndex :: Prim () Word32
  CurrentIsPegin :: Prim () Bit
  CurrentPrevOutpoint :: Prim () (Word256,Word32)
  CurrentAsset :: Prim () (Conf Word256)
  CurrentAmount :: Prim () (Conf Word64)
  CurrentScriptHash :: Prim () Word256
  CurrentSequence :: Prim () Word32
  CurrentIssuanceBlinding :: Prim () (S Word256)
  CurrentIssuanceContract :: Prim () (S Word256)
  CurrentIssuanceEntropy :: Prim () (S Word256)
  CurrentIssuanceAssetAmt :: Prim () (S (Conf Word64))
  CurrentIssuanceTokenAmt :: Prim () (S (Conf Word64))
  TapleafVersion :: Prim () Word8
  Tapbranch :: Prim Word8 (S Word256)
  InternalKey :: Prim () PubKey
  AnnexHash :: Prim () (S Word256)
  NumOutputs :: Prim () Word32
  OutputAsset :: Prim Word32 (S (Conf Word256))
  OutputAmount :: Prim Word32 (S (Conf Word64))
  OutputNonce :: Prim Word32 (S (S (Conf Word256)))
  OutputScriptHash :: Prim Word32 (S Word256)
  OutputNullDatum :: Prim (Word32, Word32) (S (S (Either (Word2, Word256) (Either Bit Word4))))
  Fee :: Prim Word256 Word64
  ScriptCMR :: Prim () Word256

instance Eq (Prim a b) where
  Version == Version = True
  LockTime == LockTime = True
  InputsHash == InputsHash = True
  OutputsHash == OutputsHash = True
  NumInputs == NumInputs = True
  InputIsPegin == InputIsPegin = True
  InputPrevOutpoint == InputPrevOutpoint = True
  InputAsset == InputAsset = True
  InputAmount == InputAmount = True
  InputScriptHash == InputScriptHash = True
  InputSequence == InputSequence = True
  InputIssuanceBlinding == InputIssuanceBlinding = True
  InputIssuanceContract == InputIssuanceContract = True
  InputIssuanceEntropy == InputIssuanceEntropy = True
  InputIssuanceAssetAmt == InputIssuanceAssetAmt = True
  InputIssuanceTokenAmt == InputIssuanceTokenAmt = True
  CurrentIndex == CurrentIndex = True
  CurrentIsPegin == CurrentIsPegin = True
  CurrentPrevOutpoint == CurrentPrevOutpoint = True
  CurrentAsset == CurrentAsset = True
  CurrentAmount == CurrentAmount = True
  CurrentScriptHash == CurrentScriptHash = True
  CurrentSequence == CurrentSequence = True
  CurrentIssuanceBlinding == CurrentIssuanceBlinding = True
  CurrentIssuanceContract == CurrentIssuanceContract = True
  CurrentIssuanceEntropy == CurrentIssuanceEntropy = True
  CurrentIssuanceAssetAmt == CurrentIssuanceAssetAmt = True
  CurrentIssuanceTokenAmt == CurrentIssuanceTokenAmt = True
  TapleafVersion == TapleafVersion = True
  Tapbranch == Tapbranch = True
  InternalKey == InternalKey = True
  AnnexHash == AnnexHash = True
  NumOutputs == NumOutputs = True
  OutputAsset == OutputAsset = True
  OutputAmount == OutputAmount = True
  OutputNonce == OutputNonce = True
  OutputScriptHash == OutputScriptHash = True
  OutputNullDatum == OutputNullDatum = True
  Fee == Fee = True
  ScriptCMR == ScriptCMR = True
  _ == _ = False

primPrefix :: String
primPrefix = "Elements"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName Version = "version"
primName LockTime = "lockTime"
primName InputsHash = "inputsHash"
primName OutputsHash = "outputsHash"
primName NumInputs = "numInputs"
primName InputIsPegin = "inputIsPegin"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputAsset = "inputAsset"
primName InputAmount = "inputAmount"
primName InputScriptHash = "inputScriptHash"
primName InputSequence = "inputSequence"
primName InputIssuanceBlinding = "inputIssuanceBlinding"
primName InputIssuanceContract = "inputIssuanceContract"
primName InputIssuanceEntropy = "inputIssuanceEntropy"
primName InputIssuanceAssetAmt = "inputIssuanceAssetAmt"
primName InputIssuanceTokenAmt = "inputIssuanceTokenAmt"
primName CurrentIndex = "currentIndex"
primName CurrentIsPegin = "currentIsPegin"
primName CurrentPrevOutpoint = "currentPrevOutpoint"
primName CurrentAsset = "currentAsset"
primName CurrentAmount = "currentAmount"
primName CurrentScriptHash = "currentScriptHash"
primName CurrentSequence = "currentSequence"
primName CurrentIssuanceBlinding = "currentIssuanceBlinding"
primName CurrentIssuanceContract = "currentIssuanceContract"
primName CurrentIssuanceEntropy = "currentIssuanceEntropy"
primName CurrentIssuanceAssetAmt = "currentIssuanceAssetAmt"
primName CurrentIssuanceTokenAmt = "currentIssuanceTokenAmt"
primName TapleafVersion = "tapleafVersion"
primName Tapbranch = "tapbranch"
primName InternalKey = "internalKey"
primName AnnexHash = "annexHash"
primName NumOutputs = "numOutputs"
primName OutputAsset = "outputAsset"
primName OutputAmount = "outputAmount"
primName OutputNonce = "outputNonce"
primName OutputScriptHash = "outputScriptHash"
primName OutputNullDatum = "outputNullDatum"
primName Fee = "fee"
primName ScriptCMR = "scriptCMR"

getPrimBit :: Monad m => m Bool -> m (SomeArrow Prim)
getPrimBit next =
  (((((makeArrow Version & makeArrow LockTime) & makeArrow InputIsPegin) & (makeArrow InputPrevOutpoint & makeArrow InputAsset)) &
    (((makeArrow InputAmount & makeArrow InputScriptHash) & makeArrow InputSequence) & (makeArrow InputIssuanceBlinding & makeArrow InputIssuanceContract))) &
   ((((makeArrow InputIssuanceEntropy & makeArrow InputIssuanceAssetAmt) & makeArrow InputIssuanceTokenAmt) & (makeArrow OutputAsset & makeArrow OutputAmount)) &
    (((makeArrow OutputNonce & makeArrow OutputScriptHash) & makeArrow OutputNullDatum) & (makeArrow ScriptCMR & makeArrow CurrentIndex)))) &
  (((((makeArrow CurrentIsPegin & makeArrow CurrentPrevOutpoint) & makeArrow CurrentAsset) & (makeArrow CurrentAmount & makeArrow CurrentScriptHash)) &
    (((makeArrow CurrentSequence & makeArrow CurrentIssuanceBlinding) & makeArrow CurrentIssuanceContract) & (makeArrow CurrentIssuanceEntropy & makeArrow CurrentIssuanceAssetAmt))) &
   ((((makeArrow CurrentIssuanceTokenAmt & makeArrow TapleafVersion) & makeArrow Tapbranch) & (makeArrow InternalKey & makeArrow AnnexHash)) &
     (((makeArrow InputsHash & makeArrow OutputsHash) & makeArrow NumInputs) & (makeArrow NumOutputs & makeArrow Fee))))
 where
  l & r = next >>= \b -> if b then r else l
  makeArrow p = return (SomeArrow p)

putPrimBit :: Prim a b -> DList Bool
putPrimBit = go
 where
  go :: Prim a b -> DList Bool
  go Version                      = ([o,o,o,o,o,o]++)
  go LockTime                     = ([o,o,o,o,o,i]++)
  go InputIsPegin                 = ([o,o,o,o,i]++)
  go InputPrevOutpoint            = ([o,o,o,i,o]++)
  go InputAsset                   = ([o,o,o,i,i]++)
  go InputAmount                  = ([o,o,i,o,o,o]++)
  go InputScriptHash              = ([o,o,i,o,o,i]++)
  go InputSequence                = ([o,o,i,o,i]++)
  go InputIssuanceBlinding        = ([o,o,i,i,o]++)
  go InputIssuanceContract        = ([o,o,i,i,i]++)
  go InputIssuanceEntropy         = ([o,i,o,o,o,o]++)
  go InputIssuanceAssetAmt        = ([o,i,o,o,o,i]++)
  go InputIssuanceTokenAmt        = ([o,i,o,o,i]++)
  go OutputAsset                  = ([o,i,o,i,o]++)
  go OutputAmount                 = ([o,i,o,i,i]++)
  go OutputNonce                  = ([o,i,i,o,o,o]++)
  go OutputScriptHash             = ([o,i,i,o,o,i]++)
  go OutputNullDatum              = ([o,i,i,o,i]++)
  go ScriptCMR                    = ([o,i,i,i,o]++)
  go CurrentIndex                 = ([o,i,i,i,i]++)
-- :TODO: Below here are primitives that are likely candidates for being jets instead of primitives (see https://github.com/ElementsProject/simplicity/issues/5).
  go CurrentIsPegin               = ([i,o,o,o,o,o]++)
  go CurrentPrevOutpoint          = ([i,o,o,o,o,i]++)
  go CurrentAsset                 = ([i,o,o,o,i]++)
  go CurrentAmount                = ([i,o,o,i,o]++)
  go CurrentScriptHash            = ([i,o,o,i,i]++)
  go CurrentSequence              = ([i,o,i,o,o,o]++)
  go CurrentIssuanceBlinding      = ([i,o,i,o,o,i]++)
  go CurrentIssuanceContract      = ([i,o,i,o,i]++)
  go CurrentIssuanceEntropy       = ([i,o,i,i,o]++)
  go CurrentIssuanceAssetAmt      = ([i,o,i,i,i]++)
  go CurrentIssuanceTokenAmt      = ([i,i,o,o,o,o]++)
  go TapleafVersion               = ([i,i,o,o,o,i]++)
  go Tapbranch                    = ([i,i,o,o,i]++)
  go InternalKey                  = ([i,i,o,i,o]++)
  go AnnexHash                    = ([i,i,o,i,i]++)
  go InputsHash                   = ([i,i,i,o,o,o]++)
  go OutputsHash                  = ([i,i,i,o,o,i]++)
  go NumInputs                    = ([i,i,i,o,i]++)
  go NumOutputs                   = ([i,i,i,i,o]++)
  go Fee                          = ([i,i,i,i,i]++)
  (o,i) = (False, True)

data PrimEnv = PrimEnv { -- envParentGenesisBlockHash :: Hash256
                         envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envTap :: TapEnv
                       , envScriptCMR :: Hash256
                       , envInputsHash :: Hash256
                       , envOutputsHash :: Hash256
                       }

primEnv :: SigTx -> Data.Word.Word32 -> TapEnv -> Hash256 -> Maybe PrimEnv
primEnv tx ix tap scmr | cond = Just $ PrimEnv { envTx = tx
                                               , envIx = ix
                                               , envTap = tap
                                               , envScriptCMR = scmr
                                               , envInputsHash = sigTxInputsHash tx
                                               , envOutputsHash = sigTxOutputsHash tx
                                               }
                   | otherwise = Nothing
 where
  cond = inRange (bounds (sigTxIn tx)) ix

primSem :: Prim a b -> a -> PrimEnv -> Maybe b
primSem p a env = interpret p a
 where
  tx = envTx env
  ix = envIx env
  lookup a i | inRange range i = Just $ a ! i
             | otherwise       = Nothing
   where
    range = bounds a
  lookupInput = lookup (sigTxIn tx)
  lookupOutput = lookup (sigTxOut tx)
  currentInput = lookupInput ix
  maxInput = snd . bounds $ sigTxIn tx
  maxOutput = snd . bounds $ sigTxOut tx
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
  encodeConfidential enc (Confidential (Point by (Schnorr.PubKey x))) = Left (toBit by, toWord256 . toInteger $ x)
  encodeAsset = encodeConfidential encodeHash . asset
  encodeAmount = encodeConfidential (toWord64 . toInteger) . amount
  encodeNonce = cast . fmap (encodeConfidential encodeHash . nonce)
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
  encodeNullDatum OP7  = Right (Right (toWord4 0x5))
  encodeNullDatum OP8  = Right (Right (toWord4 0x6))
  encodeNullDatum OP9  = Right (Right (toWord4 0x8))
  encodeNullDatum OP10 = Right (Right (toWord4 0x9))
  encodeNullDatum OP11 = Right (Right (toWord4 0xa))
  encodeNullDatum OP12 = Right (Right (toWord4 0xb))
  encodeNullDatum OP13 = Right (Right (toWord4 0xc))
  encodeNullDatum OP14 = Right (Right (toWord4 0xd))
  encodeNullDatum OP15 = Right (Right (toWord4 0xe))
  encodeNullDatum OP16 = Right (Right (toWord4 0xf))
  interpret Version = element . return . toWord32 . toInteger $ sigTxVersion tx
  interpret LockTime = element . return . toWord32 . toInteger $ sigTxLock tx
  interpret InputsHash = element . return . encodeHash $ envInputsHash env
  interpret OutputsHash = element . return . encodeHash $ envOutputsHash env
  interpret NumInputs = element . return . toWord32 . toInteger $ 1 + maxInput
  interpret InputIsPegin = return . (atInput $ toBit . sigTxiIsPegin)
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)
  interpret InputAsset = return . (atInput $ encodeAsset . utxoAsset . sigTxiTxo)
  interpret InputAmount = return . (atInput $ encodeAmount . utxoAmount . sigTxiTxo)
  interpret InputScriptHash = return . (atInput $ encodeHash . bslHash . utxoScript . sigTxiTxo)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret InputIssuanceBlinding = return . (atInput $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceBlindingNonce) <=< sigTxiIssuance))
  interpret InputIssuanceContract = return . (atInput $
      cast . fmap encodeHash . (either (Just . newIssuanceContractHash) (const Nothing) <=< sigTxiIssuance))
  interpret InputIssuanceEntropy = return . (atInput $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceEntropy) <=< sigTxiIssuance))
  interpret InputIssuanceAssetAmt = return . (atInput $
      cast . fmap (encodeAmount . either newIssuanceAmount reissuanceAmount) . sigTxiIssuance)
  interpret InputIssuanceTokenAmt = return . (atInput $
      cast . fmap (encodeAmount . either newIssuanceTokenAmount (const (Amount (Explicit 0)))) . sigTxiIssuance)
  interpret CurrentIndex = element . return . toWord32 . toInteger $ ix
  interpret CurrentIsPegin = element $ toBit . sigTxiIsPegin <$> currentInput
  interpret CurrentPrevOutpoint = element $ encodeOutpoint . sigTxiPreviousOutpoint <$> currentInput
  interpret CurrentAsset = element $ encodeAsset . utxoAsset . sigTxiTxo <$> currentInput
  interpret CurrentAmount = element $ encodeAmount . utxoAmount . sigTxiTxo <$> currentInput
  interpret CurrentScriptHash = element $ encodeHash . bslHash . utxoScript . sigTxiTxo <$> currentInput
  interpret CurrentSequence = element $ toWord32 . toInteger . sigTxiSequence <$> currentInput
  interpret CurrentIssuanceBlinding = element $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceBlindingNonce) <=< sigTxiIssuance) <$> currentInput
  interpret CurrentIssuanceContract = element $
      cast . fmap encodeHash . (either (Just . newIssuanceContractHash) (const Nothing) <=< sigTxiIssuance) <$> currentInput
  interpret CurrentIssuanceEntropy = element $
      cast . fmap encodeHash . (either (const Nothing) (Just . reissuanceEntropy) <=< sigTxiIssuance) <$> currentInput
  interpret CurrentIssuanceAssetAmt = element $
      cast . fmap (encodeAmount . either newIssuanceAmount reissuanceAmount) . sigTxiIssuance <$> currentInput
  interpret CurrentIssuanceTokenAmt = element $
      cast . fmap (encodeAmount . either newIssuanceTokenAmount (const (Amount (Explicit 0)))) . sigTxiIssuance <$> currentInput
  interpret TapleafVersion = element . return . toWord8 . toInteger . tapLeafVersion $ envTap env
  interpret Tapbranch = return . cast . fmap encodeHash . listToMaybe . flip drop (tapBranch (envTap env)) . fromInteger . fromWord8
  interpret InternalKey = element . return . encodeKey . tapInternalKey $ envTap env
  interpret AnnexHash = element . return . cast $ encodeHash . bslHash <$> tapAnnex (envTap env)
  interpret NumOutputs = element . return . toWord32 . toInteger $ 1 + maxOutput
  interpret OutputAsset = return . (atOutput $ encodeAsset . txoAsset)
  interpret OutputAmount = return . (atOutput $ encodeAmount . txoAmount)
  interpret OutputNonce = return . (atOutput $ encodeNonce . txoNonce)
  interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)
  interpret OutputNullDatum = \(i, j) -> return . cast $ do
    txo <- lookupOutput . fromInteger $ fromWord32 i
    nullData <- txNullData $ txoScript txo
    return . cast . fmap (encodeNullDatum . fmap bslHash) . listToMaybe $ List.drop (fromInteger (fromWord32 j)) nullData
  interpret Fee = \assetId -> return . toWord64 . toInteger . Monoid.getSum $ foldMap (getValue assetId) (sigTxOut tx)
   where
    getValue assetId txo = fromMaybe (Monoid.Sum 0) $ do
      guard $ BSL.null (txoScript txo)
      Explicit a <- Just . asset $ txoAsset txo
      guard $ assetId == encodeHash a
      Explicit v <- Just . amount $ txoAmount txo
      return (Monoid.Sum v)
  interpret ScriptCMR = element . return . encodeHash $ envScriptCMR env

getPrimByte :: Data.Word.Word8 -> Get (Maybe (SomeArrow Prim))
getPrimByte = error "Simplicity.Elements.Primitive.getPrimByte is not implemented"

putPrimByte :: Putter (Prim a b)
putPrimByte = error "Simplicity.Elements.Primitive.putPrimByte is not implemented"
