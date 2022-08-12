{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Bitcoin or Bitcoin-like applications.
module Simplicity.Bitcoin.Primitive
  ( Prim(..), primPrefix, primName
  , getPrimBit, getPrimByte, putPrimBit, putPrimByte
  , PrimEnv(..), primEnv
  , primSem
  -- * Re-exported Types
  , PubKey
  ) where

import qualified Data.List as List
import Data.Maybe (listToMaybe)
import Data.Serialize (Get, getWord8,
                       Putter, put, putWord8, putWord32le, putWord64le, runPutLazy)
import qualified Data.Word
import Data.Vector as Vector ((!?), length)

import Simplicity.Digest
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.Programs.LibSecp256k1
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Word

data Prim a b where
  Version :: Prim () Word32
  LockTime :: Prim () Word32
  InputsHash :: Prim () Word256
  OutputsHash :: Prim () Word256
  NumInputs :: Prim () Word32
  TotalInputValue :: Prim () Word64
  CurrentPrevOutpoint :: Prim () (Word256,Word32)
  CurrentValue :: Prim () Word64
  CurrentSequence :: Prim () Word32
  CurrentAnnexHash :: Prim () (Either () Word256)
  CurrentScriptSigHash :: Prim () Word256
  CurrentIndex :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  InputAnnexHash :: Prim Word32 (Either () (Either () Word256))
  InputScriptSigHash :: Prim Word32 (Either () Word256)
  NumOutputs :: Prim () Word32
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputScriptHash :: Prim Word32 (Either () Word256)
  TapleafVersion :: Prim () Word8
  Tapbranch :: Prim Word8 (Either () Word256)
  InternalKey :: Prim () PubKey
  AnnexHash :: Prim () (Either () Word256)
  ScriptCMR :: Prim () Word256
-- Other possible ideas:
  -- TxId :: Prim () Word256

instance Eq (Prim a b) where
  Version == Version = True
  LockTime == LockTime = True
  InputsHash == InputsHash = True
  OutputsHash == OutputsHash = True
  NumInputs == NumInputs = True
  TotalInputValue == TotalInputValue = True
  CurrentPrevOutpoint == CurrentPrevOutpoint = True
  CurrentValue == CurrentValue = True
  CurrentSequence == CurrentSequence = True
  CurrentAnnexHash == CurrentAnnexHash = True
  CurrentScriptSigHash == CurrentScriptSigHash = True
  CurrentIndex == CurrentIndex = True
  InputPrevOutpoint == InputPrevOutpoint = True
  InputValue == InputValue = True
  InputSequence == InputSequence = True
  InputAnnexHash == InputAnnexHash = True
  InputScriptSigHash == InputScriptSigHash = True
  NumOutputs == NumOutputs = True
  TotalOutputValue == TotalOutputValue = True
  OutputValue == OutputValue = True
  OutputScriptHash == OutputScriptHash = True
  TapleafVersion == TapleafVersion = True
  Tapbranch == Tapbranch = True
  InternalKey == InternalKey = True
  AnnexHash == AnnexHash = True
  ScriptCMR == ScriptCMR = True
  _ == _ = False

primPrefix :: String
primPrefix = "Bitcoin"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName Version = "version"
primName LockTime = "lockTime"
primName InputsHash = "inputsHash"
primName OutputsHash = "outputsHash"
primName NumInputs = "numInputs"
primName TotalInputValue = "totalInputValue"
primName CurrentPrevOutpoint = "currentPrevOutpoint"
primName CurrentValue = "currentValue"
primName CurrentSequence = "currentSequence"
primName CurrentAnnexHash = "currentAnnexHash"
primName CurrentScriptSigHash = "currentScriptSigHash"
primName CurrentIndex = "currentIndex"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName InputAnnexHash = "inputAnnexHash"
primName InputScriptSigHash = "inputScriptSigHash"
primName NumOutputs = "maxOutputs"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputScriptHash = "outputScriptHash"
primName TapleafVersion = "tapleafVersion"
primName Tapbranch = "tapbranch"
primName InternalKey = "internalKey"
primName AnnexHash = "annexHash"
primName ScriptCMR = "scriptCMR"

getPrimBit :: Monad m => m Bool -> m (SomeArrow Prim)
getPrimBit next =
  ((((makeArrow Version & makeArrow LockTime) & makeArrow InputsHash) &
    ((makeArrow OutputsHash & makeArrow NumInputs) & makeArrow TotalInputValue)) &
   (((makeArrow CurrentPrevOutpoint & makeArrow CurrentValue) & makeArrow CurrentSequence) &
    (makeArrow CurrentIndex & makeArrow InputPrevOutpoint))) &
  ((((makeArrow InputValue & makeArrow InputSequence) & makeArrow NumOutputs) &
    ((makeArrow TotalOutputValue & makeArrow OutputValue) & makeArrow OutputScriptHash)) &
   (((makeArrow TapleafVersion & makeArrow Tapbranch) & makeArrow InternalKey) &
    (makeArrow AnnexHash & makeArrow ScriptCMR)))
 where
  l & r = next >>= \b -> if b then r else l
  makeArrow p = return (SomeArrow p)

getPrimByte :: Data.Word.Word8 -> Get (Maybe (SomeArrow Prim))
getPrimByte = return . decode
 where
  decode 0x24 = Just $ SomeArrow Version
  decode 0x25 = Just $ SomeArrow LockTime
  decode 0x26 = Just $ SomeArrow InputsHash
  decode 0x27 = Just $ SomeArrow OutputsHash
  decode 0x28 = Just $ SomeArrow NumInputs
  decode 0x29 = Just $ SomeArrow TotalInputValue
  decode 0x2a = Just $ SomeArrow CurrentPrevOutpoint
  decode 0x2b = Just $ SomeArrow CurrentValue
  decode 0x2c = Just $ SomeArrow CurrentSequence
  decode 0x2d = Just $ SomeArrow CurrentIndex
  decode 0x2e = Just $ SomeArrow InputPrevOutpoint
  decode 0x2f = Just $ SomeArrow InputValue
  decode 0x30 = Just $ SomeArrow InputSequence
  decode 0x31 = Just $ SomeArrow NumOutputs
  decode 0x32 = Just $ SomeArrow TotalOutputValue
  decode 0x33 = Just $ SomeArrow OutputValue
  decode 0x34 = Just $ SomeArrow OutputScriptHash
  decode 0x35 = Just $ SomeArrow TapleafVersion
  decode 0x36 = Just $ SomeArrow Tapbranch
  decode 0x37 = Just $ SomeArrow InternalKey
  decode 0x38 = Just $ SomeArrow AnnexHash
  decode 0x39 = Just $ SomeArrow ScriptCMR
  decode _ = Nothing

putPrimBit :: Prim a b -> DList Bool
putPrimBit = go
 where
  go :: Prim a b -> DList Bool
  go Version             = ([o,o,o,o,o]++)
  go LockTime            = ([o,o,o,o,i]++)
  go InputsHash          = ([o,o,o,i]++)
  go OutputsHash         = ([o,o,i,o,o]++)
  go NumInputs           = ([o,o,i,o,i]++)
  go TotalInputValue     = ([o,o,i,i]++)
  go CurrentPrevOutpoint = ([o,i,o,o,o]++)
  go CurrentValue        = ([o,i,o,o,i]++)
  go CurrentSequence     = ([o,i,o,i]++)
  go CurrentIndex        = ([o,i,i,o]++)
  go InputPrevOutpoint   = ([o,i,i,i]++)
  go InputValue          = ([i,o,o,o,o]++)
  go InputSequence       = ([i,o,o,o,i]++)
  go NumOutputs          = ([i,o,o,i]++)
  go TotalOutputValue    = ([i,o,i,o,o]++)
  go OutputValue         = ([i,o,i,o,i]++)
  go OutputScriptHash    = ([i,o,i,i]++)
  go TapleafVersion      = ([i,i,o,o,o]++)
  go Tapbranch           = ([i,i,o,o,i]++)
  go InternalKey         = ([i,i,o,i]++)
  go AnnexHash           = ([i,i,i,o]++)
  go ScriptCMR           = ([i,i,i,i]++)
  (o,i) = (False, True)

putPrimByte :: Putter (Prim a b)
putPrimByte = putWord8 . encode
 where
  encode :: Prim a b -> Data.Word.Word8
  encode Version             = 0x24
  encode LockTime            = 0x25
  encode InputsHash          = 0x26
  encode OutputsHash         = 0x27
  encode NumInputs           = 0x28
  encode TotalInputValue     = 0x29
  encode CurrentPrevOutpoint = 0x2a
  encode CurrentValue        = 0x2b
  encode CurrentSequence     = 0x2c
  encode CurrentIndex        = 0x2d
  encode InputPrevOutpoint   = 0x2e
  encode InputValue          = 0x2f
  encode InputSequence       = 0x30
  encode NumOutputs          = 0x31
  encode TotalOutputValue    = 0x32
  encode OutputValue         = 0x33
  encode OutputScriptHash    = 0x34
  encode TapleafVersion      = 0x35
  encode Tapbranch           = 0x36
  encode InternalKey         = 0x37
  encode AnnexHash           = 0x38
  encode ScriptCMR           = 0x39

data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envTap :: TapEnv
                       , envInputsHash :: Hash256
                       , envOutputsHash :: Hash256
                       }

instance Show PrimEnv where
  showsPrec d env = showParen (d > 10)
                  $ showString "primEnv "
                  . showsPrec 11 (envTx env)
                  . showString " "
                  . showsPrec 11 (envIx env)
                  . showString " "
                  . showsPrec 11 (envTap env)

primEnv :: SigTx -> Data.Word.Word32 -> TapEnv -> Maybe PrimEnv
primEnv tx ix tap | cond = Just $ PrimEnv { envTx = tx
                                          , envIx = ix
                                          , envTap = tap
                                          , envInputsHash = sigTxInputsHash tx
                                          , envOutputsHash = sigTxOutputsHash tx
                                          }
                  | otherwise = Nothing
 where
  cond = fromIntegral ix < Vector.length (sigTxIn tx)

primSem :: Prim a b -> a -> PrimEnv -> Maybe b
primSem p a env = interpret p a
 where
  tx = envTx env
  ix = envIx env
  lookupInput = (sigTxIn tx !?) . fromIntegral
  lookupOutput = (sigTxOut tx !?) . fromIntegral
  currentInput = lookupInput ix
  maxInput = fromIntegral $ Vector.length (sigTxIn tx) - 1
  maxOutput = fromIntegral $ Vector.length (sigTxOut tx) - 1
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
  encodeOutpoint op = (toWord256 . integerHash256 $ opHash op, toWord32 . fromIntegral $ opIndex op)
  encodeKey (Schnorr.PubKey x) = toWord256 . toInteger $ x
  interpret Version = element . return . toWord32 . toInteger $ sigTxVersion tx
  interpret LockTime = element . return . toWord32 . toInteger $ sigTxLock tx
  interpret InputsHash = element . return . encodeHash $ envInputsHash env
  interpret OutputsHash = element . return . encodeHash $ envOutputsHash env
  interpret NumInputs = element . return . toWord32 . toInteger $ 1 + maxInput
  interpret TotalInputValue = element . return . toWord64 . fromIntegral . List.sum $ sigTxiValue <$> sigTxIn tx
  interpret CurrentPrevOutpoint = element $ encodeOutpoint . sigTxiPreviousOutpoint <$> currentInput
  interpret CurrentValue = element $ toWord64 . toInteger . sigTxiValue <$> currentInput
  interpret CurrentSequence = element $ toWord32 . toInteger . sigTxiSequence <$> currentInput
  interpret CurrentAnnexHash = element $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex <$> currentInput
  interpret CurrentScriptSigHash = element $ encodeHash . bslHash . sigTxiScriptSig <$> currentInput
  interpret CurrentIndex = element . return . toWord32 . toInteger $ ix
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)
  interpret InputValue = return . (atInput $ toWord64 . toInteger . sigTxiValue)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret InputAnnexHash = return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)
  interpret InputScriptSigHash = return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)
  interpret NumOutputs = element . return . toWord32 . toInteger $ 1 + maxOutput
  interpret TotalOutputValue = element . return . toWord64 . fromIntegral . List.sum $ txoValue <$> sigTxOut tx
  interpret OutputValue = return . (atOutput $ toWord64 . fromIntegral . txoValue)
  interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)
  interpret TapleafVersion = element . return . toWord8 . toInteger . tapLeafVersion $ envTap env
  interpret Tapbranch = return . cast . fmap encodeHash . listToMaybe . flip drop (tapBranch (envTap env)) . fromInteger . fromWord8
  interpret InternalKey = element . return . encodeKey . tapInternalKey $ envTap env
  interpret AnnexHash = element . return . cast $ encodeHash . bslHash <$> tapAnnex (envTap env)
  interpret ScriptCMR = element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env
