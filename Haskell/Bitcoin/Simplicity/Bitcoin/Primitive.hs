{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Bitcoin or Bitcoin-like applications.
module Simplicity.Bitcoin.Primitive
  ( Prim(..), primPrefix, primName
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
  TotalInputValue :: Prim () Word64
  CurrentIndex :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  InputAnnexHash :: Prim Word32 (Either () (Either () Word256))
  InputScriptSigHash :: Prim Word32 (Either () Word256)
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputScriptHash :: Prim Word32 (Either () Word256)
  TapleafVersion :: Prim () Word8
  Tappath :: Prim Word8 (Either () Word256)
  InternalKey :: Prim () PubKey
  ScriptCMR :: Prim () Word256
-- Other possible ideas:
  -- TxId :: Prim () Word256

instance Eq (Prim a b) where
  Version == Version = True
  LockTime == LockTime = True
  TotalInputValue == TotalInputValue = True
  CurrentIndex == CurrentIndex = True
  InputPrevOutpoint == InputPrevOutpoint = True
  InputValue == InputValue = True
  InputSequence == InputSequence = True
  InputAnnexHash == InputAnnexHash = True
  InputScriptSigHash == InputScriptSigHash = True
  TotalOutputValue == TotalOutputValue = True
  OutputValue == OutputValue = True
  OutputScriptHash == OutputScriptHash = True
  TapleafVersion == TapleafVersion = True
  Tappath == Tappath = True
  InternalKey == InternalKey = True
  ScriptCMR == ScriptCMR = True
  _ == _ = False

primPrefix :: String
primPrefix = "Bitcoin"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName Version = "version"
primName LockTime = "lockTime"
primName TotalInputValue = "totalInputValue"
primName CurrentIndex = "currentIndex"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName InputAnnexHash = "inputAnnexHash"
primName InputScriptSigHash = "inputScriptSigHash"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputScriptHash = "outputScriptHash"
primName TapleafVersion = "tapleafVersion"
primName Tappath = "tappath"
primName InternalKey = "internalKey"
primName ScriptCMR = "scriptCMR"

data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envTap :: TapEnv
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
  interpret TotalInputValue = element . return . toWord64 . fromIntegral . List.sum $ sigTxiValue <$> sigTxIn tx
  interpret CurrentIndex = element . return . toWord32 . toInteger $ ix
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)
  interpret InputValue = return . (atInput $ toWord64 . toInteger . sigTxiValue)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret InputAnnexHash = return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)
  interpret InputScriptSigHash = return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)
  interpret TotalOutputValue = element . return . toWord64 . fromIntegral . List.sum $ txoValue <$> sigTxOut tx
  interpret OutputValue = return . (atOutput $ toWord64 . fromIntegral . txoValue)
  interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)
  interpret TapleafVersion = element . return . toWord8 . toInteger . tapleafVersion $ envTap env
  interpret Tappath = return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8
  interpret InternalKey = element . return . encodeKey . tapInternalKey $ envTap env
  interpret ScriptCMR = element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env
