{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Bitcoin or Bitcoin-like applications.
module Simplicity.Primitive.Bitcoin
  ( Prim(..), primPrefix, primName
  , PrimEnv, primSem
  ) where

import Data.Array (Array, (!), bounds, elems, inRange)
import qualified Data.Word

import Simplicity.Digest
import Simplicity.Primitive.Bitcoin.DataTypes
import Simplicity.Ty.Word

data Prim a b where
  NVersion :: Prim () Word32
  NLockTime :: Prim () Word32
  HashInputs :: Prim () Word256
  HashOutputs :: Prim () Word256
  MaxInput :: Prim () Word32
  TotalInputValue :: Prim () Word64
  CurrentPrevOutpoint :: Prim () (Word256,Word32)
  CurrentValue :: Prim () Word64
  CurrentSequence :: Prim () Word32
  CurrentIndex :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  MaxOutput :: Prim () Word32
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputHashScript :: Prim Word32 (Either () Word256)
  ScriptCode :: Prim () Word256
-- Other possible ideas:
  -- Fees :: Prim () Word64
  -- TxId :: Prim () Word256

primPrefix :: String
primPrefix = "Bitcoin"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName NVersion = "nVersion"
primName NLockTime = "nLockTime"
primName HashInputs = "hashInputs"
primName HashOutputs = "hashOutputs"
primName MaxInput = "maxInput"
primName TotalInputValue = "totalInputValue"
primName CurrentPrevOutpoint = "currentPrevOutpoint"
primName CurrentValue = "currentValue"
primName CurrentSequence = "currentSequence"
primName CurrentIndex = "currentIndex"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName MaxOutput = "maxOutput"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputHashScript = "outputHashScript"
primName ScriptCode = "scriptCode"

-- TODO: create an interface for generating PrimEnv.
data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envScriptCode :: Hash256
                       , envHashInputs :: Hash256
                       , envHashOutputs :: Hash256
                       }

primSem :: PrimEnv -> Prim a b -> a -> Maybe b
primSem env = interpret
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
  atInput :: (SigTxInput -> a) -> Word32 -> Either () a
  atInput f = cast . fmap f . lookupInput . fromInteger . fromWord32
  atOutput :: (TxOutput -> a) -> Word32 -> Either () a
  atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord32
  encodeOutpoint op = (toWord256 . integerHash256 $ opHash op, toWord32 . fromIntegral $ opIndex op)
  interpret NVersion = const . return . toWord32 . toInteger $ sigTxVersion tx
  interpret NLockTime = const . return . toWord32 . toInteger $ sigTxLock tx
  interpret HashInputs = const . return . toWord256 . integerHash256 $ envHashInputs env
  interpret HashOutputs = const . return . toWord256 . integerHash256 $ envHashOutputs env
  interpret MaxInput = const . return . toWord32 . toInteger $ maxInput
  interpret TotalInputValue = const . return . toWord64 . fromIntegral . sum $ sigTxiValue <$> elems (sigTxIn tx)
  interpret CurrentPrevOutpoint = const $ encodeOutpoint . sigTxiPreviousOutput <$> currentInput
  interpret CurrentValue = const $ toWord64 . toInteger . sigTxiValue <$> currentInput
  interpret CurrentSequence = const $ toWord32 . toInteger . sigTxiSequence <$> currentInput
  interpret CurrentIndex = const . return . toWord32 . toInteger $ ix
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutput)
  interpret InputValue = return . (atInput $ toWord64 . toInteger . sigTxiValue)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret MaxOutput = const . return . toWord32 . toInteger $ maxOutput
  interpret TotalOutputValue = const . return . toWord64 . fromIntegral . sum $ txoValue <$> elems (sigTxOut tx)
  interpret OutputValue = return . (atOutput $ toWord64 . fromIntegral . txoValue)
  interpret OutputHashScript = return . (atOutput $ toWord256 . integerHash256 . bsHash . txoScript)
  interpret ScriptCode = const . return . toWord256 . integerHash256 $ envScriptCode env
