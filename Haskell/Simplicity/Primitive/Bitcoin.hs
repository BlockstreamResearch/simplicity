{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Bitcoin or Bitcoin-like applications.
module Simplicity.Primitive.Bitcoin
  ( Prim(..), primPrefix, primName
  , PrimEnv, primSem
  ) where

import Data.Array (Array, (!), bounds, elems, inRange)
import Data.Serialize (put, runPutLazy)
import qualified Data.Word

import Simplicity.Digest
import Simplicity.Primitive.Bitcoin.DataTypes
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
  CurrentIndex :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  NumOutputs :: Prim () Word32
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputScriptHash :: Prim Word32 (Either () Word256)
  ScriptCMR :: Prim () Word256
-- Other possible ideas:
  -- TxId :: Prim () Word256

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
primName CurrentIndex = "currentIndex"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName NumOutputs = "maxOutputs"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputScriptHash = "outputScriptHash"
primName ScriptCMR = "scriptCMR"

data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envScriptCMR :: Hash256
                       , envInputsHash :: Hash256
                       , envOutputsHash :: Hash256
                       }

primEnv :: SigTx -> Data.Word.Word32 -> Hash256 -> Maybe PrimEnv
primEnv tx ix scmr | cond = Just $ PrimEnv { envTx = tx
                                           , envIx = ix
                                           , envScriptCMR = scmr
                                           , envInputsHash = inputsHash
                                           , envOutputsHash = outputsHash
                                           }
                   | otherwise = Nothing
 where
  cond = inRange (bounds (sigTxIn tx)) ix
  -- Perhaps the inputs and outputs should be hashed into a binary tree instead?
  outputsHash = bslHash . runPutLazy $ mapM_ go (elems (sigTxOut tx))
   where
    go txo = put (txoValue txo)
          >> put (bslHash  (txoScript txo))
  inputsHash = bslHash . runPutLazy $ mapM_ go (elems (sigTxIn tx))
   where
    go txi = put (sigTxiPreviousOutput txi)
          >> put (sigTxiSequence txi)

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
  interpret Version = const . return . toWord32 . toInteger $ sigTxVersion tx
  interpret LockTime = const . return . toWord32 . toInteger $ sigTxLock tx
  interpret InputsHash = const . return . toWord256 . integerHash256 $ envInputsHash env
  interpret OutputsHash = const . return . toWord256 . integerHash256 $ envOutputsHash env
  interpret NumInputs = const . return . toWord32 . toInteger $ 1 + maxInput
  interpret TotalInputValue = const . return . toWord64 . fromIntegral . sum $ sigTxiValue <$> elems (sigTxIn tx)
  interpret CurrentPrevOutpoint = const $ encodeOutpoint . sigTxiPreviousOutput <$> currentInput
  interpret CurrentValue = const $ toWord64 . toInteger . sigTxiValue <$> currentInput
  interpret CurrentSequence = const $ toWord32 . toInteger . sigTxiSequence <$> currentInput
  interpret CurrentIndex = const . return . toWord32 . toInteger $ ix
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutput)
  interpret InputValue = return . (atInput $ toWord64 . toInteger . sigTxiValue)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret NumOutputs = const . return . toWord32 . toInteger $ 1 + maxOutput
  interpret TotalOutputValue = const . return . toWord64 . fromIntegral . sum $ txoValue <$> elems (sigTxOut tx)
  interpret OutputValue = return . (atOutput $ toWord64 . fromIntegral . txoValue)
  interpret OutputScriptHash = return . (atOutput $ toWord256 . integerHash256 . bslHash . txoScript)
  interpret ScriptCMR = const . return . toWord256 . integerHash256 $ envScriptCMR env
