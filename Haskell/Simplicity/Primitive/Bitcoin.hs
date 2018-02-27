{-# LANGUAGE GADTs #-}
module Simplicity.Primitive.Bitcoin
  ( Prim, primPrefix, primName
  ) where

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
  CurrentInput :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  MaxOutput :: Prim () Word32
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputHashScript :: Prim Word32 (Either () Word256)
  ScriptCode :: Prim () Word256

primPrefix :: String
primPrefix = "Bitcoin"

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
primName CurrentInput = "currentInput"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName MaxOutput = "maxOutput"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputHashScript = "outputHashScript"
primName ScriptCode = "scriptCode"
