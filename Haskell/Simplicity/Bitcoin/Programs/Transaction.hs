{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that access transaction data.
module Simplicity.Bitcoin.Programs.Transaction
 ( Lib(Lib), lib
 , numInputs
 , numOutputs
 , totalInputValue
 , totalOutputValue
 , fee
 , currentPrevOutpoint
 , currentValue
 , currentScriptHash
 , currentSequence
 , currentAnnexHash
 , currentScriptSigHash
 ) where

import Prelude hiding (take, drop, subtract)

import Simplicity.Digest
import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.Term hiding (one)
import Simplicity.Functor
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Word
import Simplicity.Ty.Word

data Lib term =
 Lib
  {
    -- | Returns the number of inputs the transaction has.
    numInputs :: term () Word32
    -- | Returns the number of outputs the transaction has.
  , numOutputs :: term () Word32
  , totalInputValue :: term () Word64
  , totalOutputValue :: term () Word64
  , fee :: term () Word64
    -- | Returns the `InputPrevOutpoint` of the `CurrentIndex`.
  , currentPrevOutpoint :: term () (Word256,Word32)
    -- | Returns the `InputValue` of the `CurrentIndex`.
  , currentValue :: term () Word64
    -- | Returns the `InputScriptHash` of the `CurrentIndex`.
  , currentScriptHash :: term () Word256
    -- | Returns the `InputSequence` of the `CurrentIndex`.
  , currentSequence :: term () Word32
    -- | Returns the `InputAnnexHash` of the `CurrentIndex`.
  , currentAnnexHash :: term () (S Word256)
    -- | Returns the `InputScriptSigHash` of the `CurrentIndex`.
  , currentScriptSigHash :: term () Word256
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    {
      numInputs = m numInputs
    , numOutputs = m numOutputs
    , totalInputValue = m totalInputValue
    , totalOutputValue = m totalOutputValue
    , fee = m fee
    , currentPrevOutpoint = m currentPrevOutpoint
    , currentValue = m currentValue
    , currentScriptHash = m currentScriptHash
    , currentSequence = m currentSequence
    , currentAnnexHash = m currentAnnexHash
    , currentScriptSigHash = m currentScriptSigHash
    }

-- | Build the Transaction 'Lib' library.
lib :: forall term. (Assert term, Primitive term) => Lib term
lib = l
 where
  l@Lib{..} = Lib {
    numInputs = firstFail word32 (primitive InputValue)

  , numOutputs = firstFail word32 (primitive OutputValue)

  , totalInputValue = let
      body = take (drop (primitive InputValue)) &&& ih >>> match (injl ih) (injr (add word64 >>> ih))
     in (iden &&& zero word64) >>> forWhile word32 body >>> copair iden iden

  , totalOutputValue = let
      body = take (drop (primitive OutputValue)) &&& ih >>> match (injl ih) (injr (add word64 >>> ih))
     in (iden &&& zero word64) >>> forWhile word32 body >>> copair iden iden

  , fee = totalInputValue &&& totalOutputValue >>> subtract word64 >>> ih

  , currentPrevOutpoint = primitive CurrentIndex >>> assert (primitive InputPrevOutpoint)

  , currentValue = primitive CurrentIndex >>> assert (primitive InputValue)

  , currentScriptHash = primitive CurrentIndex >>> assert (primitive InputScriptHash)

  , currentSequence = primitive CurrentIndex >>> assert (primitive InputSequence)

  , currentAnnexHash = primitive CurrentIndex >>> assert (primitive InputAnnexHash)

  , currentScriptSigHash = primitive CurrentIndex >>> assert (primitive InputScriptSigHash)
  }
