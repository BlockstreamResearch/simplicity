{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that access transaction data.
module Simplicity.Elements.Programs.Transaction
 ( Lib(Lib), lib
 , numInputs
 , numOutputs
 , outputAmount
 , inputAmount
 , currentPegin
 , currentPrevOutpoint
 , currentAsset
 , currentAmount
 , currentScriptHash
 , currentSequence
 , currentAnnexHash
 , currentScriptSigHash
 , currentReissuanceBlinding
 , currentNewIssuanceContract
 , currentReissuanceEntropy
 , currentIssuanceAssetAmount
 , currentIssuanceTokenAmount
 , currentIssuanceAssetProof
 , currentIssuanceTokenProof
 ) where

import Prelude hiding (take, drop)

import Simplicity.Digest
import Simplicity.Elements.Primitive
import Simplicity.Elements.Term hiding (one)
import Simplicity.Functor
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
    -- | Returns a pair of asset and amounts for the given output index.
    -- Returns Nothing of the index is out of range.
  , outputAmount :: term Word32 (S (Conf Word256, Conf Word64))
    -- | Returns a pair of asset and amounts for the given input index.
    -- Returns Nothing of the index is out of range.
  , inputAmount :: term Word32 (S (Conf Word256, Conf Word64))
    -- | Returns the `InputPegin` of the `CurrentIndex`.
  , currentPegin :: term () (S Word256)
    -- | Returns the `InputPrevOutpoint` of the `CurrentIndex`.
  , currentPrevOutpoint :: term () (Word256,Word32)
    -- | Returns the `InputAsset` of the `CurrentIndex`.
  , currentAsset :: term () (Conf Word256)
    -- | Returns the `inputAmount` of the `CurrentIndex`.
  , currentAmount :: term () (Conf Word256, Conf Word64)
    -- | Returns the `InputScriptHash` of the `CurrentIndex`.
  , currentScriptHash :: term () Word256
    -- | Returns the `InputSequence` of the `CurrentIndex`.
  , currentSequence :: term () Word32
    -- | Returns the `InputAnnexHash` of the `CurrentIndex`.
  , currentAnnexHash :: term () (S Word256)
    -- | Returns the `InputScriptSigHash` of the `CurrentIndex`.
  , currentScriptSigHash :: term () Word256
    -- | Returns the `ReissuanceBlinding` of the `CurrentIndex`.
  , currentReissuanceBlinding :: term () (S Word256)
    -- | Returns the `NewIssuanceContract` of the `CurrentIndex`.
  , currentNewIssuanceContract :: term () (S Word256)
    -- | Returns the `ReissuanceEntropy` of the `CurrentIndex`.
  , currentReissuanceEntropy :: term () (S Word256)
    -- | Returns the `IssuanceAssetAmount` of the `CurrentIndex`.
  , currentIssuanceAssetAmount :: term () (S (Conf Word64))
    -- | Returns the `IssuanceTokenAmount` of the `CurrentIndex`.
  , currentIssuanceTokenAmount :: term () (S (Conf Word64))
    -- | Returns the `IssuanceAssetProof` of the `CurrentIndex`.
  , currentIssuanceAssetProof :: term () Word256
    -- | Returns the `IssuanceTokenProof` of the `CurrentIndex`.
  , currentIssuanceTokenProof :: term () Word256
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    {
      numInputs = m numInputs
    , numOutputs = m numOutputs
    , outputAmount = m outputAmount
    , inputAmount = m inputAmount
    , currentPegin = m currentPegin
    , currentPrevOutpoint = m currentPrevOutpoint
    , currentAsset = m currentAsset
    , currentAmount = m currentAmount
    , currentScriptHash = m currentScriptHash
    , currentSequence = m currentSequence
    , currentAnnexHash = m currentAnnexHash
    , currentScriptSigHash = m currentScriptSigHash
    , currentReissuanceBlinding = m currentReissuanceBlinding
    , currentNewIssuanceContract = m currentNewIssuanceContract
    , currentReissuanceEntropy = m currentReissuanceEntropy
    , currentIssuanceAssetAmount = m currentIssuanceAssetAmount
    , currentIssuanceTokenAmount = m currentIssuanceTokenAmount
    , currentIssuanceAssetProof = m currentIssuanceAssetProof
    , currentIssuanceTokenProof = m currentIssuanceTokenProof
    }

-- | Build the Transaction 'Lib' library.
lib :: forall term. (Assert term, Primitive term) => Lib term
lib = l
 where
  l@Lib{..} = Lib {
    numInputs = firstFail word32 (primitive InputScriptHash)

  , numOutputs = firstFail word32 (primitive OutputScriptHash)

  , outputAmount = primitive OutputAmount &&& primitive OutputAsset
               >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))

  , inputAmount = primitive InputAmount &&& primitive InputAsset
              >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))

  , currentPegin = primitive CurrentIndex >>> assert (primitive InputPegin)

  , currentPrevOutpoint = primitive CurrentIndex >>> assert (primitive InputPrevOutpoint)

  , currentAsset = primitive CurrentIndex >>> assert (primitive InputAsset)

  , currentAmount = primitive CurrentIndex >>> assert (inputAmount)

  , currentScriptHash = primitive CurrentIndex >>> assert (primitive InputScriptHash)

  , currentSequence = primitive CurrentIndex >>> assert (primitive InputSequence)

  , currentAnnexHash = primitive CurrentIndex >>> assert (primitive InputAnnexHash)

  , currentScriptSigHash = primitive CurrentIndex >>> assert (primitive InputScriptSigHash)

  , currentReissuanceBlinding = primitive CurrentIndex >>> assert (primitive ReissuanceBlinding)

  , currentNewIssuanceContract = primitive CurrentIndex >>> assert (primitive NewIssuanceContract)

  , currentReissuanceEntropy = primitive CurrentIndex >>> assert (primitive ReissuanceEntropy)

  , currentIssuanceAssetAmount = primitive CurrentIndex >>> assert (primitive IssuanceAssetAmount)

  , currentIssuanceTokenAmount = primitive CurrentIndex >>> assert (primitive IssuanceTokenAmount)

  , currentIssuanceAssetProof = primitive CurrentIndex >>> assert (primitive IssuanceAssetProof)

  , currentIssuanceTokenProof = primitive CurrentIndex >>> assert (primitive IssuanceTokenProof)
  }
