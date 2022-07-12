{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Elements.Programs.Transaction.lib' library instance into individual functions.
module Simplicity.Elements.Programs.Transaction.Lib
  ( numInputs
  , numOutputs
  , outputAssetAmount
  , inputAssetAmount
  , currentPegin
  , currentPrevOutpoint
  , currentAsset
  , currentAssetAmount
  , currentScriptHash
  , currentSequence
  , currentAnnexHash
  , currentScriptSigHash
  , currentReissuanceBlinding
  , currentNewIssuanceContract
  , currentReissuanceEntropy
  , currentIssuanceAssetAmt
  , currentIssuanceTokenAmt
  , currentIssuanceAssetProof
  , currentIssuanceTokenProof
  ) where

import qualified Simplicity.Elements.Programs.Transaction as Transaction

numInputs = Transaction.numInputs Transaction.lib
numOutputs = Transaction.numOutputs Transaction.lib
outputAssetAmount = Transaction.outputAssetAmount Transaction.lib
inputAssetAmount = Transaction.inputAssetAmount Transaction.lib
currentPegin = Transaction.currentPegin Transaction.lib
currentPrevOutpoint = Transaction.currentPrevOutpoint Transaction.lib
currentAsset = Transaction.currentAsset Transaction.lib
currentAssetAmount = Transaction.currentAssetAmount Transaction.lib
currentScriptHash = Transaction.currentScriptHash Transaction.lib
currentSequence = Transaction.currentSequence Transaction.lib
currentAnnexHash = Transaction.currentAnnexHash Transaction.lib
currentScriptSigHash = Transaction.currentScriptSigHash Transaction.lib
currentReissuanceBlinding = Transaction.currentReissuanceBlinding Transaction.lib
currentNewIssuanceContract = Transaction.currentNewIssuanceContract Transaction.lib
currentReissuanceEntropy = Transaction.currentReissuanceEntropy Transaction.lib
currentIssuanceAssetAmt = Transaction.currentIssuanceAssetAmt Transaction.lib
currentIssuanceTokenAmt = Transaction.currentIssuanceTokenAmt Transaction.lib
currentIssuanceAssetProof = Transaction.currentIssuanceAssetProof Transaction.lib
currentIssuanceTokenProof = Transaction.currentIssuanceTokenProof Transaction.lib
