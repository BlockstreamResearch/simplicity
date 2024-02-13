{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Elements.Programs.Transaction.lib' library instance into individual functions.
module Simplicity.Elements.Programs.Transaction.Lib
  ( numInputs
  , numOutputs
  , outputAmount
  , outputIsFee
  , totalFee
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

import qualified Simplicity.Elements.Programs.Transaction as Transaction

numInputs = Transaction.numInputs Transaction.lib
numOutputs = Transaction.numOutputs Transaction.lib
outputAmount = Transaction.outputAmount Transaction.lib
outputIsFee = Transaction.outputIsFee Transaction.lib
totalFee = Transaction.totalFee Transaction.lib
inputAmount = Transaction.inputAmount Transaction.lib
currentPegin = Transaction.currentPegin Transaction.lib
currentPrevOutpoint = Transaction.currentPrevOutpoint Transaction.lib
currentAsset = Transaction.currentAsset Transaction.lib
currentAmount = Transaction.currentAmount Transaction.lib
currentScriptHash = Transaction.currentScriptHash Transaction.lib
currentSequence = Transaction.currentSequence Transaction.lib
currentAnnexHash = Transaction.currentAnnexHash Transaction.lib
currentScriptSigHash = Transaction.currentScriptSigHash Transaction.lib
currentReissuanceBlinding = Transaction.currentReissuanceBlinding Transaction.lib
currentNewIssuanceContract = Transaction.currentNewIssuanceContract Transaction.lib
currentReissuanceEntropy = Transaction.currentReissuanceEntropy Transaction.lib
currentIssuanceAssetAmount = Transaction.currentIssuanceAssetAmount Transaction.lib
currentIssuanceTokenAmount = Transaction.currentIssuanceTokenAmount Transaction.lib
currentIssuanceAssetProof = Transaction.currentIssuanceAssetProof Transaction.lib
currentIssuanceTokenProof = Transaction.currentIssuanceTokenProof Transaction.lib
