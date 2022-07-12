{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Bitcoin.Programs.Transaction.lib' library instance into individual functions.
module Simplicity.Bitcoin.Programs.Transaction.Lib
  ( numInputs
  , numOutputs
  , currentPrevOutpoint
  , currentValue
--  , currentScriptHash
  , currentSequence
  , currentAnnexHash
  , currentScriptSigHash
  ) where

import qualified Simplicity.Bitcoin.Programs.Transaction as Transaction

numInputs = Transaction.numInputs Transaction.lib
numOutputs = Transaction.numOutputs Transaction.lib
currentPrevOutpoint = Transaction.currentPrevOutpoint Transaction.lib
currentValue = Transaction.currentValue Transaction.lib
-- currentScriptHash = Transaction.currentScriptHash Transaction.lib
currentSequence = Transaction.currentSequence Transaction.lib
currentAnnexHash = Transaction.currentAnnexHash Transaction.lib
currentScriptSigHash = Transaction.currentScriptSigHash Transaction.lib
