{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Elements.Programs.Transaction.lib' library instance into individual functions.
module Simplicity.Elements.Programs.Transaction.Lib
  ( outputAssetAmount
  , inputAssetAmount
  , currentAssetAmount
  ) where

import qualified Simplicity.Elements.Programs.Transaction as Transaction

outputAssetAmount = Transaction.outputAssetAmount Transaction.lib
inputAssetAmount = Transaction.inputAssetAmount Transaction.lib
currentAssetAmount = Transaction.currentAssetAmount Transaction.lib
