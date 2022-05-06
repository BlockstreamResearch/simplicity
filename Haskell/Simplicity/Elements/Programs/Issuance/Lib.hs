{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Elements.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Elements.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Elements.Programs.Issuance.Lib
  ( inputIssuance, inputIssuanceEntropy, inputIssuanceAsset, inputIssuanceToken
  , Issuance.Bit, Issuance.Hash
  ) where

import qualified Simplicity.Elements.Programs.Issuance as Issuance

inputIssuance = Issuance.inputIssuance Issuance.lib
inputIssuanceEntropy = Issuance.inputIssuanceEntropy Issuance.lib
inputIssuanceAsset = Issuance.inputIssuanceAsset Issuance.lib
inputIssuanceToken = Issuance.inputIssuanceToken Issuance.lib
