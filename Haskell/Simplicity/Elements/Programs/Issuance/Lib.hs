{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Elements.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Elements.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Elements.Programs.Issuance.Lib
  ( issuance, issuanceEntropy, issuanceAsset, issuanceToken
  , Issuance.Bit, Issuance.Hash
  ) where

import qualified Simplicity.Elements.Programs.Issuance as Issuance

issuance = Issuance.issuance Issuance.lib
issuanceEntropy = Issuance.issuanceEntropy Issuance.lib
issuanceAsset = Issuance.issuanceAsset Issuance.lib
issuanceToken = Issuance.issuanceToken Issuance.lib
