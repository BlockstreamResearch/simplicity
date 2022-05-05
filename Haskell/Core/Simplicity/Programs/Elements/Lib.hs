{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Elements.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Elements.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.Elements.Lib
  ( Elements.Conf
  , calculateIssuanceEntropy, calculateAsset, calculateExplicitToken, calculateConfidentialToken
  , Elements.Hash
  ) where

import qualified Simplicity.Programs.Elements as Elements

-- Maybe this ought to be Template Haskell.
calculateIssuanceEntropy = Elements.calculateIssuanceEntropy Elements.lib
calculateAsset = Elements.calculateAsset Elements.lib
calculateExplicitToken = Elements.calculateExplicitToken Elements.lib
calculateConfidentialToken = Elements.calculateConfidentialToken Elements.lib
