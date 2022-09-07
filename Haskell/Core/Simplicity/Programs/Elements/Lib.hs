{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Elements.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Elements.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.Elements.Lib
  ( Elements.Conf
  , calculateIssuanceEntropy, calculateAsset, calculateExplicitToken, calculateConfidentialToken
  , buildTapleafSimplicity, buildTapbranch
  , outpointHash, assetAmountHash, nonceHash, annexHash
  , Elements.Hash, Elements.Ctx8
  ) where

import qualified Simplicity.Programs.Elements as Elements

-- Maybe this ought to be Template Haskell.
calculateIssuanceEntropy = Elements.calculateIssuanceEntropy Elements.lib
calculateAsset = Elements.calculateAsset Elements.lib
calculateExplicitToken = Elements.calculateExplicitToken Elements.lib
calculateConfidentialToken = Elements.calculateConfidentialToken Elements.lib
buildTapleafSimplicity = Elements.buildTapleafSimplicity Elements.lib
buildTapbranch = Elements.buildTapbranch Elements.lib
outpointHash = Elements.outpointHash Elements.libAssert
assetAmountHash = Elements.assetAmountHash Elements.libAssert
nonceHash = Elements.nonceHash Elements.libAssert
annexHash = Elements.annexHash Elements.libAssert
