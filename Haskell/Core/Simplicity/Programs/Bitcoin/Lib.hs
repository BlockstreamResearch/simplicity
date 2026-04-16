{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Bitcoin.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Bitcoin.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.Bitcoin.Lib
  ( buildTapleafSimplicity, buildTapbranch
  , outpointHash, annexHash
  , buildTaptweak
  , Bitcoin.Hash, Bitcoin.Ctx8
  ) where

import qualified Simplicity.Programs.Bitcoin as Bitcoin

-- Maybe this ought to be Template Haskell.
buildTapleafSimplicity = Bitcoin.buildTapleafSimplicity Bitcoin.lib
buildTapbranch = Bitcoin.buildTapbranch Bitcoin.lib
outpointHash = Bitcoin.outpointHash Bitcoin.libAssert
annexHash = Bitcoin.annexHash Bitcoin.libAssert
buildTaptweak = Bitcoin.buildTaptweak Bitcoin.libAssert
