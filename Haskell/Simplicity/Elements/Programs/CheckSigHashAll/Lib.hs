{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Elements.Programs.CheckSigHashAll.libCore' and 'Simplicity.Elements.Programs.CheckSigHashAll.libAssert' library instances into individual functions.
-- Users should prefer to use 'Simplicity.Elements.Programs.CheckSigHashAll.mkLibCore' and 'Simplicity.Elements.Programs.CheckSigHashAll.mkLibAssert' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Elements.Programs.CheckSigHashAll.Lib
  (
  -- * Operations
    sigAllCMR
  , sigHashAll
  , checkSigHashAll
  , wCheckSigHashAll
  , pkwCheckSigHashAll
  -- * Types
  , CheckSigHashAll.Hash, CheckSigHashAll.PubKey, CheckSigHashAll.Sig
  ) where

import Simplicity.Tensor
import qualified Simplicity.Elements.Programs.CheckSigHashAll as CheckSigHashAll

sigAllCMR = CheckSigHashAll.sigAllCMR (CheckSigHashAll.lib :: CheckSigHashAll.Lib Unit)
sigHashAll = CheckSigHashAll.sigHashAll CheckSigHashAll.lib
checkSigHashAll = CheckSigHashAll.checkSigHashAll CheckSigHashAll.lib
wCheckSigHashAll = CheckSigHashAll.wCheckSigHashAll CheckSigHashAll.lib
pkwCheckSigHashAll = CheckSigHashAll.pkwCheckSigHashAll CheckSigHashAll.lib
