{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module instantiates the "Simplicity.Programs.CheckSig" module functions.
-- Users should prefer to use "Simplicity.Programs.CheckSig" module in order to share library dependencies.
module Simplicity.Programs.CheckSig.Lib
 ( sigHash'
 , checkSigVerify , checkSigVerify'
 -- * Types
 , CheckSig.Hash
 ) where

import qualified Simplicity.Programs.CheckSig as CheckSig
import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Ty.Word

sigHash' = CheckSig.sigHash' Sha256.lib
checkSigVerify = CheckSig.checkSigVerify Sha256.lib LibSecp256k1.lib
checkSigVerify' = CheckSig.checkSigVerify' Sha256.lib LibSecp256k1.lib
