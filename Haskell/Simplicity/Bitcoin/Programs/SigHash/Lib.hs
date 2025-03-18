{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Bitcoin.Programs.SigHash.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Bitcoin.Programs.SigHash.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Bitcoin.Programs.SigHash.Lib
 ( outputValuesHash, outputScriptsHash
 , outputsHash, outputHash
 , inputValuesHash, inputScriptsHash, inputUtxosHash, inputUtxoHash
 , inputOutpointsHash, inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash, inputHash
 , txHash
 , tapleafHash, tappathHash, tapEnvHash
 , sigAllHash
 ) where

import qualified Simplicity.Bitcoin.Programs.SigHash as SigHash

outputValuesHash = SigHash.outputValuesHash SigHash.lib
outputScriptsHash = SigHash.outputScriptsHash SigHash.lib
outputsHash = SigHash.outputsHash SigHash.lib
outputHash = SigHash.outputHash SigHash.lib
inputValuesHash = SigHash.inputValuesHash SigHash.lib
inputScriptsHash = SigHash.inputScriptsHash SigHash.lib
inputUtxosHash = SigHash.inputUtxosHash SigHash.lib
inputUtxoHash = SigHash.inputUtxoHash SigHash.lib
inputOutpointsHash = SigHash.inputOutpointsHash SigHash.lib
inputSequencesHash = SigHash.inputSequencesHash SigHash.lib
inputAnnexesHash = SigHash.inputAnnexesHash SigHash.lib
inputsHash = SigHash.inputsHash SigHash.lib
inputHash = SigHash.inputHash SigHash.lib
inputScriptSigsHash = SigHash.inputScriptSigsHash SigHash.lib
txHash = SigHash.txHash SigHash.lib
tapleafHash = SigHash.tapleafHash SigHash.lib
tappathHash = SigHash.tappathHash SigHash.lib
tapEnvHash = SigHash.tapEnvHash SigHash.lib
sigAllHash = SigHash.sigAllHash SigHash.lib
