{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Elements.Programs.SigHash.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Elements.Programs.SigHash.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Elements.Programs.SigHash.Lib
 ( outputAmountsHash, outputNoncesHash, outputScriptsHash
 , outputRangeProofsHash, outputSurjectionProofsHash, outputsHash
 , inputAmountsHash, inputScriptsHash, inputUtxosHash
 , inputOutpointsHash, inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash
 , issuanceAssetAmountsHash, issuanceTokenAmountsHash, issuanceRangeProofsHash, issuanceBlindingEntropyHash, issuancesHash
 , txHash
 , tapleafHash, tappathHash, tapEnvHash
 , sigAllHash
 ) where

import qualified Simplicity.Elements.Programs.SigHash as SigHash

outputAmountsHash = SigHash.outputAmountsHash SigHash.lib
outputNoncesHash = SigHash.outputNoncesHash SigHash.lib
outputScriptsHash = SigHash.outputScriptsHash SigHash.lib
outputRangeProofsHash = SigHash.outputRangeProofsHash SigHash.lib
outputSurjectionProofsHash = SigHash.outputSurjectionProofsHash SigHash.lib
outputsHash = SigHash.outputsHash SigHash.lib
inputAmountsHash = SigHash.inputAmountsHash SigHash.lib
inputScriptsHash = SigHash.inputScriptsHash SigHash.lib
inputUtxosHash = SigHash.inputUtxosHash SigHash.lib
inputOutpointsHash = SigHash.inputOutpointsHash SigHash.lib
inputSequencesHash = SigHash.inputSequencesHash SigHash.lib
inputAnnexesHash = SigHash.inputAnnexesHash SigHash.lib
inputsHash = SigHash.inputsHash SigHash.lib
issuanceAssetAmountsHash = SigHash.issuanceAssetAmountsHash SigHash.lib
issuanceTokenAmountsHash = SigHash.issuanceTokenAmountsHash SigHash.lib
issuanceRangeProofsHash = SigHash.issuanceRangeProofsHash SigHash.lib
issuanceBlindingEntropyHash = SigHash.issuanceBlindingEntropyHash SigHash.lib
issuancesHash = SigHash.issuancesHash SigHash.lib
inputScriptSigsHash = SigHash.inputScriptSigsHash SigHash.lib
txHash = SigHash.txHash SigHash.lib
tapleafHash = SigHash.tapleafHash SigHash.lib
tappathHash = SigHash.tappathHash SigHash.lib
tapEnvHash = SigHash.tapEnvHash SigHash.lib
sigAllHash = SigHash.sigAllHash SigHash.lib
