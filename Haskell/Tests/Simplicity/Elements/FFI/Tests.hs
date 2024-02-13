module Simplicity.Elements.FFI.Tests (tests) where

import Control.Arrow ((***), (+++))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Vector ((!?))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (NonNegative(..), Property, classify, forAll, testProperty)
import Lens.Family2 (under, view)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Elements.Arbitrary
import qualified Simplicity.Elements.DataTypes as Prim
import Simplicity.Elements.FFI.Jets
import Simplicity.Elements.Jets
import qualified Simplicity.Elements.Primitive as Prim
import Simplicity.Elements.Semantics
import Simplicity.Elements.TestEval
import Simplicity.FFI.Jets
import qualified Simplicity.Programs.Elements.Lib as Prog
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

toW32 :: Word.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW8 :: Word.Word8 -> Word8
toW8 = toWord8 . fromIntegral

tests :: TestTree
tests = testGroup "Elements"
        [ testGroup "Jets"
          [ testProperty "tx_is_final" prop_tx_is_final
          , testProperty "tx_lock_height" prop_tx_lock_height
          , testProperty "tx_lock_time" prop_tx_lock_time
          , testProperty "tx_lock_distance" prop_tx_lock_distance
          , testProperty "tx_lock_duration" prop_tx_lock_duration
          , testProperty "check_lock_height" prop_check_lock_height
          , testProperty "check_lock_time" prop_check_lock_time
          , testProperty "check_lock_distance" prop_check_lock_distance
          , testProperty "check_lock_duration" prop_check_lock_duration
          , testProperty "calculate_issuance_entropy" prop_calculate_issuance_entropy
          , testProperty "calculate_asset" prop_calculate_asset
          , testProperty "calculate_explicit_token" prop_calculate_explicit_token
          , testProperty "calculate_confidential_token" prop_calculate_confidential_token
          , testProperty "outpoint_hash" prop_outpoint_hash
          , testProperty "asset_amount_hash" prop_asset_amount_hash
          , testProperty "nonce_hash" prop_nonce_hash
          , testProperty "annex_hash" prop_annex_hash
          , testProperty "build_tapleaf_simplicity" prop_build_tapleaf_simplicity
          , testProperty "build_tapbranch" prop_build_tapbranch
          , testProperty "issuance" prop_issuance
          , testProperty "issuance_asset" prop_issuance_asset
          , testProperty "issuance_token" prop_issuance_token
          , testProperty "issuance_entropy" prop_issuance_entropy
          , testProperty "output_amounts_hash" prop_output_amounts_hash
          , testProperty "output_nonces_hash" prop_output_nonces_hash
          , testProperty "output_scripts_hash" prop_output_scripts_hash
          , testProperty "output_range_proofs_hash" prop_output_range_proofs_hash
          , testProperty "output_surjection_proofs_hash" prop_output_surjection_proofs_hash
          , testProperty "outputs_hash" prop_outputs_hash
          , testProperty "input_outpoints_hash" prop_input_outpoints_hash
          , testProperty "input_amounts_hash" prop_input_amounts_hash
          , testProperty "input_scripts_hash" prop_input_scripts_hash
          , testProperty "input_utxos_hash" prop_input_utxos_hash
          , testProperty "input_sequences_hash" prop_input_sequences_hash
          , testProperty "input_annexes_hash" prop_input_annexes_hash
          , testProperty "input_script_sigs_hash" prop_input_script_sigs_hash
          , testProperty "inputs_hash" prop_inputs_hash
          , testProperty "issuance_asset_amounts_hash" prop_issuance_asset_amounts_hash
          , testProperty "issuance_token_amounts_hash" prop_issuance_token_amounts_hash
          , testProperty "issuance_range_proofs_hash" prop_issuance_range_proofs_hash
          , testProperty "issuance_blinding_entropy_hash" prop_issuance_blinding_entropy_hash
          , testProperty "issuances_hash" prop_issuances_hash
          , testProperty "tx_hash" prop_tx_hash
          , testProperty "tapleaf_hash" prop_tapleaf_hash
          , testProperty "tappath_hash" prop_tappath_hash
          , testProperty "tap_env_hash" prop_tap_env_hash
          , testProperty "sig_all_hash" prop_sig_all_hash
          ]
        , testGroup "Transaction"
          [ testProperty "script_cmr" prop_script_cmr
          , testProperty "internal_key" prop_internal_key
          , testProperty "current_index" prop_current_index
          , testProperty "num_inputs" prop_num_inputs
          , testProperty "num_outputs" prop_num_outputs
          , testProperty "lock_time" prop_lock_time
          , testProperty "output_asset" prop_output_asset
          , testProperty "output_amount" prop_output_amount
          , testProperty "output_nonce" prop_output_nonce
          , testProperty "output_script_hash" prop_output_script_hash
          , testProperty "output_null_datum" prop_output_null_datum
          , testProperty "output_is_fee" prop_output_is_fee
          , testProperty "output_surjection_proof" prop_output_surjection_proof
          , testProperty "output_range_proof" prop_output_range_proof
          , testProperty "total_fee" prop_total_fee
          , testProperty "current_pegin" prop_current_pegin
          , testProperty "current_prev_outpoint" prop_current_prev_outpoint
          , testProperty "current_asset" prop_current_asset
          , testProperty "current_amount" prop_current_amount
          , testProperty "current_script_hash" prop_current_script_hash
          , testProperty "current_sequence" prop_current_sequence
          , testProperty "current_annex_hash" prop_current_annex_hash
          , testProperty "current_script_sig_hash" prop_current_script_sig_hash
          , testProperty "current_reissuance_blinding" prop_current_reissuance_blinding
          , testProperty "current_new_issuance_contract" prop_current_new_issuance_contract
          , testProperty "current_reissuance_entropy" prop_current_reissuance_entropy
          , testProperty "current_issuance_asset_amount" prop_current_issuance_asset_amount
          , testProperty "current_issuance_token_amount" prop_current_issuance_token_amount
          , testProperty "current_issuance_asset_proof" prop_current_issuance_asset_proof
          , testProperty "current_issuance_token_proof" prop_current_issuance_token_proof
          , testProperty "input_pegin" prop_input_pegin
          , testProperty "input_prev_outpoint" prop_input_prev_outpoint
          , testProperty "input_asset" prop_input_asset
          , testProperty "input_amount" prop_input_amount
          , testProperty "input_script_hash" prop_input_script_hash
          , testProperty "input_sequence" prop_input_sequence
          , testProperty "input_annex_hash" prop_input_annex_hash
          , testProperty "input_script_sig_hash" prop_input_script_sig_hash
          , testProperty "reissuance_blinding" prop_reissuance_blinding
          , testProperty "new_issuance_contract" prop_new_issuance_contract
          , testProperty "reissuance_entropy" prop_reissuance_entropy
          , testProperty "issuance_asset_amount" prop_issuance_asset_amount
          , testProperty "issuance_token_amount" prop_issuance_token_amount
          , testProperty "issuance_asset_proof" prop_issuance_asset_proof
          , testProperty "issuance_token_proof" prop_issuance_token_proof
          , testProperty "tapleaf_version" prop_tapleaf_version
          , testProperty "tappath" prop_tappath
          , testProperty "version" prop_version
          , testProperty "genesis_block_hash" prop_genesis_block_hash
          ]
        ]

prop_tx_is_final :: Property
prop_tx_is_final = forallPrimEnv $ \env -> fast_tx_is_final env () == tx_is_final env ()
 where
  fast_tx_is_final = testEval (specification (ElementsJet (TimeLockJet TxIsFinal)))

prop_tx_lock_height :: Property
prop_tx_lock_height = forallPrimEnv $ \env -> fast_tx_lock_height env () == tx_lock_height env ()
 where
  fast_tx_lock_height = testEval (specification (ElementsJet (TimeLockJet TxLockHeight)))

prop_tx_lock_time :: Property
prop_tx_lock_time = forallPrimEnv $ \env -> fast_tx_lock_time env () == tx_lock_time env ()
 where
  fast_tx_lock_time = testEval (specification (ElementsJet (TimeLockJet TxLockTime)))

prop_tx_lock_distance :: Property
prop_tx_lock_distance = forallPrimEnv $ \env -> fast_tx_lock_distance env () == tx_lock_distance env ()
 where
  fast_tx_lock_distance = testEval (specification (ElementsJet (TimeLockJet TxLockDistance)))

prop_tx_lock_duration :: Property
prop_tx_lock_duration = forallPrimEnv $ \env -> fast_tx_lock_duration env () == tx_lock_duration env ()
 where
  fast_tx_lock_duration = testEval (specification (ElementsJet (TimeLockJet TxLockDuration)))

prop_check_lock_height :: Word32 -> Property
prop_check_lock_height = \w -> forallPrimEnv $ \env -> fast_check_lock_height env w == check_lock_height env w
 where
  fast_check_lock_height = testEval (specification (ElementsJet (TimeLockJet CheckLockHeight)))

prop_check_lock_time :: Word32 -> Property
prop_check_lock_time = \w -> forallPrimEnv $ \env -> fast_check_lock_time env w == check_lock_time env w
 where
  fast_check_lock_time = testEval (specification (ElementsJet (TimeLockJet CheckLockTime)))

prop_check_lock_distance :: Word16 -> Property
prop_check_lock_distance = \w -> forallPrimEnv $ \env -> fast_check_lock_distance env w == check_lock_distance env w
 where
  fast_check_lock_distance = testEval (specification (ElementsJet (TimeLockJet CheckLockDistance)))

prop_check_lock_duration :: Word16 -> Property
prop_check_lock_duration = \w -> forallPrimEnv $ \env -> fast_check_lock_duration env w == check_lock_duration env w
 where
  fast_check_lock_duration = testEval (specification (ElementsJet (TimeLockJet CheckLockDuration)))

prop_calculate_issuance_entropy :: ((Word256, Word32), Word256) -> Bool
prop_calculate_issuance_entropy = \input ->
  calculate_issuance_entropy input == fast_calculate_issuance_entropy input
 where
  fast_calculate_issuance_entropy = testCoreEval Prog.calculateIssuanceEntropy

prop_calculate_asset :: Word256 -> Bool
prop_calculate_asset = \input ->
  calculate_asset input == fast_calculate_asset input
 where
  fast_calculate_asset = testCoreEval Prog.calculateAsset

prop_calculate_explicit_token :: Word256 -> Bool
prop_calculate_explicit_token = \input ->
  calculate_explicit_token input == fast_calculate_explicit_token input
 where
  fast_calculate_explicit_token = testCoreEval Prog.calculateExplicitToken

prop_calculate_confidential_token :: Word256 -> Bool
prop_calculate_confidential_token = \input ->
  calculate_confidential_token input == fast_calculate_confidential_token input
 where
  fast_calculate_confidential_token = testCoreEval Prog.calculateConfidentialToken

prop_outpoint_hash :: Sha256CtxElement -> (Either () Word256, (Word256, Word32)) -> Bool
prop_outpoint_hash = \ctx op ->
  let input = (ctxAsTy ctx, op)
  in outpoint_hash input == fast_outpoint_hash input
 where
  fast_outpoint_hash = testCoreEval Prog.outpointHash

prop_asset_amount_hash :: Sha256CtxElement -> Either PointElement Word256 -> Either PointElement Word64 -> Bool
prop_asset_amount_hash = \ctx cw256 cw64 ->
  let input = (ctxAsTy ctx, (cast cw256, cast cw64))
  in asset_amount_hash input == fast_asset_amount_hash input
 where
  fast_asset_amount_hash = testCoreEval Prog.assetAmountHash
  cast = either (Left . pointAsTy) Right

prop_nonce_hash :: Sha256CtxElement -> Maybe Prim.Nonce -> Bool
prop_nonce_hash = \ctx mnonce ->
  let input = (ctxAsTy ctx, cast mnonce)
  in nonce_hash input == fast_nonce_hash input
 where
  fast_nonce_hash = testCoreEval Prog.nonceHash
  cast = maybe (Left ()) (Right . ((toBit *** (toWord256 . fromIntegral)) +++ (toWord256 . integerHash256)) . Prim.nonce)

prop_annex_hash :: Sha256CtxElement -> Maybe Word256 -> Bool
prop_annex_hash = \ctx mw256 ->
  let input = (ctxAsTy ctx, cast mw256)
  in annex_hash input == fast_annex_hash input
 where
  fast_annex_hash = testCoreEval Prog.annexHash
  cast = maybe (Left ()) Right

prop_build_tapleaf_simplicity :: Word256 -> Bool
prop_build_tapleaf_simplicity = \w ->
  build_tapleaf_simplicity w == fast_build_tapleaf_simplicity w
 where
  fast_build_tapleaf_simplicity = testCoreEval Prog.buildTapleafSimplicity
   
prop_build_tapbranch :: Word256 -> Word256 -> Bool
prop_build_tapbranch = \a b ->
  build_tapbranch (a, b) == fast_build_tapbranch (a, b)
 where
  fast_build_tapbranch = testCoreEval Prog.buildTapbranch
   
prop_issuance :: Property
prop_issuance = forallInPrimEnv $ \env i ->
   fast_issuance env (toW32 i) == issuance env (toW32 i)
 where
  fast_issuance = testEval (specification (ElementsJet (IssuanceJet Issuance)))

prop_issuance_asset :: Property
prop_issuance_asset = forallInPrimEnv $ \env i ->
   fast_issuance_asset env (toW32 i) == issuance_asset env (toW32 i)
 where
  fast_issuance_asset = testEval (specification (ElementsJet (IssuanceJet IssuanceAsset)))

prop_issuance_token :: Property
prop_issuance_token = forallInPrimEnv $ \env i ->
   fast_issuance_token env (toW32 i) == issuance_token env (toW32 i)
 where
  fast_issuance_token = testEval (specification (ElementsJet (IssuanceJet IssuanceToken)))

prop_issuance_entropy :: Property
prop_issuance_entropy = forallInPrimEnv $ \env i ->
   fast_issuance_entropy env (toW32 i) == issuance_entropy env (toW32 i)
 where
  fast_issuance_entropy = testEval (specification (ElementsJet (IssuanceJet IssuanceEntropy)))

prop_output_amounts_hash :: Property
prop_output_amounts_hash = forallPrimEnv $ \env -> fast_output_amounts_hash env () == output_amounts_hash env ()
 where
  fast_output_amounts_hash = testEval (specification (ElementsJet (SigHashJet OutputAmountsHash)))

prop_output_nonces_hash :: Property
prop_output_nonces_hash = forallPrimEnv $ \env -> fast_output_nonces_hash env () == output_nonces_hash env ()
 where
  fast_output_nonces_hash = testEval (specification (ElementsJet (SigHashJet OutputNoncesHash)))

prop_output_scripts_hash :: Property
prop_output_scripts_hash = forallPrimEnv $ \env -> fast_output_scripts_hash env () == output_scripts_hash env ()
 where
  fast_output_scripts_hash = testEval (specification (ElementsJet (SigHashJet OutputScriptsHash)))

prop_output_range_proofs_hash :: Property
prop_output_range_proofs_hash = forallPrimEnv $ \env -> fast_output_range_proofs_hash env () == output_range_proofs_hash env ()
 where
  fast_output_range_proofs_hash = testEval (specification (ElementsJet (SigHashJet OutputRangeProofsHash)))

prop_output_surjection_proofs_hash :: Property
prop_output_surjection_proofs_hash = forallPrimEnv $ \env -> fast_output_surjection_proofs_hash env () == output_surjection_proofs_hash env ()
 where
  fast_output_surjection_proofs_hash = testEval (specification (ElementsJet (SigHashJet OutputSurjectionProofsHash)))

prop_outputs_hash :: Property
prop_outputs_hash = forallPrimEnv $ \env -> fast_outputs_hash env () == outputs_hash env ()
 where
  fast_outputs_hash = testEval (specification (ElementsJet (SigHashJet OutputsHash)))

prop_input_outpoints_hash :: Property
prop_input_outpoints_hash = forallPrimEnv $ \env -> fast_input_outpoints_hash env () == input_outpoints_hash env ()
 where
  fast_input_outpoints_hash = testEval (specification (ElementsJet (SigHashJet InputOutpointsHash)))

prop_input_amounts_hash :: Property
prop_input_amounts_hash = forallPrimEnv $ \env -> fast_input_amounts_hash env () == input_amounts_hash env ()
 where
  fast_input_amounts_hash = testEval (specification (ElementsJet (SigHashJet InputAmountsHash)))

prop_input_scripts_hash :: Property
prop_input_scripts_hash = forallPrimEnv $ \env -> fast_input_scripts_hash env () == input_scripts_hash env ()
 where
  fast_input_scripts_hash = testEval (specification (ElementsJet (SigHashJet InputScriptsHash)))

prop_input_utxos_hash :: Property
prop_input_utxos_hash = forallPrimEnv $ \env -> fast_input_utxos_hash env () == input_utxos_hash env ()
 where
  fast_input_utxos_hash = testEval (specification (ElementsJet (SigHashJet InputUtxosHash)))

prop_input_sequences_hash :: Property
prop_input_sequences_hash = forallPrimEnv $ \env -> fast_input_sequences_hash env () == input_sequences_hash env ()
 where
  fast_input_sequences_hash = testEval (specification (ElementsJet (SigHashJet InputSequencesHash)))

prop_input_annexes_hash :: Property
prop_input_annexes_hash = forallPrimEnv $ \env -> fast_input_annexes_hash env () == input_annexes_hash env ()
 where
  fast_input_annexes_hash = testEval (specification (ElementsJet (SigHashJet InputAnnexesHash)))

prop_input_script_sigs_hash :: Property
prop_input_script_sigs_hash = forallPrimEnv $ \env -> fast_input_script_sigs_hash env () == input_script_sigs_hash env ()
 where
  fast_input_script_sigs_hash = testEval (specification (ElementsJet (SigHashJet InputScriptSigsHash)))

prop_inputs_hash :: Property
prop_inputs_hash = forallPrimEnv $ \env -> fast_inputs_hash env () == inputs_hash env ()
 where
  fast_inputs_hash = testEval (specification (ElementsJet (SigHashJet InputsHash)))

prop_issuance_asset_amounts_hash :: Property
prop_issuance_asset_amounts_hash = forallPrimEnv $ \env -> fast_issuance_asset_amounts_hash env () == issuance_asset_amounts_hash env ()
 where
  fast_issuance_asset_amounts_hash = testEval (specification (ElementsJet (SigHashJet IssuanceAssetAmountsHash)))

prop_issuance_token_amounts_hash :: Property
prop_issuance_token_amounts_hash = forallPrimEnv $ \env -> fast_issuance_token_amounts_hash env () == issuance_token_amounts_hash env ()
 where
  fast_issuance_token_amounts_hash = testEval (specification (ElementsJet (SigHashJet IssuanceTokenAmountsHash)))

prop_issuance_range_proofs_hash :: Property
prop_issuance_range_proofs_hash = forallPrimEnv $ \env -> fast_issuance_range_proofs_hash env () == issuance_range_proofs_hash env ()
 where
  fast_issuance_range_proofs_hash = testEval (specification (ElementsJet (SigHashJet IssuanceRangeProofsHash)))

prop_issuance_blinding_entropy_hash :: Property
prop_issuance_blinding_entropy_hash = forallPrimEnv $ \env -> fast_issuance_blinding_entropy_hash env () == issuance_blinding_entropy_hash env ()
 where
  fast_issuance_blinding_entropy_hash = testEval (specification (ElementsJet (SigHashJet IssuanceBlindingEntropyHash)))

prop_issuances_hash :: Property
prop_issuances_hash = forallPrimEnv $ \env -> fast_issuances_hash env () == issuances_hash env ()
 where
  fast_issuances_hash = testEval (specification (ElementsJet (SigHashJet IssuancesHash)))

prop_tx_hash :: Property
prop_tx_hash = forallPrimEnv $ \env -> fast_tx_hash env () == tx_hash env ()
 where
  fast_tx_hash = testEval (specification (ElementsJet (SigHashJet TxHash)))

prop_tapleaf_hash :: Property
prop_tapleaf_hash = forallPrimEnv $ \env -> fast_tapleaf_hash env () == tapleaf_hash env ()
 where
  fast_tapleaf_hash = testEval (specification (ElementsJet (SigHashJet TapleafHash)))

prop_tappath_hash :: Property
prop_tappath_hash = forallPrimEnv $ \env -> fast_tappath_hash env () == tappath_hash env ()
 where
  fast_tappath_hash = testEval (specification (ElementsJet (SigHashJet TappathHash)))

prop_tap_env_hash :: Property
prop_tap_env_hash = forallPrimEnv $ \env -> fast_tap_env_hash env () == tap_env_hash env ()
 where
  fast_tap_env_hash = testEval (specification (ElementsJet (SigHashJet TapEnvHash)))

prop_sig_all_hash :: Property
prop_sig_all_hash = forallPrimEnv $ \env -> fast_sig_all_hash env () == sig_all_hash env ()
 where
  fast_sig_all_hash = testEval (specification (ElementsJet (SigHashJet SigAllHash)))

prop_script_cmr :: Property
prop_script_cmr = forallPrimEnv $ \env -> fast_script_cmr env () == script_cmr env ()
 where
  fast_script_cmr = testEval (specification (ElementsJet (TransactionJet ScriptCMR)))

prop_internal_key :: Property
prop_internal_key = forallPrimEnv $ \env -> fast_internal_key env () == internal_key env ()
 where
  fast_internal_key = testEval (specification (ElementsJet (TransactionJet InternalKey)))

prop_current_index :: Property
prop_current_index = forallPrimEnv $ \env -> fast_current_index env () == current_index env ()
 where
  fast_current_index = testEval (specification (ElementsJet (TransactionJet CurrentIndex)))

prop_num_inputs :: Property
prop_num_inputs = forallPrimEnv $ \env -> fast_num_inputs env () == num_inputs env ()
 where
  fast_num_inputs = testEval (specification (ElementsJet (TransactionJet NumInputs)))

prop_num_outputs :: Property
prop_num_outputs = forallPrimEnv $ \env -> fast_num_outputs env () == num_outputs env ()
 where
  fast_num_outputs = testEval (specification (ElementsJet (TransactionJet NumOutputs)))

prop_lock_time :: Property
prop_lock_time = forallPrimEnv $ \env -> fast_lock_time env () == lock_time env ()
 where
  fast_lock_time = testEval (specification (ElementsJet (TransactionJet LockTime)))

prop_output_asset :: Property
prop_output_asset = forallOutPrimEnv $ \env i -> fast_output_asset env (toW32 i) == output_asset env (toW32 i)
 where
  fast_output_asset = testEval (specification (ElementsJet (TransactionJet OutputAsset)))

prop_output_amount :: Property
prop_output_amount = forallOutPrimEnv $ \env i -> fast_output_amount env (toW32 i) == output_amount env (toW32 i)
 where
  fast_output_amount = testEval (specification (ElementsJet (TransactionJet OutputAmount)))

prop_output_nonce :: Property
prop_output_nonce = forallOutPrimEnv $ \env i -> fast_output_nonce env (toW32 i) == output_nonce env (toW32 i)
 where
  fast_output_nonce = testEval (specification (ElementsJet (TransactionJet OutputNonce)))

prop_output_script_hash :: Property
prop_output_script_hash = forallOutPrimEnv $ \env i -> fast_output_script_hash env (toW32 i) == output_script_hash env (toW32 i)
 where
  fast_output_script_hash = testEval (specification (ElementsJet (TransactionJet OutputScriptHash)))

prop_output_null_datum :: NonNegative Integer -> Property
prop_output_null_datum = \(NonNegative j) -> forallOutPrimEnv $ \env i -> fast_output_null_datum env (toW32 i, toWord32 j) == output_null_datum env (toW32 i, toWord32 j)
 where
  fast_output_null_datum = testEval (specification (ElementsJet (TransactionJet OutputNullDatum)))

prop_output_is_fee :: Property
prop_output_is_fee = forallOutPrimEnv $ \env i ->
  classify (isJust $ Prim.sigTxOut (Prim.envTx env) !? (fromIntegral i) >>= Prim.outputFee) "is_fee"
  $ fast_output_is_fee env (toW32 i) == output_is_fee env (toW32 i)
 where
  fast_output_is_fee = testEval (specification (ElementsJet (TransactionJet OutputIsFee)))

prop_output_surjection_proof :: Property
prop_output_surjection_proof = forallOutPrimEnv $ \env i -> fast_output_surjection_proof env (toW32 i) == output_surjection_proof env (toW32 i)
 where
  fast_output_surjection_proof = testEval (specification (ElementsJet (TransactionJet OutputSurjectionProof)))

prop_output_range_proof :: Property
prop_output_range_proof = forallOutPrimEnv $ \env i -> fast_output_range_proof env (toW32 i) == output_range_proof env (toW32 i)
 where
  fast_output_range_proof = testEval (specification (ElementsJet (TransactionJet OutputRangeProof)))

prop_total_fee :: Property
prop_total_fee = forallOutPrimEnv $ \env i -> forAll arbitraryHash256
               $ \hash -> let input = fromMaybe hash (getAssetId (Prim.sigTxOut (Prim.envTx env)) (fromIntegral i))
                              fee = Map.findWithDefault 0 input (Prim.totalFee (Prim.envTx env))
                          in classify (0 /= fee) "non-zero fee"
               $ fast_total_fee env (fromHash input) == total_fee env (fromHash input)
 where
  fast_total_fee = testEval (specification (ElementsJet (TransactionJet TotalFee)))
  getAssetId outputs ix = (outputs !? ix) >>= explicitId . view (under Prim.asset) . Prim.txoAsset
  explicitId (Prim.Explicit a) = Just a
  explicitId (Prim.Confidential _ _) = Nothing
  fromHash = toWord256 . integerHash256

prop_current_pegin :: Property
prop_current_pegin = forallPrimEnv $ \env -> fast_current_pegin env () == current_pegin env ()
 where
  fast_current_pegin = testEval (specification (ElementsJet (TransactionJet CurrentPegin)))

prop_current_prev_outpoint :: Property
prop_current_prev_outpoint = forallPrimEnv $ \env -> fast_current_prev_outpoint env () == current_prev_outpoint env ()
 where
  fast_current_prev_outpoint = testEval (specification (ElementsJet (TransactionJet CurrentPrevOutpoint)))

prop_current_asset :: Property
prop_current_asset = forallPrimEnv $ \env -> fast_current_asset env () == current_asset env ()
 where
  fast_current_asset = testEval (specification (ElementsJet (TransactionJet CurrentAsset)))

prop_current_amount :: Property
prop_current_amount = forallPrimEnv $ \env -> fast_current_amount env () == current_amount env ()
 where
  fast_current_amount = testEval (specification (ElementsJet (TransactionJet CurrentAmount)))

prop_current_script_hash :: Property
prop_current_script_hash = forallPrimEnv $ \env -> fast_current_script_hash env () == current_script_hash env ()
 where
  fast_current_script_hash = testEval (specification (ElementsJet (TransactionJet CurrentScriptHash)))

prop_current_sequence :: Property
prop_current_sequence = forallPrimEnv $ \env -> fast_current_sequence env () == current_sequence env ()
 where
  fast_current_sequence = testEval (specification (ElementsJet (TransactionJet CurrentSequence)))

prop_current_annex_hash :: Property
prop_current_annex_hash = forallPrimEnv $ \env -> fast_current_annex_hash env () == current_annex_hash env ()
 where
  fast_current_annex_hash = testEval (specification (ElementsJet (TransactionJet CurrentAnnexHash)))

prop_current_script_sig_hash :: Property
prop_current_script_sig_hash = forallPrimEnv $ \env -> fast_current_script_sig_hash env () == current_script_sig_hash env ()
 where
  fast_current_script_sig_hash = testEval (specification (ElementsJet (TransactionJet CurrentScriptSigHash)))

prop_current_reissuance_blinding :: Property
prop_current_reissuance_blinding = forallPrimEnv $ \env -> fast_current_reissuance_blinding env () == current_reissuance_blinding env ()
 where
  fast_current_reissuance_blinding = testEval (specification (ElementsJet (TransactionJet CurrentReissuanceBlinding)))

prop_current_new_issuance_contract :: Property
prop_current_new_issuance_contract = forallPrimEnv $ \env -> fast_current_new_issuance_contract env () == current_new_issuance_contract env ()
 where
  fast_current_new_issuance_contract = testEval (specification (ElementsJet (TransactionJet CurrentNewIssuanceContract)))

prop_current_reissuance_entropy :: Property
prop_current_reissuance_entropy = forallPrimEnv $ \env -> fast_current_reissuance_entropy env () == current_reissuance_entropy env ()
 where
  fast_current_reissuance_entropy = testEval (specification (ElementsJet (TransactionJet CurrentReissuanceEntropy)))

prop_current_issuance_asset_amount :: Property
prop_current_issuance_asset_amount = forallPrimEnv $ \env -> fast_current_issuance_asset_amount env () == current_issuance_asset_amount env ()
 where
  fast_current_issuance_asset_amount = testEval (specification (ElementsJet (TransactionJet CurrentIssuanceAssetAmount)))

prop_current_issuance_token_amount :: Property
prop_current_issuance_token_amount = forallPrimEnv $ \env -> fast_current_issuance_token_amount env () == current_issuance_token_amount env ()
 where
  fast_current_issuance_token_amount = testEval (specification (ElementsJet (TransactionJet CurrentIssuanceTokenAmount)))

prop_current_issuance_asset_proof :: Property
prop_current_issuance_asset_proof = forallPrimEnv $ \env -> fast_current_issuance_asset_proof env () == current_issuance_asset_proof env ()
 where
  fast_current_issuance_asset_proof = testEval (specification (ElementsJet (TransactionJet CurrentIssuanceAssetProof)))

prop_current_issuance_token_proof :: Property
prop_current_issuance_token_proof = forallPrimEnv $ \env -> fast_current_issuance_token_proof env () == current_issuance_token_proof env ()
 where
  fast_current_issuance_token_proof = testEval (specification (ElementsJet (TransactionJet CurrentIssuanceTokenProof)))

prop_input_pegin :: Property
prop_input_pegin = forallInPrimEnv $ \env i -> fast_input_pegin env (toW32 i) == input_pegin env (toW32 i)
 where
  fast_input_pegin = testEval (specification (ElementsJet (TransactionJet InputPegin)))

prop_input_prev_outpoint :: Property
prop_input_prev_outpoint = forallInPrimEnv $ \env i -> fast_input_prev_outpoint env (toW32 i) == input_prev_outpoint env (toW32 i)
 where
  fast_input_prev_outpoint = testEval (specification (ElementsJet (TransactionJet InputPrevOutpoint)))

prop_input_asset :: Property
prop_input_asset = forallInPrimEnv $ \env i -> fast_input_asset env (toW32 i) == input_asset env (toW32 i)
 where
  fast_input_asset = testEval (specification (ElementsJet (TransactionJet InputAsset)))

prop_input_amount :: Property
prop_input_amount = forallInPrimEnv $ \env i -> fast_input_amount env (toW32 i) == input_amount env (toW32 i)
 where
  fast_input_amount = testEval (specification (ElementsJet (TransactionJet InputAmount)))

prop_input_script_hash :: Property
prop_input_script_hash = forallInPrimEnv $ \env i -> fast_input_script_hash env (toW32 i) == input_script_hash env (toW32 i)
 where
  fast_input_script_hash = testEval (specification (ElementsJet (TransactionJet InputScriptHash)))

prop_input_sequence :: Property
prop_input_sequence = forallInPrimEnv $ \env i -> fast_input_sequence env (toW32 i) == input_sequence env (toW32 i)
 where
  fast_input_sequence = testEval (specification (ElementsJet (TransactionJet InputSequence)))

prop_input_annex_hash :: Property
prop_input_annex_hash = forallInPrimEnv $ \env i -> fast_input_annex_hash env (toW32 i) == input_annex_hash env (toW32 i)
 where
  fast_input_annex_hash = testEval (specification (ElementsJet (TransactionJet InputAnnexHash)))

prop_input_script_sig_hash :: Property
prop_input_script_sig_hash = forallInPrimEnv $ \env i -> fast_input_script_sig_hash env (toW32 i) == input_script_sig_hash env (toW32 i)
 where
  fast_input_script_sig_hash = testEval (specification (ElementsJet (TransactionJet InputScriptSigHash)))

prop_reissuance_blinding :: Property
prop_reissuance_blinding = forallInPrimEnv $ \env i -> fast_reissuance_blinding env (toW32 i) == reissuance_blinding env (toW32 i)
 where
  fast_reissuance_blinding = testEval (specification (ElementsJet (TransactionJet ReissuanceBlinding)))

prop_new_issuance_contract :: Property
prop_new_issuance_contract = forallInPrimEnv $ \env i -> fast_new_issuance_contract env (toW32 i) == new_issuance_contract env (toW32 i)
 where
  fast_new_issuance_contract = testEval (specification (ElementsJet (TransactionJet NewIssuanceContract)))

prop_reissuance_entropy :: Property
prop_reissuance_entropy = forallInPrimEnv $ \env i -> fast_reissuance_entropy env (toW32 i) == reissuance_entropy env (toW32 i)
 where
  fast_reissuance_entropy = testEval (specification (ElementsJet (TransactionJet ReissuanceEntropy)))

prop_issuance_asset_amount :: Property
prop_issuance_asset_amount = forallInPrimEnv $ \env i -> fast_issuance_asset_amount env (toW32 i) == issuance_asset_amount env (toW32 i)
 where
  fast_issuance_asset_amount = testEval (specification (ElementsJet (TransactionJet IssuanceAssetAmount)))

prop_issuance_token_amount :: Property
prop_issuance_token_amount = forallInPrimEnv $ \env i -> fast_issuance_token_amount env (toW32 i) == issuance_token_amount env (toW32 i)
 where
  fast_issuance_token_amount = testEval (specification (ElementsJet (TransactionJet IssuanceTokenAmount)))

prop_issuance_asset_proof :: Property
prop_issuance_asset_proof = forallInPrimEnv $ \env i -> fast_issuance_asset_proof env (toW32 i) == issuance_asset_proof env (toW32 i)
 where
  fast_issuance_asset_proof = testEval (specification (ElementsJet (TransactionJet IssuanceAssetProof)))

prop_issuance_token_proof :: Property
prop_issuance_token_proof = forallInPrimEnv $ \env i -> fast_issuance_token_proof env (toW32 i) == issuance_token_proof env (toW32 i)
 where
  fast_issuance_token_proof = testEval (specification (ElementsJet (TransactionJet IssuanceTokenProof)))

prop_tapleaf_version :: Property
prop_tapleaf_version = forallPrimEnv $ \env -> fast_tapleaf_version env () == tapleaf_version env ()
 where
  fast_tapleaf_version = testEval (specification (ElementsJet (TransactionJet TapleafVersion)))

prop_tappath :: Property
prop_tappath = forallPrimEnv $ \env -> forAll (genTappathIx env) $ \i -> fast_tappath env (toW8 i) == tappath env (toW8 i)
 where
  fast_tappath = testEval (specification (ElementsJet (TransactionJet Tappath)))
  genTappathIx = genBoundaryCases . fromIntegral . length . Prim.tappath . Prim.envTap

prop_version :: Property
prop_version = forallPrimEnv $ \env -> fast_version env () == version env ()
 where
  fast_version = testEval (specification (ElementsJet (TransactionJet Version)))

prop_genesis_block_hash :: Property
prop_genesis_block_hash = forallPrimEnv $ \env -> fast_genesis_block_hash env () == genesis_block_hash env ()
 where
  fast_genesis_block_hash = testEval (specification (ElementsJet (TransactionJet GenesisBlockHash)))
