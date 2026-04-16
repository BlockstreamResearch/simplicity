module Simplicity.Bitcoin.FFI.Tests (tests) where

import Control.Arrow ((***), (+++))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Vector ((!?))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, (@?=), testCase)
import Test.Tasty.QuickCheck (NonNegative(..), Property, classify, forAll, testProperty)
import Lens.Family2 (under, view)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Bitcoin.Arbitrary
import qualified Simplicity.Bitcoin.DataTypes as Prim
import Simplicity.Bitcoin.FFI.Jets
import Simplicity.Bitcoin.Jets
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.Semantics
import Simplicity.Bitcoin.TestEval
import Simplicity.FFI.Jets
import qualified Simplicity.Programs.Bitcoin.Lib as Prog
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

toW32 :: Word.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW8 :: Word.Word8 -> Word8
toW8 = toWord8 . fromIntegral

tests :: TestTree
tests = testGroup "Bitcoin"
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
          , testProperty "outpoint_hash" prop_outpoint_hash
          , testProperty "annex_hash" prop_annex_hash
          , testProperty "build_tapleaf_simplicity" prop_build_tapleaf_simplicity
          , testProperty "build_tapbranch" prop_build_tapbranch
          , testProperty "build_taptweak" prop_build_taptweak
          , testProperty "output_values_hash" prop_output_values_hash
          , testProperty "output_scripts_hash" prop_output_scripts_hash
          , testProperty "outputs_hash" prop_outputs_hash
          , testProperty "output_hash" prop_output_hash
          , testProperty "input_outpoints_hash" prop_input_outpoints_hash
          , testProperty "input_values_hash" prop_input_values_hash
          , testProperty "input_scripts_hash" prop_input_scripts_hash
          , testProperty "input_utxos_hash" prop_input_utxos_hash
          , testProperty "input_utxo_hash" prop_input_utxo_hash
          , testProperty "input_sequences_hash" prop_input_sequences_hash
          , testProperty "input_annexes_hash" prop_input_annexes_hash
          , testProperty "input_script_sigs_hash" prop_input_script_sigs_hash
          , testProperty "inputs_hash" prop_inputs_hash
          , testProperty "input_hash" prop_input_hash
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
          , testProperty "output_value" prop_output_value
          , testProperty "output_script_hash" prop_output_script_hash
          , testProperty "total_output_value" prop_total_output_value
          , testProperty "current_prev_outpoint" prop_current_prev_outpoint
          , testProperty "current_value" prop_current_value
          , testProperty "current_script_hash" prop_current_script_hash
          , testProperty "current_sequence" prop_current_sequence
          , testProperty "current_annex_hash" prop_current_annex_hash
          , testProperty "current_script_sig_hash" prop_current_script_sig_hash
          , testProperty "input_prev_outpoint" prop_input_prev_outpoint
          , testProperty "input_value" prop_input_value
          , testProperty "input_script_hash" prop_input_script_hash
          , testProperty "input_sequence" prop_input_sequence
          , testProperty "input_annex_hash" prop_input_annex_hash
          , testProperty "input_script_sig_hash" prop_input_script_sig_hash
          , testProperty "total_input_value" prop_total_input_value
          , testProperty "fee" prop_fee
          , testProperty "tapleaf_version" prop_tapleaf_version
          , testProperty "tappath" prop_tappath
          , testProperty "version" prop_version
          , testProperty "transaction_id" prop_transaction_id
          ]
        ]

prop_tx_is_final :: Property
prop_tx_is_final = forallPrimEnv $ \env -> fast_tx_is_final env () == tx_is_final env ()
 where
  fast_tx_is_final = testEval (specification (BitcoinJet (TimeLockJet TxIsFinal)))

prop_tx_lock_height :: Property
prop_tx_lock_height = forallPrimEnv $ \env -> fast_tx_lock_height env () == tx_lock_height env ()
 where
  fast_tx_lock_height = testEval (specification (BitcoinJet (TimeLockJet TxLockHeight)))

prop_tx_lock_time :: Property
prop_tx_lock_time = forallPrimEnv $ \env -> fast_tx_lock_time env () == tx_lock_time env ()
 where
  fast_tx_lock_time = testEval (specification (BitcoinJet (TimeLockJet TxLockTime)))

prop_tx_lock_distance :: Property
prop_tx_lock_distance = forallPrimEnv $ \env -> fast_tx_lock_distance env () == tx_lock_distance env ()
 where
  fast_tx_lock_distance = testEval (specification (BitcoinJet (TimeLockJet TxLockDistance)))

prop_tx_lock_duration :: Property
prop_tx_lock_duration = forallPrimEnv $ \env -> fast_tx_lock_duration env () == tx_lock_duration env ()
 where
  fast_tx_lock_duration = testEval (specification (BitcoinJet (TimeLockJet TxLockDuration)))

prop_check_lock_height :: Word32 -> Property
prop_check_lock_height = \w -> forallPrimEnv $ \env -> fast_check_lock_height env w == check_lock_height env w
 where
  fast_check_lock_height = testEval (specification (BitcoinJet (TimeLockJet CheckLockHeight)))

prop_check_lock_time :: Word32 -> Property
prop_check_lock_time = \w -> forallPrimEnv $ \env -> fast_check_lock_time env w == check_lock_time env w
 where
  fast_check_lock_time = testEval (specification (BitcoinJet (TimeLockJet CheckLockTime)))

prop_check_lock_distance :: Word16 -> Property
prop_check_lock_distance = \w -> forallPrimEnv $ \env -> fast_check_lock_distance env w == check_lock_distance env w
 where
  fast_check_lock_distance = testEval (specification (BitcoinJet (TimeLockJet CheckLockDistance)))

prop_check_lock_duration :: Word16 -> Property
prop_check_lock_duration = \w -> forallPrimEnv $ \env -> fast_check_lock_duration env w == check_lock_duration env w
 where
  fast_check_lock_duration = testEval (specification (BitcoinJet (TimeLockJet CheckLockDuration)))

prop_outpoint_hash :: Sha256CtxElement -> (Word256, Word32) -> Bool
prop_outpoint_hash = \ctx op ->
  let input = (ctxAsTy ctx, op)
  in outpoint_hash input == fast_outpoint_hash input
 where
  fast_outpoint_hash = testCoreEval Prog.outpointHash

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

prop_build_taptweak :: FieldElement -> Word256 -> Bool
prop_build_taptweak = \a b ->
  let input = (feAsTy a, b) in
  build_taptweak input == fast_build_taptweak input
 where
  fast_build_taptweak = testCoreEval Prog.buildTaptweak

prop_output_values_hash :: Property
prop_output_values_hash = forallPrimEnv $ \env -> fast_output_values_hash env () == output_values_hash env ()
 where
  fast_output_values_hash = testEval (specification (BitcoinJet (SigHashJet OutputValuesHash)))

prop_output_scripts_hash :: Property
prop_output_scripts_hash = forallPrimEnv $ \env -> fast_output_scripts_hash env () == output_scripts_hash env ()
 where
  fast_output_scripts_hash = testEval (specification (BitcoinJet (SigHashJet OutputScriptsHash)))

prop_outputs_hash :: Property
prop_outputs_hash = forallPrimEnv $ \env -> fast_outputs_hash env () == outputs_hash env ()
 where
  fast_outputs_hash = testEval (specification (BitcoinJet (SigHashJet OutputsHash)))

prop_output_hash :: Property
prop_output_hash = forallOutPrimEnv $ \env i -> fast_output_hash env (toW32 i) == output_hash env (toW32 i)
 where
  fast_output_hash = testEval (specification (BitcoinJet (SigHashJet OutputHash)))

prop_input_outpoints_hash :: Property
prop_input_outpoints_hash = forallPrimEnv $ \env -> fast_input_outpoints_hash env () == input_outpoints_hash env ()
 where
  fast_input_outpoints_hash = testEval (specification (BitcoinJet (SigHashJet InputOutpointsHash)))

prop_input_values_hash :: Property
prop_input_values_hash = forallPrimEnv $ \env -> fast_input_values_hash env () == input_values_hash env ()
 where
  fast_input_values_hash = testEval (specification (BitcoinJet (SigHashJet InputValuesHash)))

prop_input_scripts_hash :: Property
prop_input_scripts_hash = forallPrimEnv $ \env -> fast_input_scripts_hash env () == input_scripts_hash env ()
 where
  fast_input_scripts_hash = testEval (specification (BitcoinJet (SigHashJet InputScriptsHash)))

prop_input_utxos_hash :: Property
prop_input_utxos_hash = forallPrimEnv $ \env -> fast_input_utxos_hash env () == input_utxos_hash env ()
 where
  fast_input_utxos_hash = testEval (specification (BitcoinJet (SigHashJet InputUtxosHash)))

prop_input_utxo_hash :: Property
prop_input_utxo_hash = forallInPrimEnv $ \env i -> fast_input_utxo_hash env (toW32 i) == input_utxo_hash env (toW32 i)
 where
  fast_input_utxo_hash = testEval (specification (BitcoinJet (SigHashJet InputUtxoHash)))

prop_input_sequences_hash :: Property
prop_input_sequences_hash = forallPrimEnv $ \env -> fast_input_sequences_hash env () == input_sequences_hash env ()
 where
  fast_input_sequences_hash = testEval (specification (BitcoinJet (SigHashJet InputSequencesHash)))

prop_input_annexes_hash :: Property
prop_input_annexes_hash = forallPrimEnv $ \env -> fast_input_annexes_hash env () == input_annexes_hash env ()
 where
  fast_input_annexes_hash = testEval (specification (BitcoinJet (SigHashJet InputAnnexesHash)))

prop_input_script_sigs_hash :: Property
prop_input_script_sigs_hash = forallPrimEnv $ \env -> fast_input_script_sigs_hash env () == input_script_sigs_hash env ()
 where
  fast_input_script_sigs_hash = testEval (specification (BitcoinJet (SigHashJet InputScriptSigsHash)))

prop_inputs_hash :: Property
prop_inputs_hash = forallPrimEnv $ \env -> fast_inputs_hash env () == inputs_hash env ()
 where
  fast_inputs_hash = testEval (specification (BitcoinJet (SigHashJet InputsHash)))

prop_input_hash :: Property
prop_input_hash = forallInPrimEnv $ \env i -> fast_input_hash env (toW32 i) == input_hash env (toW32 i)
 where
  fast_input_hash = testEval (specification (BitcoinJet (SigHashJet InputHash)))

prop_tx_hash :: Property
prop_tx_hash = forallPrimEnv $ \env -> fast_tx_hash env () == tx_hash env ()
 where
  fast_tx_hash = testEval (specification (BitcoinJet (SigHashJet TxHash)))

prop_tapleaf_hash :: Property
prop_tapleaf_hash = forallPrimEnv $ \env -> fast_tapleaf_hash env () == tapleaf_hash env ()
 where
  fast_tapleaf_hash = testEval (specification (BitcoinJet (SigHashJet TapleafHash)))

prop_tappath_hash :: Property
prop_tappath_hash = forallPrimEnv $ \env -> fast_tappath_hash env () == tappath_hash env ()
 where
  fast_tappath_hash = testEval (specification (BitcoinJet (SigHashJet TappathHash)))

prop_tap_env_hash :: Property
prop_tap_env_hash = forallPrimEnv $ \env -> fast_tap_env_hash env () == tap_env_hash env ()
 where
  fast_tap_env_hash = testEval (specification (BitcoinJet (SigHashJet TapEnvHash)))

prop_sig_all_hash :: Property
prop_sig_all_hash = forallPrimEnv $ \env -> fast_sig_all_hash env () == sig_all_hash env ()
 where
  fast_sig_all_hash = testEval (specification (BitcoinJet (SigHashJet SigAllHash)))

prop_script_cmr :: Property
prop_script_cmr = forallPrimEnv $ \env -> fast_script_cmr env () == script_cmr env ()
 where
  fast_script_cmr = testEval (specification (BitcoinJet (TransactionJet ScriptCMR)))

prop_internal_key :: Property
prop_internal_key = forallPrimEnv $ \env -> fast_internal_key env () == internal_key env ()
 where
  fast_internal_key = testEval (specification (BitcoinJet (TransactionJet InternalKey)))

prop_current_index :: Property
prop_current_index = forallPrimEnv $ \env -> fast_current_index env () == current_index env ()
 where
  fast_current_index = testEval (specification (BitcoinJet (TransactionJet CurrentIndex)))

prop_num_inputs :: Property
prop_num_inputs = forallPrimEnv $ \env -> fast_num_inputs env () == num_inputs env ()
 where
  fast_num_inputs = testEval (specification (BitcoinJet (TransactionJet NumInputs)))

prop_num_outputs :: Property
prop_num_outputs = forallPrimEnv $ \env -> fast_num_outputs env () == num_outputs env ()
 where
  fast_num_outputs = testEval (specification (BitcoinJet (TransactionJet NumOutputs)))

prop_lock_time :: Property
prop_lock_time = forallPrimEnv $ \env -> fast_lock_time env () == lock_time env ()
 where
  fast_lock_time = testEval (specification (BitcoinJet (TransactionJet LockTime)))

prop_output_value :: Property
prop_output_value = forallOutPrimEnv $ \env i -> fast_output_value env (toW32 i) == output_value env (toW32 i)
 where
  fast_output_value = testEval (specification (BitcoinJet (TransactionJet OutputValue)))

prop_output_script_hash :: Property
prop_output_script_hash = forallOutPrimEnv $ \env i -> fast_output_script_hash env (toW32 i) == output_script_hash env (toW32 i)
 where
  fast_output_script_hash = testEval (specification (BitcoinJet (TransactionJet OutputScriptHash)))

prop_total_output_value :: Property
prop_total_output_value = forallPrimEnv $ \env -> fast_total_output_value env () == total_output_value env ()
 where
  fast_total_output_value = testEval (specification (BitcoinJet (TransactionJet TotalOutputValue)))

prop_current_prev_outpoint :: Property
prop_current_prev_outpoint = forallPrimEnv $ \env -> fast_current_prev_outpoint env () == current_prev_outpoint env ()
 where
  fast_current_prev_outpoint = testEval (specification (BitcoinJet (TransactionJet CurrentPrevOutpoint)))

prop_current_value :: Property
prop_current_value = forallPrimEnv $ \env -> fast_current_value env () == current_value env ()
 where
  fast_current_value = testEval (specification (BitcoinJet (TransactionJet CurrentValue)))

prop_current_script_hash :: Property
prop_current_script_hash = forallPrimEnv $ \env -> fast_current_script_hash env () == current_script_hash env ()
 where
  fast_current_script_hash = testEval (specification (BitcoinJet (TransactionJet CurrentScriptHash)))

prop_current_sequence :: Property
prop_current_sequence = forallPrimEnv $ \env -> fast_current_sequence env () == current_sequence env ()
 where
  fast_current_sequence = testEval (specification (BitcoinJet (TransactionJet CurrentSequence)))

prop_current_annex_hash :: Property
prop_current_annex_hash = forallPrimEnv $ \env -> fast_current_annex_hash env () == current_annex_hash env ()
 where
  fast_current_annex_hash = testEval (specification (BitcoinJet (TransactionJet CurrentAnnexHash)))

prop_current_script_sig_hash :: Property
prop_current_script_sig_hash = forallPrimEnv $ \env -> fast_current_script_sig_hash env () == current_script_sig_hash env ()
 where
  fast_current_script_sig_hash = testEval (specification (BitcoinJet (TransactionJet CurrentScriptSigHash)))

prop_input_prev_outpoint :: Property
prop_input_prev_outpoint = forallInPrimEnv $ \env i -> fast_input_prev_outpoint env (toW32 i) == input_prev_outpoint env (toW32 i)
 where
  fast_input_prev_outpoint = testEval (specification (BitcoinJet (TransactionJet InputPrevOutpoint)))

prop_input_value :: Property
prop_input_value = forallInPrimEnv $ \env i -> fast_input_value env (toW32 i) == input_value env (toW32 i)
 where
  fast_input_value = testEval (specification (BitcoinJet (TransactionJet InputValue)))

prop_input_script_hash :: Property
prop_input_script_hash = forallInPrimEnv $ \env i -> fast_input_script_hash env (toW32 i) == input_script_hash env (toW32 i)
 where
  fast_input_script_hash = testEval (specification (BitcoinJet (TransactionJet InputScriptHash)))

prop_input_sequence :: Property
prop_input_sequence = forallInPrimEnv $ \env i -> fast_input_sequence env (toW32 i) == input_sequence env (toW32 i)
 where
  fast_input_sequence = testEval (specification (BitcoinJet (TransactionJet InputSequence)))

prop_input_annex_hash :: Property
prop_input_annex_hash = forallInPrimEnv $ \env i -> fast_input_annex_hash env (toW32 i) == input_annex_hash env (toW32 i)
 where
  fast_input_annex_hash = testEval (specification (BitcoinJet (TransactionJet InputAnnexHash)))

prop_input_script_sig_hash :: Property
prop_input_script_sig_hash = forallInPrimEnv $ \env i -> fast_input_script_sig_hash env (toW32 i) == input_script_sig_hash env (toW32 i)
 where
  fast_input_script_sig_hash = testEval (specification (BitcoinJet (TransactionJet InputScriptSigHash)))

prop_total_input_value :: Property
prop_total_input_value = forallPrimEnv $ \env -> fast_total_input_value env () == total_input_value env ()
 where
  fast_total_input_value = testEval (specification (BitcoinJet (TransactionJet TotalInputValue)))

prop_fee :: Property
prop_fee = forallPrimEnv $ \env -> fast_fee env () == fee env ()
 where
  fast_fee = testEval (specification (BitcoinJet (TransactionJet Fee)))

prop_tapleaf_version :: Property
prop_tapleaf_version = forallPrimEnv $ \env -> fast_tapleaf_version env () == tapleaf_version env ()
 where
  fast_tapleaf_version = testEval (specification (BitcoinJet (TransactionJet TapleafVersion)))

prop_tappath :: Property
prop_tappath = forallPrimEnv $ \env -> forAll (genTappathIx env) $ \i -> fast_tappath env (toW8 i) == tappath env (toW8 i)
 where
  fast_tappath = testEval (specification (BitcoinJet (TransactionJet Tappath)))
  genTappathIx = genBoundaryCases . fromIntegral . length . Prim.tappath . Prim.envTap

prop_version :: Property
prop_version = forallPrimEnv $ \env -> fast_version env () == version env ()
 where
  fast_version = testEval (specification (BitcoinJet (TransactionJet Version)))

prop_transaction_id :: Property
prop_transaction_id = forallPrimEnv $ \env -> fast_transaction_id env () == transaction_id env ()
 where
  fast_transaction_id = testEval (specification (BitcoinJet (TransactionJet TransactionId)))
