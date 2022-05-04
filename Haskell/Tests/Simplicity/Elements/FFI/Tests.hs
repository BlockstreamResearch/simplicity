module Simplicity.Elements.FFI.Tests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (NonNegative(..), Property, forAll, testProperty)

import Simplicity.Arbitrary
import Simplicity.Elements.Arbitrary
import Simplicity.Elements.DataTypes
import Simplicity.Elements.FFI.Jets
import Simplicity.Elements.Jets
import Simplicity.Elements.Primitive
import Simplicity.Elements.Semantics
import Simplicity.Elements.TestEval
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

toW32 :: Word.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW8 :: Word.Word8 -> Word8
toW8 = toWord8 . fromIntegral

tests :: TestTree
tests = testGroup "Elements"
        [ testGroup "Primitives"
          [ testProperty "version" prop_version
          , testProperty "lock_time" prop_lock_time
          , testProperty "inputs_hash" prop_inputs_hash
          , testProperty "outputs_hash" prop_outputs_hash
          , testProperty "num_inputs" prop_num_inputs
          , testProperty "input_is_pegin" prop_input_is_pegin
          , testProperty "input_prev_outpoint" prop_input_prev_outpoint
          , testProperty "input_asset" prop_input_asset
          , testProperty "input_amount" prop_input_amount
          , testProperty "input_script_hash" prop_input_script_hash
          , testProperty "input_sequence" prop_input_sequence
          , testProperty "input_issuance_blinding" prop_input_issuance_blinding
          , testProperty "input_issuance_contract" prop_input_issuance_contract
          , testProperty "input_issuance_entropy" prop_input_issuance_entropy
          , testProperty "input_issuance_asset_amt" prop_input_issuance_asset_amt
          , testProperty "input_issuance_token_amt" prop_input_issuance_token_amt
          , testProperty "input_issuance_asset_proof" prop_input_issuance_asset_proof
          , testProperty "input_issuance_token_proof" prop_input_issuance_token_proof
          , testProperty "current_index" prop_current_index
          , testProperty "current_is_pegin" prop_current_is_pegin
          , testProperty "current_prev_outpoint" prop_current_prev_outpoint
          , testProperty "current_asset" prop_current_asset
          , testProperty "current_amount" prop_current_amount
          , testProperty "current_script_hash" prop_current_script_hash
          , testProperty "current_sequence" prop_current_sequence
          , testProperty "current_issuance_blinding" prop_current_issuance_blinding
          , testProperty "current_issuance_contract" prop_current_issuance_contract
          , testProperty "current_issuance_entropy" prop_current_issuance_entropy
          , testProperty "current_issuance_asset_amt" prop_current_issuance_asset_amt
          , testProperty "current_issuance_token_amt" prop_current_issuance_token_amt
          , testProperty "current_issuance_asset_proof" prop_current_issuance_asset_proof
          , testProperty "current_issuance_token_proof" prop_current_issuance_token_proof
          , testProperty "tapleaf_version" prop_tapleaf_version
          , testProperty "tapbranch" prop_tapbranch
          , testProperty "internal_key" prop_internal_key
          , testProperty "annex_hash" prop_annex_hash
          , testProperty "num_outputs" prop_num_outputs
          , testProperty "output_asset" prop_output_asset
          , testProperty "output_amount" prop_output_amount
          , testProperty "output_nonce" prop_output_nonce
          , testProperty "output_script_hash" prop_output_script_hash
          , testProperty "output_null_datum" prop_output_null_datum
          , testProperty "output_surjection_proof" prop_output_surjection_proof
          , testProperty "output_range_proof" prop_output_range_proof
          , testProperty "script_cmr" prop_script_cmr
          ]
        , testGroup "Jets"
          [ testProperty "tx_is_final" prop_tx_is_final
          , testProperty "tx_lock_height" prop_tx_lock_height
          , testProperty "tx_lock_time" prop_tx_lock_time
          , testProperty "tx_lock_distance" prop_tx_lock_distance
          , testProperty "tx_lock_duration" prop_tx_lock_duration
          , testProperty "check_lock_height" prop_check_lock_height
          , testProperty "check_lock_time" prop_check_lock_time
          , testProperty "check_lock_distance" prop_check_lock_distance
          , testProperty "check_lock_duration" prop_check_lock_duration
          ]
        ]

prop_version :: Property
prop_version = forallPrimEnv $ \env -> primSem Version () env == version env ()

prop_lock_time :: Property
prop_lock_time = forallPrimEnv $ \env -> primSem LockTime () env == lock_time env ()

prop_inputs_hash :: Property
prop_inputs_hash = forallPrimEnv $ \env -> primSem InputsHash () env == inputs_hash env ()

prop_outputs_hash :: Property
prop_outputs_hash = forallPrimEnv $ \env -> primSem OutputsHash () env == outputs_hash env ()

prop_num_inputs :: Property
prop_num_inputs = forallPrimEnv $ \env -> primSem NumInputs () env == num_inputs env ()

prop_input_is_pegin :: Property
prop_input_is_pegin = forallInPrimEnv $ \env i -> primSem InputIsPegin (toW32 i) env == input_is_pegin env (toW32 i)

prop_input_prev_outpoint :: Property
prop_input_prev_outpoint = forallInPrimEnv $ \env i -> primSem InputPrevOutpoint (toW32 i) env == input_prev_outpoint env (toW32 i)

prop_input_asset :: Property
prop_input_asset = forallInPrimEnv $ \env i -> primSem InputAsset (toW32 i) env == input_asset env (toW32 i)

prop_input_amount :: Property
prop_input_amount = forallInPrimEnv $ \env i -> primSem InputAmount (toW32 i) env == input_amount env (toW32 i)

prop_input_sequence :: Property
prop_input_sequence = forallInPrimEnv $ \env i -> primSem InputSequence (toW32 i) env == input_sequence env (toW32 i)

prop_input_script_hash :: Property
prop_input_script_hash = forallInPrimEnv $ \env i -> primSem InputScriptHash (toW32 i) env == input_script_hash env (toW32 i)

prop_input_issuance_blinding :: Property
prop_input_issuance_blinding = forallInPrimEnv $ \env i -> primSem InputIssuanceBlinding (toW32 i) env == input_issuance_blinding env (toW32 i)

prop_input_issuance_contract :: Property
prop_input_issuance_contract = forallInPrimEnv $ \env i -> primSem InputIssuanceContract (toW32 i) env == input_issuance_contract env (toW32 i)

prop_input_issuance_entropy :: Property
prop_input_issuance_entropy = forallInPrimEnv $ \env i -> primSem InputIssuanceEntropy (toW32 i) env == input_issuance_entropy env (toW32 i)

prop_input_issuance_asset_amt :: Property
prop_input_issuance_asset_amt = forallInPrimEnv $ \env i -> primSem InputIssuanceAssetAmt (toW32 i) env == input_issuance_asset_amt env (toW32 i)

prop_input_issuance_token_amt :: Property
prop_input_issuance_token_amt = forallInPrimEnv $ \env i -> primSem InputIssuanceTokenAmt (toW32 i) env == input_issuance_token_amt env (toW32 i)

prop_input_issuance_asset_proof :: Property
prop_input_issuance_asset_proof = forallInPrimEnv $ \env i -> primSem InputIssuanceAssetAmt (toW32 i) env == input_issuance_asset_amt env (toW32 i)

prop_input_issuance_token_proof :: Property
prop_input_issuance_token_proof = forallInPrimEnv $ \env i -> primSem InputIssuanceTokenAmt (toW32 i) env == input_issuance_token_amt env (toW32 i)

prop_current_index :: Property
prop_current_index = forallPrimEnv $ \env -> primSem CurrentIndex () env == current_index env ()

prop_current_is_pegin :: Property
prop_current_is_pegin = forallPrimEnv $ \env -> primSem CurrentIsPegin () env == current_is_pegin env ()

prop_current_prev_outpoint :: Property
prop_current_prev_outpoint = forallPrimEnv $ \env -> primSem CurrentPrevOutpoint () env == current_prev_outpoint env ()

prop_current_asset :: Property
prop_current_asset = forallPrimEnv $ \env -> primSem CurrentAsset () env == current_asset env ()

prop_current_amount :: Property
prop_current_amount = forallPrimEnv $ \env -> primSem CurrentAmount () env == current_amount env ()

prop_current_sequence :: Property
prop_current_sequence = forallPrimEnv $ \env -> primSem CurrentSequence () env == current_sequence env ()

prop_current_script_hash :: Property
prop_current_script_hash = forallPrimEnv $ \env -> primSem CurrentScriptHash () env == current_script_hash env ()

prop_current_issuance_blinding :: Property
prop_current_issuance_blinding = forallPrimEnv $ \env -> primSem CurrentIssuanceBlinding () env == current_issuance_blinding env ()

prop_current_issuance_contract :: Property
prop_current_issuance_contract = forallPrimEnv $ \env -> primSem CurrentIssuanceContract () env == current_issuance_contract env ()

prop_current_issuance_entropy :: Property
prop_current_issuance_entropy = forallPrimEnv $ \env -> primSem CurrentIssuanceEntropy () env == current_issuance_entropy env ()

prop_current_issuance_asset_amt :: Property
prop_current_issuance_asset_amt = forallPrimEnv $ \env -> primSem CurrentIssuanceAssetAmt () env == current_issuance_asset_amt env ()

prop_current_issuance_token_amt :: Property
prop_current_issuance_token_amt = forallPrimEnv $ \env -> primSem CurrentIssuanceTokenAmt () env == current_issuance_token_amt env ()

prop_current_issuance_asset_proof :: Property
prop_current_issuance_asset_proof = forallPrimEnv $ \env -> primSem CurrentIssuanceAssetAmt () env == current_issuance_asset_amt env ()

prop_current_issuance_token_proof :: Property
prop_current_issuance_token_proof = forallPrimEnv $ \env -> primSem CurrentIssuanceTokenAmt () env == current_issuance_token_amt env ()

prop_tapleaf_version :: Property
prop_tapleaf_version = forallPrimEnv $ \env -> primSem TapleafVersion () env == tapleaf_version env ()

prop_tapbranch :: Property
prop_tapbranch = forallPrimEnv $ \env -> forAll (genTapBranchIx env) $ \i -> primSem Tapbranch (toW8 i) env == tapbranch env (toW8 i)
 where
  genTapBranchIx = genBoundaryCases . fromIntegral . length . tapBranch . envTap

prop_internal_key :: Property
prop_internal_key = forallPrimEnv $ \env -> primSem InternalKey () env == internal_key env ()

prop_annex_hash :: Property
prop_annex_hash = forallPrimEnv $ \env -> primSem AnnexHash () env == annex_hash env ()

prop_num_outputs :: Property
prop_num_outputs = forallPrimEnv $ \env -> primSem NumOutputs () env == num_outputs env ()

prop_output_asset :: Property
prop_output_asset = forallOutPrimEnv $ \env i -> primSem OutputAsset (toW32 i) env == output_asset env (toW32 i)

prop_output_amount :: Property
prop_output_amount = forallOutPrimEnv $ \env i -> primSem OutputAmount (toW32 i) env == output_amount env (toW32 i)

prop_output_nonce :: Property
prop_output_nonce = forallOutPrimEnv $ \env i -> primSem OutputNonce (toW32 i) env == output_nonce env (toW32 i)

prop_output_script_hash :: Property
prop_output_script_hash = forallOutPrimEnv $ \env i -> primSem OutputScriptHash (toW32 i) env == output_script_hash env (toW32 i)

prop_output_null_datum :: NonNegative Integer -> Property
prop_output_null_datum (NonNegative j) = forallOutPrimEnv $ \env i -> primSem OutputNullDatum (toW32 i, toWord32 j) env == output_null_datum env (toW32 i, toWord32 j)

prop_output_surjection_proof :: Property
prop_output_surjection_proof = forallOutPrimEnv $ \env i -> primSem OutputSurjectionProof (toW32 i) env == output_surjection_proof env (toW32 i)

prop_output_range_proof :: Property
prop_output_range_proof = forallOutPrimEnv $ \env i -> primSem OutputRangeProof (toW32 i) env == output_range_proof env (toW32 i)

prop_script_cmr :: Property
prop_script_cmr = forallPrimEnv $ \env -> primSem ScriptCMR () env == script_cmr env ()

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
