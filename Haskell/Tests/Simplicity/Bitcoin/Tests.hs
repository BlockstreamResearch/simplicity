module Simplicity.Bitcoin.Tests (tests) where

import Control.Arrow ((***), (+++))
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Serialize (encode, put, putWord8, putWord32be, runPutLazy)
import Data.Vector ((!), (!?), fromList)
import Lens.Family2 (review, over, under, view)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, (@?=), assertBool, testCase)
import Test.Tasty.QuickCheck (Property, NonNegative(..), arbitrary, classify, forAll, testProperty)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Bitcoin.Arbitrary
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Jets
import Simplicity.Bitcoin.Term
import Simplicity.Bitcoin.TestEval
import Simplicity.Bitcoin.Primitive (primEnv, primEnvHash, envTx, envTap)
import qualified Simplicity.Bitcoin.Programs.TimeLock as Prog
import Simplicity.Bitcoin.Semantics
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.CheckSig.Lib
import qualified Simplicity.Programs.Sha256 as Sha256
import qualified Simplicity.Programs.Bitcoin.Lib as Prog
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as Prog
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

toW32 :: Word.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW16 :: Word.Word16 -> Word16
toW16 = toWord16 . fromIntegral

toW8 :: Word.Word8 -> Word8
toW8 = toWord8 . fromIntegral

tests :: TestTree
tests = testGroup "Bitcoin"
        [ -- Regression.tests
          testGroup "TimeLock"
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
        , testGroup "Bitcoin Functions"
          [ testProperty "outpoint_hash" prop_outpoint_hash
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
          , testProperty "tap_env_hash" prop_tap_env_hash
          , testProperty "tappath_hash" prop_tappath_hash
          , testProperty "tapleaf_hash" prop_tapleaf_hash
          , testProperty "sig_all_hash" prop_sig_all_hash
          , testProperty "script_cmr" prop_script_cmr
          , testProperty "internal_key" prop_internal_key
          , testProperty "current_index" prop_current_index
          , testProperty "num_inputs" prop_num_inputs
          , testProperty "num_outputs" prop_num_outputs
          , testProperty "lock_time" prop_lock_time
          , testProperty "output_value" prop_output_value
          , testProperty "output_script_hash" prop_output_script_hash
          --, testProperty "total_fee" prop_total_fee
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
          , testProperty "tapleaf_version" prop_tapleaf_version
          , testProperty "tappath" prop_tappath
          , testProperty "version" prop_version
          , testProperty "transaction_id" prop_transaction_id
          ]
        , testCase "sigHashAll" (assertBool "sigHashAll_matches" hunit_sigHashAll)
        ]

-- We use continuations here because we need to ensure that 'fastSpec' is memoized outside of any lambda expressions.
checkJet jet k = k (\env a -> fastSpec env a == implementation jet env a)
 where
  fastSpec = testEval (specification jet)

prop_tx_is_final :: Property
prop_tx_is_final = checkJet (BitcoinJet (TimeLockJet TxIsFinal))
                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_height :: Property
prop_tx_lock_height = checkJet (BitcoinJet (TimeLockJet TxLockHeight))
                    $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_time :: Property
prop_tx_lock_time = checkJet (BitcoinJet (TimeLockJet TxLockTime))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_distance :: Property
prop_tx_lock_distance = checkJet (BitcoinJet (TimeLockJet TxLockDistance))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_duration :: Property
prop_tx_lock_duration = checkJet (BitcoinJet (TimeLockJet TxLockDuration))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_check_lock_height :: Property
prop_check_lock_height = checkJet (BitcoinJet (TimeLockJet CheckLockHeight))
                       $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . sigTxLock $ envTx env)
                                                 $ \w -> check env (toW32 w)

prop_check_lock_time :: Property
prop_check_lock_time = checkJet (BitcoinJet (TimeLockJet CheckLockTime))
                     $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . sigTxLock $ envTx env)
                                               $ \w -> check env (toW32 w)

prop_check_lock_distance :: Property
prop_check_lock_distance = checkJet (BitcoinJet (TimeLockJet CheckLockDistance))
                         $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . txLockDistance $ envTx env)
                                                   $ \w -> check env (toW16 w)

prop_check_lock_duration :: Property
prop_check_lock_duration = checkJet (BitcoinJet (TimeLockJet CheckLockDuration))
                         $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . txLockDuration $ envTx env)
                                                   $ \w -> check env (toW16 w)

prop_build_tapleaf_simplicity :: HashElement -> Bool
prop_build_tapleaf_simplicity = \cmr ->
  let input = heAsTy cmr in
  fast_build_tapleaf_simplicity input ==
    implementation (BitcoinJet (SigHashJet BuildTapleafSimplicity)) undefined input
 where
  fast_build_tapleaf_simplicity = testCoreEval Prog.buildTapleafSimplicity

prop_build_tapbranch :: HashElement -> HashElement -> Bool
prop_build_tapbranch = \a b ->
  let input = (heAsTy a, heAsTy b) in
  fast_build_tapbranch input ==
    implementation (BitcoinJet (SigHashJet BuildTapbranch)) undefined input
 where
  fast_build_tapbranch = testCoreEval Prog.buildTapbranch

prop_build_taptweak :: FieldElement -> HashElement -> Bool
prop_build_taptweak = \a b ->
  let input = (feAsTy a, heAsTy b) in
  fast_build_taptweak input ==
    implementation (BitcoinJet (SigHashJet BuildTaptweak)) undefined input
 where
  fast_build_taptweak = testCoreEval Prog.buildTaptweak

prop_outpoint_hash :: Sha256CtxElement -> (HashElement, Word.Word32) -> Bool
prop_outpoint_hash = \ctx op ->
  let input = (ctxAsTy ctx, (heAsTy *** (toWord32 . fromIntegral) $ op))
  in fast_outpoint_hash input == implementation (BitcoinJet (SigHashJet OutpointHash)) undefined input
 where
  fast_outpoint_hash = testCoreEval Prog.outpointHash

prop_annex_hash :: Sha256CtxElement -> Maybe Word256 -> Bool
prop_annex_hash = \ctx mw256 ->
  let input = (ctxAsTy ctx, cast mw256)
  in fast_annex_hash input == implementation (BitcoinJet (SigHashJet AnnexHash)) undefined input
 where
  fast_annex_hash = testCoreEval Prog.annexHash
  cast = maybe (Left ()) Right

prop_output_values_hash :: Property
prop_output_values_hash = checkJet (BitcoinJet (SigHashJet OutputValuesHash))
                         $ \check -> forallPrimEnv $ \env -> check env ()

prop_output_scripts_hash :: Property
prop_output_scripts_hash = checkJet (BitcoinJet (SigHashJet OutputScriptsHash))
                         $ \check -> forallPrimEnv $ \env -> check env ()

prop_outputs_hash :: Property
prop_outputs_hash = checkJet (BitcoinJet (SigHashJet OutputsHash))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_output_hash :: Property
prop_output_hash = checkJet (BitcoinJet (SigHashJet OutputHash))
                  $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_input_outpoints_hash :: Property
prop_input_outpoints_hash = checkJet (BitcoinJet (SigHashJet InputOutpointsHash))
                          $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_values_hash :: Property
prop_input_values_hash = checkJet (BitcoinJet (SigHashJet InputValuesHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_scripts_hash :: Property
prop_input_scripts_hash = checkJet (BitcoinJet (SigHashJet InputScriptsHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_utxos_hash :: Property
prop_input_utxos_hash = checkJet (BitcoinJet (SigHashJet InputUtxosHash))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_utxo_hash :: Property
prop_input_utxo_hash = checkJet (BitcoinJet (SigHashJet InputUtxoHash))
                     $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_sequences_hash :: Property
prop_input_sequences_hash = checkJet (BitcoinJet (SigHashJet InputSequencesHash))
                          $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_annexes_hash :: Property
prop_input_annexes_hash = checkJet (BitcoinJet (SigHashJet InputAnnexesHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_script_sigs_hash :: Property
prop_input_script_sigs_hash = checkJet (BitcoinJet (SigHashJet InputScriptSigsHash))
                            $ \check -> forallPrimEnv $ \env -> check env ()

prop_inputs_hash :: Property
prop_inputs_hash = checkJet (BitcoinJet (SigHashJet InputsHash))
                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_hash :: Property
prop_input_hash = checkJet (BitcoinJet (SigHashJet InputHash))
                 $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_tx_hash :: Property
prop_tx_hash = checkJet (BitcoinJet (SigHashJet TxHash))
             $ \check -> forallPrimEnv $ \env -> check env ()

prop_tappath_hash :: Property
prop_tappath_hash = checkJet (BitcoinJet (SigHashJet TappathHash))
                    $ \check -> forallPrimEnv $ \env -> check env ()

prop_tapleaf_hash :: Property
prop_tapleaf_hash = checkJet (BitcoinJet (SigHashJet TapleafHash))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_tap_env_hash :: Property
prop_tap_env_hash = checkJet (BitcoinJet (SigHashJet TapEnvHash))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_sig_all_hash :: Property
prop_sig_all_hash = checkJet (BitcoinJet (SigHashJet SigAllHash))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_script_cmr :: Property
prop_script_cmr = checkJet (BitcoinJet (TransactionJet ScriptCMR))
                $ \check -> forallPrimEnv $ \env -> check env ()

prop_internal_key :: Property
prop_internal_key = checkJet (BitcoinJet (TransactionJet InternalKey))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_index :: Property
prop_current_index = checkJet (BitcoinJet (TransactionJet CurrentIndex))
                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_num_inputs :: Property
prop_num_inputs = checkJet (BitcoinJet (TransactionJet NumInputs))
                $ \check -> forallPrimEnv $ \env -> check env ()

prop_num_outputs :: Property
prop_num_outputs = checkJet (BitcoinJet (TransactionJet NumOutputs))
                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_lock_time :: Property
prop_lock_time = checkJet (BitcoinJet (TransactionJet LockTime))
               $ \check -> forallPrimEnv $ \env -> check env ()

prop_output_value :: Property
prop_output_value = checkJet (BitcoinJet (TransactionJet OutputValue))
                   $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_script_hash :: Property
prop_output_script_hash = checkJet (BitcoinJet (TransactionJet OutputScriptHash))
                        $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

{-
prop_total_fee :: Property
prop_total_fee = checkJet (BitcoinJet (TransactionJet TotalFee))
               $ \check -> forallOutPrimEnv $ \env i -> forAll arbitraryHash256
               $ \hash -> let input = fromMaybe hash (getAssetId (sigTxOut (envTx env)) (fromIntegral i))
                              fee = Map.findWithDefault 0 input (totalFee (envTx env))
                          in classify (0 /= fee) "non-zero fee" $ check env (fromHash input)
 where
  getAssetId outputs ix = (outputs !? ix) >>= explicitId . view (under asset) . txoAsset
  explicitId (Explicit a) = Just a
  explicitId (Confidential _ _) = Nothing
  fromHash = toWord256 . integerHash256
-}

prop_current_prev_outpoint :: Property
prop_current_prev_outpoint = checkJet (BitcoinJet (TransactionJet CurrentPrevOutpoint))
                           $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_value :: Property
prop_current_value = checkJet (BitcoinJet (TransactionJet CurrentValue))
                    $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_script_hash :: Property
prop_current_script_hash = checkJet (BitcoinJet (TransactionJet CurrentScriptHash))
                         $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_sequence :: Property
prop_current_sequence = checkJet (BitcoinJet (TransactionJet CurrentSequence))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_annex_hash :: Property
prop_current_annex_hash = checkJet (BitcoinJet (TransactionJet CurrentAnnexHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_script_sig_hash :: Property
prop_current_script_sig_hash = checkJet (BitcoinJet (TransactionJet CurrentScriptSigHash))
                             $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_prev_outpoint :: Property
prop_input_prev_outpoint = checkJet (BitcoinJet (TransactionJet InputPrevOutpoint))
                         $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_value :: Property
prop_input_value = checkJet (BitcoinJet (TransactionJet InputValue))
                  $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_script_hash :: Property
prop_input_script_hash = checkJet (BitcoinJet (TransactionJet InputScriptHash))
                       $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_sequence :: Property
prop_input_sequence = checkJet (BitcoinJet (TransactionJet InputSequence))
                    $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_annex_hash :: Property
prop_input_annex_hash = checkJet (BitcoinJet (TransactionJet InputAnnexHash))
                      $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_script_sig_hash :: Property
prop_input_script_sig_hash = checkJet (BitcoinJet (TransactionJet InputScriptSigHash))
                           $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_tapleaf_version :: Property
prop_tapleaf_version = checkJet (BitcoinJet (TransactionJet TapleafVersion))
                     $ \check -> forallPrimEnv $ \env -> check env ()

prop_tappath :: Property
prop_tappath = checkJet (BitcoinJet (TransactionJet Tappath))
               $ \check -> forallPrimEnv $ \env -> forAll (genTappathIx env) $ \i -> check env (toW8 i)
 where
  genTappathIx = genBoundaryCases . fromIntegral . length . tappath . envTap

prop_version :: Property
prop_version = checkJet (BitcoinJet (TransactionJet Version))
             $ \check -> forallPrimEnv $ \env -> check env ()

prop_transaction_id :: Property
prop_transaction_id = checkJet (BitcoinJet (TransactionJet TransactionId))
                        $ \check -> forallPrimEnv $ \env -> check env ()

tapEnv :: TapEnv
tapEnv = TapEnv
         { tapleafVersion = 0xbe
         , tapInternalKey = Schnorr.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
         , tappath = []
         , tapScriptCMR = review (over be256) 0x896b16e4692350cb43c4807c8f9f63637f70f84a17b678ca9467109ff1e50f61
         }

tx1 :: SigTx
tx1 = SigTx
      { sigTxVersion = 0x00000002
      , sigTxIn = fromList [input0]
      , sigTxOut = fromList [output0]
      , sigTxLock = 0
      }
 where
  input0 = SigTxInput
    { sigTxiPreviousOutpoint = Outpoint (review (over be256) 0xeb04b68e9a26d116046c76e8ff47332fb71dda90ff4bef5370f25226d3bc09fc) 0
    , sigTxiTxo = TxOutput
        { txoValue = 10000000000
        , txoScript = BSL.empty
        }
    , sigTxiSequence = 0xfffffffe
    , sigTxiAnnex = Nothing
    , sigTxiScriptSig = BSL.empty
    }
  output0 = TxOutput
    { txoValue = 9999996700
    , txoScript = BSL.pack
        [ 0x19, 0x76, 0xa9, 0x14, 0x48, 0x63, 0x3e, 0x2c, 0x0e, 0xe9, 0x49, 0x5d, 0xd3, 0xf9, 0xc4, 0x37
        , 0x32, 0xc4, 0x7f, 0x47, 0x02, 0xa3, 0x62, 0xc8, 0x88, 0xac]
    }

hunit_sigHashAll :: Bool
hunit_sigHashAll = Just (integerHash256 sigHashAll_spec) == (fromWord256 <$> (sem (sigHash' Prog.sigAllHash) txEnv ()))
 where
  ix = 0
  txo = sigTxiTxo (sigTxIn tx1 ! (fromIntegral ix))
  Just txEnv = primEnv tx1 ix tapEnv
  signatureTag = bsHash $ BSC.pack "Simplicity\USSignature"
  sigHashAll_spec = bslHash . runPutLazy
                  $ put signatureTag >> put signatureTag
                 >> put (commitmentRoot Prog.sigAllHash)
                 >> put (primEnvHash txEnv)
