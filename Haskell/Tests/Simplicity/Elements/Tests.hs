module Simplicity.Elements.Tests (tests) where

import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Serialize (encode, put, putWord8, putWord32be, runPutLazy)
import Data.Vector ((!), fromList)
import Lens.Family2 (review, over)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, (@?=), assertBool, testCase)
import Test.Tasty.QuickCheck (Property, NonNegative(..), arbitrary, forAll, testProperty)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Elements.Arbitrary
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Jets
import Simplicity.Elements.TestEval
import Simplicity.Elements.Primitive (primEnv, envTx, envTap)
import Simplicity.Elements.Programs.CheckSigHashAll.Lib
import qualified Simplicity.Elements.Programs.TimeLock as Prog
import Simplicity.Elements.Semantics
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.CheckSigHash
import qualified Simplicity.Programs.Sha256 as Sha256
import qualified Simplicity.Programs.Elements.Lib as Prog
import qualified Simplicity.Elements.Programs.Issuance.Lib as Prog
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
tests = testGroup "Elements"
        [ testGroup "TimeLock"
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
        , testGroup "Elements Functions"
          [ testProperty "calculate_issuance_entropy" prop_calculate_issuance_entropy
          , testProperty "calculate_asset" prop_calculate_asset
          , testProperty "calculate_explicit_token" prop_calculate_explicit_token
          , testProperty "calculate_confidential_token" prop_calculate_confidential_token
          , testProperty "input_issuance" prop_input_issuance
          , testProperty "input_issuance_asset" prop_input_issuance_asset
          , testProperty "input_issuance_token" prop_input_issuance_token
          , testProperty "input_issuance_entropy" prop_input_issuance_entropy
          , testProperty "script_cmr" prop_script_cmr
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
          , testProperty "output_surjection_proof" prop_output_surjection_proof
          , testProperty "output_range_proof" prop_output_range_proof
          , testProperty "current_is_pegin" prop_current_is_pegin
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
          , testProperty "input_is_pegin" prop_input_is_pegin
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
          , testProperty "tapbranch" prop_tapbranch
          , testProperty "version" prop_version
          , testProperty "genesis_block_hash" prop_genesis_block_hash
          , testCase "issuance_entropy_1" assert_issuance_entropy_1
          , testCase "calculate_asset_1" assert_calculate_asset_1
          , testCase "calculcate_token_1" assert_calculcate_token_1
          , testCase "issuance_entropy_2" assert_issuance_entropy_2
          , testCase "calculate_asset_2" assert_calculate_asset_2
          , testCase "calculcate_token_2" assert_calculcate_token_2
          , testCase "issuance_entropy_3" assert_issuance_entropy_3
          , testCase "calculate_asset_3" assert_calculate_asset_3
          , testCase "calculcate_token_3" assert_calculcate_token_3
          , testCase "issuance_entropy_4" assert_issuance_entropy_4
          , testCase "calculate_asset_4" assert_calculate_asset_4
          , testCase "calculcate_token_4" assert_calculcate_token_4
          ]
        , testCase "sigHashAll" (assertBool "sigHashAll_matches" hunit_sigHashAll)
        ]


-- We use continuations here because we need to ensure that 'fastSpec' is memoized outside of any lambda expressions.
checkJet jet k = k (\env a -> fastSpec env a == implementation jet env a)
 where
  fastSpec = testEval (specification jet)

prop_tx_is_final :: Property
prop_tx_is_final = checkJet (ElementsJet (TimeLockJet TxIsFinal))
                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_height :: Property
prop_tx_lock_height = checkJet (ElementsJet (TimeLockJet TxLockHeight))
                    $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_time :: Property
prop_tx_lock_time = checkJet (ElementsJet (TimeLockJet TxLockTime))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_distance :: Property
prop_tx_lock_distance = checkJet (ElementsJet (TimeLockJet TxLockDistance))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_tx_lock_duration :: Property
prop_tx_lock_duration = checkJet (ElementsJet (TimeLockJet TxLockDuration))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_check_lock_height :: Property
prop_check_lock_height = checkJet (ElementsJet (TimeLockJet CheckLockHeight))
                       $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . sigTxLock $ envTx env)
                                                 $ \w -> check env (toW32 w)

prop_check_lock_time :: Property
prop_check_lock_time = checkJet (ElementsJet (TimeLockJet CheckLockTime))
                     $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . sigTxLock $ envTx env)
                                               $ \w -> check env (toW32 w)

prop_check_lock_distance :: Property
prop_check_lock_distance = checkJet (ElementsJet (TimeLockJet CheckLockDistance))
                         $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . txLockDistance $ envTx env)
                                                   $ \w -> check env (toW16 w)

prop_check_lock_duration :: Property
prop_check_lock_duration = checkJet (ElementsJet (TimeLockJet CheckLockDuration))
                         $ \check -> forallPrimEnv $ \env -> forAll (genBoundaryCases . txLockDuration $ envTx env)
                                                   $ \w -> check env (toW16 w)

prop_calculate_issuance_entropy :: Outpoint -> HashElement -> Bool
prop_calculate_issuance_entropy = \op contract ->
  let input = ((fromHash (opHash op), fromIndex (opIndex op)), heAsTy contract) in
  fast_calculate_issuance_entropy input ==
    implementation (ElementsJet (IssuanceJet CalculateIssuanceEntropy)) undefined input
 where
  fromHash = toWord256 . integerHash256
  fromIndex = toWord32 . fromIntegral
  fast_calculate_issuance_entropy = testCoreEval Prog.calculateIssuanceEntropy

prop_calculate_asset :: HashElement -> Bool
prop_calculate_asset = \entropy ->
  let input = heAsTy entropy in
  fast_calculate_asset input ==
    implementation (ElementsJet (IssuanceJet CalculateAsset)) undefined input
 where
  fast_calculate_asset = testCoreEval Prog.calculateAsset

prop_calculate_explicit_token :: HashElement -> Bool
prop_calculate_explicit_token = \entropy ->
  let input = heAsTy entropy in
  fast_calculate_explicit_token input ==
    implementation (ElementsJet (IssuanceJet CalculateExplicitToken)) undefined input
 where
  fast_calculate_explicit_token = testCoreEval Prog.calculateExplicitToken

prop_calculate_confidential_token :: HashElement -> Bool
prop_calculate_confidential_token = \entropy ->
  let input = heAsTy entropy in
  fast_calculate_confidential_token input ==
    implementation (ElementsJet (IssuanceJet CalculateConfidentialToken)) undefined input
 where
  fast_calculate_confidential_token = testCoreEval Prog.calculateConfidentialToken

prop_input_issuance :: Property
prop_input_issuance = checkJet (ElementsJet (IssuanceJet Issuance))
                    $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_issuance_asset :: Property
prop_input_issuance_asset = checkJet (ElementsJet (IssuanceJet IssuanceAsset))
                          $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_issuance_token :: Property
prop_input_issuance_token = checkJet (ElementsJet (IssuanceJet IssuanceToken))
                          $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_issuance_entropy :: Property
prop_input_issuance_entropy = checkJet (ElementsJet (IssuanceJet IssuanceEntropy))
                            $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_script_cmr :: Property
prop_script_cmr = checkJet (ElementsJet (TransactionJet ScriptCMR))
                $ \check -> forallPrimEnv $ \env -> check env ()

prop_internal_key :: Property
prop_internal_key = checkJet (ElementsJet (TransactionJet InternalKey))
                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_index :: Property
prop_current_index = checkJet (ElementsJet (TransactionJet CurrentIndex))
                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_num_inputs :: Property
prop_num_inputs = checkJet (ElementsJet (TransactionJet NumInputs))
                $ \check -> forallPrimEnv $ \env -> check env ()

prop_num_outputs :: Property
prop_num_outputs = checkJet (ElementsJet (TransactionJet NumOutputs))
                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_lock_time :: Property
prop_lock_time = checkJet (ElementsJet (TransactionJet LockTime))
               $ \check -> forallPrimEnv $ \env -> check env ()

prop_output_asset :: Property
prop_output_asset = checkJet (ElementsJet (TransactionJet OutputAsset))
                  $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_amount :: Property
prop_output_amount = checkJet (ElementsJet (TransactionJet OutputAssetAmount))
                   $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_nonce :: Property
prop_output_nonce = checkJet (ElementsJet (TransactionJet OutputNonce))
                  $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_script_hash :: Property
prop_output_script_hash = checkJet (ElementsJet (TransactionJet OutputScriptHash))
                        $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_null_datum :: Property
prop_output_null_datum = checkJet (ElementsJet (TransactionJet OutputNullDatum))
                       $ \check -> forallOutPrimEnv $ \env i -> forAll arbitrary $ \(NonNegative j) -> check env (toW32 i, toWord32 j)

prop_output_surjection_proof :: Property
prop_output_surjection_proof = checkJet (ElementsJet (TransactionJet OutputSurjectionProof))
                             $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_output_range_proof :: Property
prop_output_range_proof = checkJet (ElementsJet (TransactionJet OutputRangeProof))
                        $ \check -> forallOutPrimEnv $ \env i -> check env (toW32 i)

prop_current_is_pegin :: Property
prop_current_is_pegin = checkJet (ElementsJet (TransactionJet CurrentIsPegin))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_prev_outpoint :: Property
prop_current_prev_outpoint = checkJet (ElementsJet (TransactionJet CurrentPrevOutpoint))
                           $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_asset :: Property
prop_current_asset = checkJet (ElementsJet (TransactionJet CurrentAsset))
                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_amount :: Property
prop_current_amount = checkJet (ElementsJet (TransactionJet CurrentAssetAmount))
                    $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_script_hash :: Property
prop_current_script_hash = checkJet (ElementsJet (TransactionJet CurrentScriptHash))
                         $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_sequence :: Property
prop_current_sequence = checkJet (ElementsJet (TransactionJet CurrentSequence))
                      $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_annex_hash :: Property
prop_current_annex_hash = checkJet (ElementsJet (TransactionJet CurrentAnnexHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_script_sig_hash :: Property
prop_current_script_sig_hash = checkJet (ElementsJet (TransactionJet CurrentScriptSigHash))
                             $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_reissuance_blinding :: Property
prop_current_reissuance_blinding = checkJet (ElementsJet (TransactionJet CurrentReissuanceBlinding))
                                 $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_new_issuance_contract :: Property
prop_current_new_issuance_contract = checkJet (ElementsJet (TransactionJet CurrentNewIssuanceContract))
                                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_reissuance_entropy :: Property
prop_current_reissuance_entropy = checkJet (ElementsJet (TransactionJet CurrentReissuanceEntropy))
                                $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_issuance_asset_amount :: Property
prop_current_issuance_asset_amount = checkJet (ElementsJet (TransactionJet CurrentIssuanceAssetAmount))
                                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_issuance_token_amount :: Property
prop_current_issuance_token_amount = checkJet (ElementsJet (TransactionJet CurrentIssuanceTokenAmount))
                                   $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_issuance_asset_proof :: Property
prop_current_issuance_asset_proof = checkJet (ElementsJet (TransactionJet CurrentIssuanceAssetProof))
                                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_current_issuance_token_proof :: Property
prop_current_issuance_token_proof = checkJet (ElementsJet (TransactionJet CurrentIssuanceTokenProof))
                                  $ \check -> forallPrimEnv $ \env -> check env ()

prop_input_is_pegin :: Property
prop_input_is_pegin = checkJet (ElementsJet (TransactionJet InputIsPegin))
                    $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_prev_outpoint :: Property
prop_input_prev_outpoint = checkJet (ElementsJet (TransactionJet InputPrevOutpoint))
                         $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_asset :: Property
prop_input_asset = checkJet (ElementsJet (TransactionJet InputAsset))
                 $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_amount :: Property
prop_input_amount = checkJet (ElementsJet (TransactionJet InputAssetAmount))
                  $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_script_hash :: Property
prop_input_script_hash = checkJet (ElementsJet (TransactionJet InputScriptHash))
                       $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_sequence :: Property
prop_input_sequence = checkJet (ElementsJet (TransactionJet InputSequence))
                    $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_annex_hash :: Property
prop_input_annex_hash = checkJet (ElementsJet (TransactionJet InputAnnexHash))
                      $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_input_script_sig_hash :: Property
prop_input_script_sig_hash = checkJet (ElementsJet (TransactionJet InputScriptSigHash))
                           $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_reissuance_blinding :: Property
prop_reissuance_blinding = checkJet (ElementsJet (TransactionJet ReissuanceBlinding))
                         $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_new_issuance_contract :: Property
prop_new_issuance_contract = checkJet (ElementsJet (TransactionJet NewIssuanceContract))
                           $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_reissuance_entropy :: Property
prop_reissuance_entropy = checkJet (ElementsJet (TransactionJet ReissuanceEntropy))
                        $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_issuance_asset_amount :: Property
prop_issuance_asset_amount = checkJet (ElementsJet (TransactionJet IssuanceAssetAmount))
                           $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_issuance_token_amount :: Property
prop_issuance_token_amount = checkJet (ElementsJet (TransactionJet IssuanceTokenAmount))
                           $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_issuance_asset_proof :: Property
prop_issuance_asset_proof = checkJet (ElementsJet (TransactionJet IssuanceAssetProof))
                          $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_issuance_token_proof :: Property
prop_issuance_token_proof = checkJet (ElementsJet (TransactionJet IssuanceTokenProof))
                          $ \check -> forallInPrimEnv $ \env i -> check env (toW32 i)

prop_tapleaf_version :: Property
prop_tapleaf_version = checkJet (ElementsJet (TransactionJet TapleafVersion))
                     $ \check -> forallPrimEnv $ \env -> check env ()

prop_tapbranch :: Property
prop_tapbranch = checkJet (ElementsJet (TransactionJet Tapbranch))
               $ \check -> forallPrimEnv $ \env -> forAll (genTapBranchIx env) $ \i -> check env (toW8 i)
 where
  genTapBranchIx = genBoundaryCases . fromIntegral . length . tapBranch . envTap

prop_version :: Property
prop_version = checkJet (ElementsJet (TransactionJet Version))
             $ \check -> forallPrimEnv $ \env -> check env ()

prop_genesis_block_hash :: Property
prop_genesis_block_hash = checkJet (ElementsJet (TransactionJet GenesisBlockHash))
                        $ \check -> forallPrimEnv $ \env -> check env ()

-- example test data from Elements Core 0.17
(assert_issuance_entropy_1, assert_calculate_asset_1, assert_calculcate_token_1) =
  ( calculateIssuanceEntropy outpoint contractHash @?= entropy
  , calculateAsset entropy @?= assetID
  , calculateToken (Amount (Explicit undefined)) entropy @?= tokenID
  )
 where
  contractHash = review (over le256) 0
  outpoint = Outpoint (review (over le256) 0x05a047c98e82a848dee94efcf32462b065198bebf2404d201ba2e06db30b28f4) 0
  entropy = review (over le256) 0x746f447f691323502cad2ef646f932613d37a83aeaa2133185b316648df4b70a
  assetID = review (over le256) 0xdcd60818d863b5c026c40b2bc3ba6fdaf5018bcc8606c18adf7db4da0bcd8533
  tokenID = review (over le256) 0xc1adb114f4f87d33bf9ce90dd4f9ca523dd414d6cd010a7917903e2009689530

-- example test data from Elements Core 0.21 with prevout vout = 1
(assert_issuance_entropy_2, assert_calculate_asset_2, assert_calculcate_token_2) =
  ( calculateIssuanceEntropy outpoint contractHash @?= entropy
  , calculateAsset entropy @?= assetID
  , calculateToken (Amount (Confidential undefined undefined)) entropy @?= tokenID
  )
 where
  contractHash = review (over le256) 0
  outpoint = Outpoint (review (over le256) 0xc76664aa4be760056dcc39b59637eeea8f3c3c3b2aeefb9f23a7b99945a2931e) 1
  entropy = review (over le256) 0xbc67a13736341d8ad19e558433483a38cae48a44a5a8b5598ca0b01b5f9f9f41
  assetID = review (over le256) 0x2ec6c1a06e895b06fffb8dc36084255f890467fb906565b0c048d4c807b4a129
  tokenID = review (over le256) 0xd09d205ff7c626ca98c91fed24787ff747fec62194ed1b7e6ef6cc775a1a1fdc

-- example test data from Elements Core 0.21 with a given contract hash and non-blinded issuance
(assert_issuance_entropy_3, assert_calculate_asset_3, assert_calculcate_token_3) =
  ( calculateIssuanceEntropy outpoint contractHash @?= entropy
  , calculateAsset entropy @?= assetID
  , calculateToken (Amount (Explicit undefined)) entropy @?= tokenID
  )
 where
  contractHash = review (over le256) 0xe06e6d4933e76afd7b9cc6a013e0855aa60bbe6d2fca1c27ec6951ff5f1a20c9
  outpoint = Outpoint (review (over le256) 0xee45365ddb62e8822182fbdd132fb156b4991e0b7411cff4aab576fd964f2edb) 0
  entropy = review (over le256) 0x1922da340705eef526640b49d28b08928630d1ad52db0f945f3c389267e292c9
  assetID = review (over le256) 0x8eebf6109bca0331fe559f0cbd1ef846a2bbb6812f3ae3d8b0b610170cc21a4e
  tokenID = review (over le256) 0xeb02cbc591c9ede071625c129f0a1fab386202cb27a894a45be0d564e961d6bc

-- example test data from Elements Core 0.21 with confidential re-issuance
(assert_issuance_entropy_4, assert_calculate_asset_4, assert_calculcate_token_4) =
  ( calculateIssuanceEntropy outpoint contractHash @?= entropy
  , calculateAsset entropy @?= assetID
  , calculateToken (Amount (Confidential undefined undefined)) entropy @?= tokenID
  )
 where
  contractHash = review (over le256) 0
  outpoint = Outpoint (review (over le256) 0x8903ee739b52859877fbfedc58194c2d59d0f5a4ea3c2774dc3cba3031cec757) 0
  entropy = review (over le256) 0xb9789de8589dc1b664e4f2bda4d04af9d4d2180394a8c47b1f889acfb5e0acc4
  assetID = review (over le256) 0xbdab916e8cda17781bcdb84505452e44d0ab2f080e9e5dd7765ffd5ce0c07cd9
  tokenID = review (over le256) 0xf144868169dfc7afc024c4d8f55607ac8dfe925e67688650a9cdc54c3cfa5b1c

tapEnv :: TapEnv
tapEnv = TapEnv
         { tapAnnex = Nothing
         , tapLeafVersion = 0xbe
         , tapInternalKey = Schnorr.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
         , tapBranch = []
         }

tx1 :: SigTx
tx1 = SigTx
      { sigTxVersion = 0x00000002
      , sigTxIn = fromList [input0]
      , sigTxOut = fromList [output0, output1]
      , sigTxLock = 0
      }
 where
  assetId = Asset . Explicit $ review (over be256) 0x230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2
  input0 = SigTxInput
    { sigTxiIsPegin = False
    , sigTxiPreviousOutpoint = Outpoint (review (over be256) 0xeb04b68e9a26d116046c76e8ff47332fb71dda90ff4bef5370f25226d3bc09fc) 0
    , sigTxiTxo = UTXO
        { utxoAsset = assetId
        , utxoAmount = Amount . Explicit $ 10000000000
        , utxoScript = BSL.empty
        }
    , sigTxiSequence = 0xfffffffe
    , sigTxiIssuance = Nothing
    , sigTxiAnnex = Nothing
    , sigTxiScriptSig = BSL.empty
    }
  output0 = TxOutput
    { txoAsset = assetId
    , txoAmount = Amount . Explicit $ 9999996700
    , txoNonce = Nothing
    , txoScript = BSL.pack
        [ 0x19, 0x76, 0xa9, 0x14, 0x48, 0x63, 0x3e, 0x2c, 0x0e, 0xe9, 0x49, 0x5d, 0xd3, 0xf9, 0xc4, 0x37
        , 0x32, 0xc4, 0x7f, 0x47, 0x02, 0xa3, 0x62, 0xc8, 0x88, 0xac]
    }
  output1 = TxOutput
    { txoAsset = assetId
    , txoAmount = Amount . Explicit $ 3300
    , txoNonce = Nothing
    , txoScript = BSL.empty
    }

hunit_sigHashAll :: Bool
hunit_sigHashAll = all (Just (integerHash256 sigHashAll_spec) ==)
                   [fromWord256 <$> (sem sigHashAll txEnv ()), fromWord256 <$> (sem (sigHash Sha256.lib hashAll) txEnv ())]
 where
  ix = 0
  genesis = review (over be256) 0x0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206
  cmr = review (over be256) 0x896b16e4692350cb43c4807c8f9f63637f70f84a17b678ca9467109ff1e50f61
  txo = sigTxiTxo (sigTxIn tx1 ! (fromIntegral ix))
  Just txEnv = primEnv tx1 ix tapEnv genesis cmr
  sigHashTag = bsHash $ BSC.pack "Simplicity-Draft\USSigHash"
  taproot_spec = bsHash $ encode cmr <> encode (tapLeafVersion tapEnv)
  asset_spec (Asset (Explicit id)) = bsHash $ encode (0x01 :: Word.Word256) <> encode id
  asset_spec (Asset (Confidential (Point b x) _)) = bsHash $ encode (if b then 0x0b else 0x0a :: Word.Word256) <> encode (Schnorr.fe_pack x)
  amount_spec (Amount (Explicit amt)) = bsHash $ encode (0x01 :: Word.Word256) <> encode (fromIntegral amt :: Word.Word256)
  amount_spec (Amount (Confidential (Point b x) _)) = bsHash $ encode (if b then 0x09 else 0x08 :: Word.Word256) <> encode (Schnorr.fe_pack x)
  hashAll_spec = bslHash . runPutLazy
               $ put sigHashTag >> put sigHashTag
              >> put (sigTxInputsHash tx1)
              >> put (sigTxOutputsHash tx1)
              >> put (bsHash mempty)
              >> put taproot_spec
              >> put (asset_spec (utxoAsset txo))
              >> put (amount_spec (utxoAmount txo))
              >> putWord32be (sigTxVersion tx1)
              >> putWord32be (sigTxLock tx1)
              >> putWord32be ix
  signatureTag = bsHash $ BSC.pack "Simplicity-Draft\USSignature"
  sigHashAll_spec = bslHash . runPutLazy
                  $ put signatureTag >> put signatureTag
                 >> put (commitmentRoot hashAll)
                 >> put hashAll_spec
