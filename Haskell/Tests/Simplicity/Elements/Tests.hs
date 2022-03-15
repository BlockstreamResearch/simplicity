module Simplicity.Elements.Tests (tests) where

import Data.Array ((!), listArray, elems)
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Digest.Pure.SHA (padSHA1)
import Data.Serialize (encode, put, putLazyByteString, putWord8, putWord32be, putWord32le, runPutLazy)
import Lens.Family2 (review, over)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (NonNegative(..), Property, forAll, testProperty)

import Simplicity.Digest
import Simplicity.Elements.Arbitrary
import Simplicity.Elements.DataTypes
import Simplicity.Elements.FFI.Jets
import Simplicity.Elements.Primitive
import Simplicity.Elements.Programs.CheckSigHashAll.Lib
import Simplicity.Elements.Semantics
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.CheckSigHash
import qualified Simplicity.Programs.Sha256 as Sha256
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
        , testCase "sigHashAll" (assertBool "sigHashAll_matches" hunit_sigHashAll)
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

-- :TODO: Make proper arbitrary NullDatum scripts
prop_output_null_datum :: NonNegative Integer -> Property
prop_output_null_datum (NonNegative j) = forallOutPrimEnv $ \env i -> primSem OutputNullDatum (toW32 i, toWord32 j) env == output_null_datum env (toW32 i, toWord32 j)

prop_output_surjection_proof :: Property
prop_output_surjection_proof = forallOutPrimEnv $ \env i -> primSem OutputSurjectionProof (toW32 i) env == output_surjection_proof env (toW32 i)

prop_output_range_proof :: Property
prop_output_range_proof = forallOutPrimEnv $ \env i -> primSem OutputRangeProof (toW32 i) env == output_range_proof env (toW32 i)

prop_script_cmr :: Property
prop_script_cmr = forallPrimEnv $ \env -> primSem ScriptCMR () env == script_cmr env ()

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
      , sigTxIn = listArray (0, 0) [input0]
      , sigTxOut = listArray (0, 1) [output0, output1]
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
  cmr = review (over be256) 0x896b16e4692350cb43c4807c8f9f63637f70f84a17b678ca9467109ff1e50f61
  txo = sigTxiTxo (sigTxIn tx1 ! ix)
  Just txEnv = primEnv tx1 ix tapEnv cmr
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
