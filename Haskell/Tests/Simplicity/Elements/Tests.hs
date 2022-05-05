module Simplicity.Elements.Tests (tests) where

import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Either (fromLeft, fromRight)
import Data.Serialize (encode, put, putWord8, putWord32be, runPutLazy)
import Data.Vector ((!), fromList)
import Lens.Family2 (review, over)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, (@?=), assertBool, testCase)
import Test.Tasty.QuickCheck (Property, forAll, testProperty)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Elements.Arbitrary
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Jets
import Simplicity.Elements.TestEval
import Simplicity.Elements.Primitive
import Simplicity.Elements.Programs.CheckSigHashAll.Lib
import qualified Simplicity.Elements.Programs.TimeLock as Prog
import Simplicity.Elements.Semantics
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.CheckSigHash
import qualified Simplicity.Programs.Sha256 as Sha256
import qualified Simplicity.Programs.Elements.Lib as Prog
import Simplicity.TestCoreEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

toW32 :: Word.Word32 -> Word32
toW32 = toWord32 . fromIntegral

toW16 :: Word.Word16 -> Word16
toW16 = toWord16 . fromIntegral

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
  txo = sigTxiTxo (sigTxIn tx1 ! (fromIntegral ix))
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
