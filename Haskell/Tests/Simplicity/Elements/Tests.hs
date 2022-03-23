module Simplicity.Elements.Tests (tests) where

import Data.Array ((!), listArray)
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Serialize (encode, put, putWord8, putWord32be, runPutLazy)
import Lens.Family2 (review, over)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Primitive
import Simplicity.Elements.Programs.CheckSigHashAll.Lib
import Simplicity.Elements.Semantics
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.CheckSigHash
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Ty.Word
import qualified Simplicity.Word as Word

tests :: TestTree
tests = testGroup "Elements"
        [ testCase "sigHashAll" (assertBool "sigHashAll_matches" hunit_sigHashAll)
        ]

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
