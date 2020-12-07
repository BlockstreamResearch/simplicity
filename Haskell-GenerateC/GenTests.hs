{-# LANGUAGE KindSignatures, ScopedTypeVariables #-}
module GenTests where

import Data.Array (listArray)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Char (toUpper)
import Data.List (intercalate)
import Data.List.Split (chunksOf)
import Data.Serialize (encode, runPut)
import Numeric (showHex)
import System.IO (hPutStrLn, stderr)
import Lens.Family2 ((^.), over, review, to, Getter')

import Simplicity.Digest
import qualified Simplicity.Elements.JetType
import qualified Simplicity.Elements.Dag
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Primitive
import Simplicity.Elements.Jets (JetType, WrappedSimplicity, fastEval, jetSubst, unwrap)
import Simplicity.Elements.Serialization.BitString
import qualified Simplicity.Elements.Programs.CheckSigHashAll.Lib
import Simplicity.Elements.Term
import qualified Simplicity.LibSecp256k1.Spec
import Simplicity.MerkleRoot
import Simplicity.Programs.Generic
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Sha256
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib
import qualified Simplicity.Programs.CheckSigHash
import Simplicity.Serialization
import Simplicity.Word

data Example (jt :: * -> * -> *)
             a b = Example { _name :: String
                           , _path :: [String]
                           , _text :: [String]
                           , _withJets :: Bool
                           , _prog :: WrappedSimplicity a b
                           }
type ExampleNoJets a b = Example Simplicity.Elements.JetType.NoJets a b
type ExampleProg = Example JetType () ()

name f (Example n pa t wj pr) = (\n -> Example n pa t wj pr) <$> f n
path f (Example n pa t wj pr) = (\pa -> Example n pa t wj pr) <$> f pa
text f (Example n pa t wj pr) = (\t -> Example n pa t wj pr) <$> f t
withJets f (Example n pa t wj pr) = (\wj -> Example n pa t wj pr) <$> f wj
prog f (Example n pa t wj pr) = (\pr -> Example n pa t wj pr) <$> f pr

fullname = to proj
 where
  proj x | null (x^.path) = x^.name
         | otherwise = last (x^.path) ++ capital (x^.name)
  capital [] = []
  capital (a:b) = toUpper a : b

showComment wj txt = unlines $ ["/* A length-prefixed encoding of the following Simplicity program:"]
                  ++ body
                  ++ [" * with jets." | wj]
                  ++ [" */"]
 where
  body = map (" *     "++) $ txt

showBinary name bin = unlines $ start ++ [intercalate ",\n" chunks] ++ finish
 where
  start = ["const unsigned char "++name++"[] = {"]
  finish = ["};", "", "const size_t sizeof_"++name++" = sizeof("++name++");"]
  chunks = ("  "++) . intercalate ", " <$> chunksOf 20 (showByte <$> bin)
  showByte b = "0x" ++ padding ++ t
   where
    padding = replicate (2 - length t) '0'
    t = showHex b ""

showHash name h = unlines $ ["const uint32_t "++name++"[] = {", body, "};"]
 where
  str_h = padding ++ text
   where
    padding = replicate (64 - length text) '0'
    text = Numeric.showHex (integerHash256 h) ""
  body = "  " ++ intercalate ", " (format <$> chunksOf 8 str_h)
   where
    format x = "0x" ++ x ++ "u"

fileC :: forall jt a b. (Simplicity.Elements.JetType.JetType jt, TyC a, TyC b) => Example jt a b -> String
fileC example = "#include \""++example^.name++".h\"\n"
        ++ "\n"
        ++ showComment (example^.withJets) (example^.text)
        ++ showBinary (example^.fullname) binary
        ++ "\n"
        ++ "/* The commitment Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_cmr") cmr
        ++ "\n"
        ++ "/* The identity Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_imr") imr
        ++ "\n"
        ++ "/* The annotated Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_amr") amr
 where
  binary = BS.unpack . runPut . putBitStream . putTermLengthCode
         $ (unwrap (example^.prog) :: Simplicity.Elements.Dag.JetDag jt a b)
  cmr = commitmentRoot . unwrap $ example^.prog
  imr = identityRoot . unwrap $ example^.prog
  amr = annotatedRoot . unwrap $ example^.prog

fileH example = "#ifndef "++headerDef++"\n"
             ++ "#define "++headerDef++"\n"
             ++ "\n"
             ++ "#include <stddef.h>\n"
             ++ "#include <stdint.h>\n"
             ++ "\n"
             ++ showComment (example^.withJets) (example^.text)
             ++ "extern const unsigned char "++example^.fullname++"[];\n"
             ++ "extern const size_t sizeof_"++example^.fullname++";\n"
             ++ "\n"
             ++ "/* The commitment Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
             ++ "extern const uint32_t "++example^.fullname++"_cmr[];\n"
             ++ "\n"
             ++ "/* The identity Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
             ++ "extern const uint32_t "++example^.fullname++"_imr[];\n"
             ++ "\n"
             ++ "/* The annotated Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
             ++ "extern const uint32_t "++example^.fullname++"_amr[];\n"
             ++ "\n"
             ++ "#endif\n"
 where
  headerDef = "SIMPLICITY_" ++ (toUpper <$> intercalate "_" (example^.path ++ [example^.name])) ++ "_H"

writeFiles example = do
 hPutStrLn stderr $ "Writing "++example^.name
 writeFile (example^.name++".h") (fileH example)
 writeFile (example^.name++".c") (fileC example)

main = do
  writeFiles example_hashBlock
  writeFiles schnorr0
  writeFiles schnorr6
  writeFiles checkSigHashAllTx1

noJetSubst :: (TyC a, TyC b) => Simplicity.Elements.Dag.NoJetDag a b -> WrappedSimplicity a b
noJetSubst = Simplicity.Elements.Dag.jetSubst

example_hashBlock :: ExampleNoJets (Hash, Block) Hash
example_hashBlock = Example
  { _name = "hashBlock"
  , _path = []
  , _text = [ "hashBlock"
            ]
  , _withJets = False
  , _prog = noJetSubst hashBlock
  }

schnorr0 :: ExampleProg
schnorr0 = Example
  { _name = "schnorr0"
  , _path = []
  , _text = [ "(scribe (toWord256 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9) &&&"
            , " zero word256) &&&"
            , " witness (toWord512 0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0) >>>"
            , "Simplicity.Programs.LibSecp256k1.Lib.bip_0340_verify"
            ]
  , _withJets = True
  , _prog = jetSubst
          $ (scribe (Arith.toWord256 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9) &&&
             Arith.zero Arith.word256) &&&
             witness (Arith.toWord512 0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0) >>>
            Simplicity.Programs.LibSecp256k1.Lib.bip_0340_verify
   }

schnorr6 :: ExampleProg
schnorr6 = Example
  { _name = "schnorr6"
  , _path = []
  , _text = [ "(scribe (toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) &&&"
            , " scribe (toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)) &&&"
            , " witness (toWord512 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2) >>>"
            , "Simplicity.Programs.LibSecp256k1.Lib.bip_0340_verify"
            ]
  , _withJets = True
  , _prog = jetSubst
          $ (scribe (Arith.toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) &&&
             scribe (Arith.toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)) &&&
             witness (Arith.toWord512 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2) >>>
            Simplicity.Programs.LibSecp256k1.Lib.bip_0340_verify
   }

checkSigHashAllTx1 :: ExampleProg
checkSigHashAllTx1 = Example
  { _name = "checkSigHashAllTx1"
  , _path = ["primitive", "elements"]
  , _text = [ "Simplicity.Programs.CheckSigHash.checkSigHash' Simplicity.Elements.Programs.CheckSigHashAll.Lib.hashAll"
            , "(Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)"
            , "(Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63"
            , "                                  0x" ++ sh s ++ ")"
            ]
  , _withJets = True
  , _prog = jetSubst
          $ Simplicity.Programs.CheckSigHash.checkSigHash' (unwrap hashMode)
            (Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)
            (Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
                                              s)
   }
 where
  sh v = replicate (64 - length s) '0' ++ s
   where
    s = Numeric.showHex v ""
  s = insecureSig . fromIntegral . Arith.fromWord256 $ msg
  Just msg = fastEval (Simplicity.Programs.CheckSigHash.sigHash libSha256 (unwrap hashMode)) env ()
  hashMode = jetSubst $ Simplicity.Elements.Programs.CheckSigHashAll.Lib.hashAll
  libSha256 = Simplicity.Programs.Sha256.lib
  Just env = primEnv tx1 0 undefined
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

insecureSig :: Word256 -> Word256
insecureSig msg = fromInteger ((toInteger k * (1 + e)) `mod` order)
 where
  order = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
  k :: Word256
  k = 1 + fromInteger order `div` 2
  px :: Word256
  px = 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
  e = integerHash256 . bsHash $ schnorrTag <> schnorrTag <> encode px <> encode px <> encode msg
  schnorrTag = encode . bsHash $ BSC.pack "BIP0340/challenge"
