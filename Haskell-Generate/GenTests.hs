{-# LANGUAGE KindSignatures, ScopedTypeVariables #-}
module GenTests where

import Prelude hiding (drop, take)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Char (toUpper)
import Data.Functor.Identity (runIdentity)
import Data.Maybe (fromJust)
import Data.Kind (Type)
import Data.List (intercalate)
import Data.List.Split (chunksOf)
import Data.Serialize (encode, runPut)
import Data.Vector (fromList)
import Numeric (showHex)
import System.IO (hPutStrLn, stderr)
import Lens.Family2 ((^.), (&), (.~), over, review, to, Getter')
import Lens.Family2.Stock (mapped)

import Simplicity.Digest
import qualified Simplicity.Elements.JetType
import qualified Simplicity.Elements.Dag
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Dag (SimplicityDag)
import Simplicity.Elements.Inference
import Simplicity.Elements.Primitive
import Simplicity.Elements.Jets (JetType, WrappedSimplicity, fastEval, jetSubst, pruneSubst, unwrap)
import Simplicity.Elements.Serialization.BitString
import Simplicity.Elements.StaticAnalysis.Cost
import qualified Simplicity.Elements.Programs.SigHash.Lib
import Simplicity.Elements.Term
import qualified Simplicity.LibSecp256k1.Spec
import Simplicity.MerkleRoot
import Simplicity.Programs.Generic
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Sha256
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib
import qualified Simplicity.Programs.CheckSig.Lib
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Word

data Example (jt :: Type -> Type -> Type)
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
  start = ["const unsigned char "++name++"[] = " ++ open]
  open | null bin = "\"\";"
       | otherwise = "{"
  finish = close ++ ["", "const size_t sizeof_"++name++" = "++sizeof++";"]
  close | null bin = []
        | otherwise = ["};"]
  sizeof | null bin = "0"
         | otherwise = "sizeof("++name++")"
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
        ++ showBinary (example^.fullname) binP
        ++ showBinary (example^.fullname++"_witness") binW
        ++ "\n"
        ++ "/* The commitment Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_cmr") cmr
        ++ "\n"
        ++ "/* The identity Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_imr") imr
        ++ "\n"
        ++ "/* The annotated Merkle root of the above "++example^.fullname++" Simplicity expression. */\n"
        ++ showHash (example^.fullname++"_amr") amr
        ++ "\n"
        ++ "/* The cost of the above "++example^.fullname++" Simplicity expression in milli weight units. */\n"
        ++ "const ubounded "++example^.fullname++"_cost = "++ (if cost < 2^32 then show cost else "UBOUNDED_MAX") ++";\n"
 where
  (program,witness) = putTermLengthCode (unwrap (example^.prog) :: Simplicity.Elements.Dag.JetDag jt a b)
  binP = BS.unpack . runPut $ putBitStream program
  binW = BS.unpack . runPut $ putBitStream witness
  cmr = commitmentRoot . unwrap $ example^.prog
  imr = identityRoot . unwrap $ example^.prog
  amr = annotatedRoot . unwrap $ example^.prog
  cost = milliWeigh . unwrap $ example^.prog

fileH example = "#ifndef "++headerDef++"\n"
             ++ "#define "++headerDef++"\n"
             ++ "\n"
             ++ "#include <stddef.h>\n"
             ++ "#include <stdint.h>\n"
             ++ "#include \""++concat (replicate (length (example^.path)) "../")++"bounded.h\"\n"
             ++ "\n"
             ++ showComment (example^.withJets) (example^.text)
             ++ "extern const unsigned char "++example^.fullname++"[];\n"
             ++ "extern const size_t sizeof_"++example^.fullname++";\n"
             ++ "extern const unsigned char "++example^.fullname++"_witness[];\n"
             ++ "extern const size_t sizeof_"++example^.fullname++"_witness;\n"
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
             ++ "/* The cost of the above "++example^.fullname++" Simplicity expression in milli weight units. */\n"
             ++ "extern const ubounded "++example^.fullname++"_cost;\n"
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
  writeFiles ctx8Unpruned
  writeFiles ctx8Pruned
  writeFiles schnorr0
  writeFiles schnorr6
  writeFiles checkSigHashAllTx1
  writeRegression4
  writeFiles typeSkipTest

noJetSubst :: (TyC a, TyC b) => Simplicity.Elements.Dag.NoJetDag a b -> WrappedSimplicity a b
noJetSubst = Simplicity.Elements.Dag.jetSubst

noJetPrune :: (TyC a, TyC b) => PrimEnv -> a -> Simplicity.Elements.Dag.NoJetDag a b -> Maybe (WrappedSimplicity a b)
noJetPrune env a prog = Simplicity.Elements.Dag.pruneSubst prog env a

example_hashBlock :: ExampleNoJets (Hash, Block) Hash
example_hashBlock = Example
  { _name = "hashBlock"
  , _path = []
  , _text = [ "hashBlock"
            ]
  , _withJets = False
  , _prog = noJetSubst hashBlock
  }

ctx8Unpruned :: ExampleNoJets () ()
ctx8Unpruned = Example
  { _name = "ctx8Unpruned"
  , _path = []
  , _text = [ "(scribe (toWord256 0x067C531269735CA7F541FDACA8F0DC76305D3CADA140F89372A410FE5EFF6E4D) &&&"
            , " (ctx8Init &&& scribe (toWord128 0xDE188941A3375D3A8A061E67576E926D)) >>> ctx8Addn vector16 >>> ctx8Finalize) >>>"
            , "eq >>> verify"
            ]
  , _withJets = False
  , _prog = noJetSubst
          $ (scribe (Arith.toWord256 0x067C531269735CA7F541FDACA8F0DC76305D3CADA140F89372A410FE5EFF6E4D) &&&
              ((ctx8Init &&& scribe (Arith.toWord128 0xDE188941A3375D3A8A061E67576E926D)) >>> ctx8Addn Arith.vector16 >>> ctx8Finalize)) >>>
            eq >>> verify
  }

ctx8Pruned :: ExampleNoJets () ()
ctx8Pruned = Example
  { _name = "ctx8Pruned"
  , _path = []
  , _text = [ "(scribe (toWord256 0x067C531269735CA7F541FDACA8F0DC76305D3CADA140F89372A410FE5EFF6E4D) &&&"
            , " (ctx8Init &&& scribe (toWord128 0xDE188941A3375D3A8A061E67576E926D)) >>> ctx8Addn vector16 >>> ctx8Finalize) >>>"
            , "eq >>> verify"
            ]
  , _withJets = False
  , _prog = prog
  }
 where
  Just prog = noJetPrune undefined ()
            $ (scribe (Arith.toWord256 0x067C531269735CA7F541FDACA8F0DC76305D3CADA140F89372A410FE5EFF6E4D) &&&
                ((ctx8Init &&& scribe (Arith.toWord128 0xDE188941A3375D3A8A061E67576E926D)) >>> ctx8Addn Arith.vector16 >>> ctx8Finalize)) >>>
              eq >>> verify

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
  , _text = [ "Simplicity.Programs.CheckSig.Lib.checkSigVerify' Simplicity.Elements.Programs.SigHash.Lib.sigAllHash"
            , "(Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)"
            , "(Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63"
            , "                                  0x" ++ sh s ++ ")"
            ]
  , _withJets = True
  , _prog = prunedProg
          $ (Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
                                              s)
   }
 where
  pk = Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
  program sig = jetSubst $ Simplicity.Programs.CheckSig.Lib.checkSigVerify' (unwrap hashMode) pk sig
  prunedProg sig = fromJust $ pruneSubst (Simplicity.Programs.CheckSig.Lib.checkSigVerify' (unwrap hashMode) pk sig) env
  sh v = replicate (64 - length s) '0' ++ s
   where
    s = Numeric.showHex v ""
  s = insecureSig . fromIntegral . Arith.fromWord256 $ msg
  Just msg = fastEval (Simplicity.Programs.CheckSig.Lib.sigHash' (unwrap hashMode)) env ()
  hashMode = jetSubst $ Simplicity.Elements.Programs.SigHash.Lib.sigAllHash
  genesis = review (over be256) 0x0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206
  Just env = primEnv tx1 0 tapEnv genesis
  cmr = commitmentRoot . unwrap $ program (Simplicity.LibSecp256k1.Spec.Sig 0 0)
  tapEnv = TapEnv { tapleafVersion = 0xbe
                  , tapInternalKey = pk
                  , tappath = []
                  , tapScriptCMR = cmr
                  }
  tx1 = SigTx
        { sigTxVersion = 0x00000002
        , sigTxIn = fromList [input0]
        , sigTxOut = fromList [output0, output1]
        , sigTxLock = 0
        }
   where
    assetId = Asset . Explicit $ review (over be256) 0x230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2
    input0 = SigTxInput
      { sigTxiPegin = Nothing
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

writeRegression4 = do
  hPutStrLn stderr $ "Writing regression4"
  writeFile "regression4.h" regression4H
  writeFile "regression4.c" regression4C
 where
  regression4Bin = BS.unpack . runPut . Simplicity.Serialization.putBitStream . putDagNoWitnessLengthCode $ code
   where
    -- We bypass the requirement for type annotations since they are expensive to compute and are not actually need for serialization.
    -- I promise the term we are generating is in fact well typed (with very large types that GHC doesn't particularly like to process).
    code :: SimplicityDag [] Ty (SomeArrow Simplicity.Elements.JetType.NoJets) UntypedValue
    code = (uWitness OneV : f 15 ++ [uComp (3*2^16) 1]) & (mapped.tyAnnotation) .~ bypassTyping
     where
      f 0 = [uIden, uTake 1, uIden, uDrop 1, uComp 3 1]
      f n = rec ++ rec ++ [uComp (3*2^n) 1]
       where
        rec = f (n-1)
    bypassTyping = undefined
  regression4Src = [
   "uWitness OneV : f 15 ++ [uComp (3*2^16) 1]",
   " where",
   "  f 0 = [uIden, uTake 1, uIden, uDrop 1, uComp 3 1]",
   "  f n = rec ++ rec ++ [uComp (3*2^n) 1]",
   "   where",
   "    rec = f (n-1)"]
  regression4C =
           "#include \"regression4.h\"\n"
        ++ "\n"
        ++ showComment False regression4Src
        ++ showBinary "regression4" regression4Bin
  regression4H = "#ifndef "++headerDef++"\n"
              ++ "#define "++headerDef++"\n"
              ++ "\n"
              ++ "#include <stddef.h>\n"
              ++ "#include <stdint.h>\n"
              ++ "#include \"bounded.h\"\n"
              ++ "\n"
              ++ showComment False regression4Src
              ++ "extern const unsigned char "++"regression4"++"[];\n"
              ++ "extern const size_t sizeof_"++"regression4"++";\n"
              ++ "\n"
              ++ "#endif\n"
    where
     headerDef = "SIMPLICITY_" ++ (toUpper <$> "regression4") ++ "_H"

typeSkipTest :: ExampleNoJets () ()
typeSkipTest = Example
  { _name = "typeSkipTest"
  , _path = []
  , _text = [ "witness (runIdentity (getValue (return True))) >>> mn >>> unit"
            , " where"
            , "  l1 = take l0 &&& drop l0"
            , "  l2 = take l1 &&& drop l1"
            , "  l3 = take l2 &&& drop l2"
            , "  ltop = l3"
            , "  m1 = copair l3 l3"
            , "  m2 = take l1 &&& drop m1"
            , "  m3 = take m2 &&& drop l2"
            , "  m4 = take l3 &&& drop m3"
            , "  m5 = copair (injl m4) (injr ltop)"
            , "  m6 = take l1 &&& drop m5"
            , "  m7 = take m6 &&& drop l2"
            , "  m8 = take l3 &&& drop m7"
            , "  n1 = copair l3 l3"
            , "  n2 = take n1 &&& drop l1"
            , "  n3 = take l2 &&& drop n2"
            , "  n4 = take n3 &&& drop l3"
            , "  n5 = copair (injl ltop) (injr n4)"
            , "  n6 = take n5 &&& drop l0"
            , "  n7 = take l1 &&& drop n6"
            , "  n8 = take n7 &&& drop l2"
            , "  mn = copair (injl m8) (injr n8)"
            ]
  , _withJets = False
  , _prog = prog
  }
 where
  l0 = iden :: (Core term) => term () ()
  l1 = take l0 &&& drop l0
  l2 = take l1 &&& drop l1
  l3 = take l2 &&& drop l2
  ltop = l3
  m1 = copair l3 l3
  m2 = take l1 &&& drop m1
  m3 = take m2 &&& drop l2
  m4 = take l3 &&& drop m3
  m5 = copair (injl m4) (injr ltop)
  m6 = take m5 &&& drop l0
  m7 = take l1 &&& drop m6
  m8 = take m7 &&& drop l2
  n1 = copair l3 l3
  n2 = take n1 &&& drop l1
  n3 = take l2 &&& drop n2
  n4 = take n3 &&& drop l3
  n5 = copair (injl ltop) (injr n4)
  n6 = take l0 &&& drop n5
  n7 = take n6 &&& drop l1
  n8 = take l2 &&& drop n7
  mn = copair (injl m8) (injr n8)
  Just prog = noJetPrune undefined ()
            $ witness (runIdentity (getValue (return True))) >>> mn >>> unit
