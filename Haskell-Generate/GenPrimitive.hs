module GenPrimitives where

import Prelude hiding (sum)

import Control.Monad.Cont (Cont, cont, runCont)
import Data.Char (isAlphaNum, isDigit, isUpper, toLower, toUpper)
import Data.Fixed (Fixed(MkFixed))
import Data.Function (on)
import Data.Functor.Fixedpoint (Fix(..), cata)
import Data.List (groupBy, intercalate, sortBy)
import Data.List.Split (chunksOf, condense, dropInitBlank, keepDelimsL, split, whenElt)
import Data.Maybe (isJust)
import qualified Data.Map as Map
import Numeric (showHex)

import Simplicity.BitMachine.StaticAnalysis.Cost
import Simplicity.Digest
import Simplicity.Elements.Jets
import Simplicity.Elements.Term
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Ty

-- :TODO: This tool should probably be moved to Simplicity.Serialization for general use.
enumerate :: (Cont (DList a) void -> Cont (DList a) Bool -> Cont (DList a) a) -> [a]
enumerate tree = runCont (tree end branch) (:) []
 where
  end = cont $ \k -> id
  branch = cont $ \k -> k False . k True

jetList :: [SomeArrow JetType]
jetList = sortBy (compare `on` name) $ Map.elems jetMap
 where
  name (SomeArrow j) = jetName j

snakeCase :: String -> String
snakeCase str = intercalate "_" . groupSingles $ (split . keepDelimsL . dropInitBlank . whenElt) isUpper =<< splitDigit
 where
  splitDigit = (split . condense . whenElt) isDigit $ str
  groupSingles = map concat . groupBy singles
   where
    singles x y = null (tail x) && null (tail y)

upperSnakeCase :: String -> String
upperSnakeCase = map toUpper . snakeCase

lowerSnakeCase :: String -> String
lowerSnakeCase = map toLower . snakeCase

data CompactTy = CTyOne
               | CTyWord Int
               | CTyMaybe CompactTy
               | CTySum CompactTy CompactTy
               | CTyProd CompactTy CompactTy
     deriving (Eq, Ord)

showCHash h = intercalate ", " (format <$> chunksOf 8 str_h)
 where
  format x = "0x" ++ x ++ "u"
  str_h = padding ++ text
   where
    padding = replicate (64 - length text) '0'
    text = showHex (integerHash256 h) ""

compactTy :: Ty -> CompactTy
compactTy = cata go -- memoCataTy go
 where
  go One = CTyOne
  go (Sum CTyOne CTyOne) = CTyWord 1
  go (Sum CTyOne y) = CTyMaybe y
  go (Sum x y) = CTySum x y
  go (Prod (CTyWord wx) (CTyWord wy)) | wx == wy = CTyWord (wx + wy)
  go (Prod x y) = CTyProd x y

compactCName :: CompactTy -> ShowS
compactCName s = showString "ty_" . go s
 where
  go CTyOne = showString "u"
  go (CTyWord 1) = showString "b"
  go (CTyWord n) | n < 2^10 = showString "w" . shows n
                 | n < 2^20 = showString "w" . shows (n `div` (2^10)) . showString "Ki"
                 | n < 2^30 = showString "w" . shows (n `div` (2^20)) . showString "Mi"
                 | otherwise = showString "w" . shows (n `div` (2^30)) . showString "Gi"
  go (CTyMaybe x) = showString "m" . go x
  go (CTySum x y) = showString "s" . go x . go y
  go (CTyProd x y) = showString "p" . go x . go y

cInitializeTy :: CompactTy -> String
cInitializeTy ty = showString "(*bound_var)[" . compactCName ty
                 . showString "] = (unification_var){ .isBound = true, .bound = " . cBoundTy ty
                 . showString "};"
                 $ ""
 where
  cBoundTy CTyOne = showString "{ .kind = ONE }"
  cBoundTy (CTyWord 1) = cBoundTy (CTySum CTyOne CTyOne)
  cBoundTy (CTyWord n) = cBoundTy (CTyProd rec rec)
   where
    rec = CTyWord (n `div` 2)
  cBoundTy (CTyMaybe x) = cBoundTy (CTySum CTyOne x)
  cBoundTy (CTySum x y) = showString "{ .kind = SUM, .arg = { &(*bound_var)[" . compactCName x
                        . showString "], &(*bound_var)[" . compactCName y
                        . showString "] } }"
  cBoundTy (CTyProd x y) = showString "{ .kind = PRODUCT, .arg = { &(*bound_var)[" . compactCName x
                         . showString "], &(*bound_var)[" . compactCName y
                         . showString "] } }"

cJetNode :: (TyC x, TyC y) => String -> JetType x y -> String
cJetNode name jt = unlines
  [ "[" ++ upperSnakeCase name ++ "] ="
  , "{ .tag = JET"
  , ", .jet = " ++ lowerSnakeCase name
  , ", .cmr = {{" ++ showCHash (commitmentRoot (jet (specification jt))) ++ "}}"
  , ", .sourceIx = " ++ compactCName (compactTy (unreflect tyx)) ""
  , ", .targetIx = " ++ compactCName (compactTy (unreflect tyy)) ""
  , ", .cost = " ++ show costRep ++ " /* milli weight units */"
  , "}"
  ]
 where
  MkFixed costRep = cost name
  (tyx, tyy) = reifyArrow jt

jetName :: JetType x y -> String
jetName = filter isAlphaNum . last . words . show

tyList :: [CompactTy]
tyList = Map.keys . foldr combine wordMap $ (tys =<< jetList)
 where
  wordMap = Map.fromList [(CTyWord n, ty) | (n, ty) <- Prelude.take 32 words]
   where
    words = (1, sum one one) : [(2*n, prod ty ty) | (n, ty) <- words]
  tys (SomeArrow jet) = [unreflect x, unreflect y]
   where
    (x,y) = reifyArrow jet
  combine ty map | isJust (Map.lookup cTy map) = map
                 | otherwise = Map.insert cTy ty (foldr combine map (children ty))
   where
    cTy = compactTy ty
    children (Fix One) = []
    children (Fix (Sum x y)) = [x,y]
    children (Fix (Prod x y)) = [x,y]

cEnumTyFile :: String
cEnumTyFile = unlines . fmap item $ tyList
 where
  item ty@CTyOne = compactCName ty " = 0,"
  item ty@(CTyWord n) = compactCName ty " = " ++ show (1 + ln n) ++ ","
  item ty = compactCName ty ","
  ln n = length . tail . takeWhile (0 <) $ iterate (`div` 2) n

cInitializeTyFile :: String
cInitializeTyFile = unlines $ cInitializeTy <$> tyList

cEnumJetFile :: String
cEnumJetFile = unlines $ map f jetList
 where
  f (SomeArrow jet) = (upperSnakeCase . jetName $ jet) ++ ","

cJetNodeFile :: String
cJetNodeFile = intercalate "," $ map f jetList
 where
  f (SomeArrow jet) = cJetNode (jetName jet) jet

writeIncludeFile :: FilePath -> String -> IO ()
writeIncludeFile name content = writeFile name (header ++ content)
 where
  header = "/* This file has been automatically generated. */\n"

main = do
  writeIncludeFile "primitiveEnumTy.inc" cEnumTyFile
  writeIncludeFile "primitiveInitTy.inc" cInitializeTyFile
  writeIncludeFile "primitiveEnumJet.inc" cEnumJetFile
  writeIncludeFile "primitiveJetNode.inc" cJetNodeFile


-- :TODO: Move jet costs to within the jet's specifications.
-- These values are from <https://gist.githubusercontent.com/sanket1729/0bf92ab9b2d17895d4afdfe3a85bdf70/raw/a0c8cf0f08e07945d8fcc04640bf567a9ba9f368/jet_benches.json>
rawBenchmark :: String -> Double
rawBenchmark "Add32" = 60.6159814446884
rawBenchmark "AnnexHash" = 211.09026343236047
rawBenchmark "AssetAmountHash" = 180.8254919736737
rawBenchmark "Bip0340Verify" = 45984.13321032714
rawBenchmark "BuildTapbranch" = 1435.412867661228
rawBenchmark "BuildTapleafSimplicity" = 1015.4756900209926
rawBenchmark "CalculateAsset" = 360.06007299543614
rawBenchmark "CalculateConfidentialToken" = 350.8989606414178
rawBenchmark "CalculateExplicitToken" = 348.558227539948
rawBenchmark "CalculateIssuanceEntropy" = 1615.3358870703569
rawBenchmark "CheckLockDistance" = 76.17692580261182
rawBenchmark "CheckLockDuration" = 82.56209366173621
rawBenchmark "CheckLockHeight" = 53.39333721048194
rawBenchmark "CheckLockTime" = 43.33177031077567
rawBenchmark "CheckSigVerify" = 45317.78400574591
rawBenchmark "CurrentAmount" = 135.78732293160343
rawBenchmark "CurrentAnnexHash" = 58.0203752897563
rawBenchmark "CurrentAsset" = 71.80146032912744
rawBenchmark "CurrentIndex" = 26.943694312350118
rawBenchmark "CurrentIssuanceAssetAmount" = 60.15236323350894
rawBenchmark "CurrentIssuanceAssetProof" = 58.69505263721878
rawBenchmark "CurrentIssuanceTokenAmount" = 57.88357975346324
rawBenchmark "CurrentIssuanceTokenProof" = 64.85132714583088
rawBenchmark "CurrentNewIssuanceContract" = 66.56515141152202
rawBenchmark "CurrentPegin" = 54.45051148992831
rawBenchmark "CurrentPrevOutpoint" = 54.691581509829085
rawBenchmark "CurrentReissuanceBlinding" = 90.7476615079706
rawBenchmark "CurrentReissuanceEntropy" = 33.30636781763847
rawBenchmark "CurrentScriptHash" = 85.52894572950431
rawBenchmark "CurrentScriptSigHash" = 246.03219697098845
rawBenchmark "CurrentSequence" = 66.709044658464
rawBenchmark "Decompress" = 5063.4349045984945
rawBenchmark "Eq256" = 69.6319118898475
rawBenchmark "Eq32" = 31.290935557610673
rawBenchmark "FeAdd" = 638.4705854453882
rawBenchmark "FeInvert" = 1816.4543078142224
rawBenchmark "FeIsOdd" = 141.26751532118217
rawBenchmark "FeIsZero" = 135.7335653472474
rawBenchmark "FeMultiply" = 502.6515061676853
rawBenchmark "FeMultiplyBeta" = 342.5283243289971
rawBenchmark "FeNegate" = 991.5229432627041
rawBenchmark "FeNormalize" = 1211.064013872284
rawBenchmark "FeSquare" = 362.5923855673133
rawBenchmark "FeSquareRoot" = 5762.70977938353
rawBenchmark "FullAdd32" = 42.46377799498269
rawBenchmark "FullMultiply32" = 62.64401083252537
rawBenchmark "FullSubtract32" = 47.56906525614555
rawBenchmark "GeIsOnCurve" = 348.3597036875192
rawBenchmark "GejAdd" = 1484.0743539425114
rawBenchmark "GejDouble" = 860.8679720044591
rawBenchmark "GejGeAdd" = 1361.790763671032
rawBenchmark "GejGeAddEx" = 1351.3040959587274
rawBenchmark "GejInfinity" = 472.28466266578215
rawBenchmark "GejIsInfinity" = 684.0069105380625
rawBenchmark "GejIsOnCurve" = 582.937187897334
rawBenchmark "GejNegate" = 723.6308629543321
rawBenchmark "GejNormalize" = 2688.076048829166
rawBenchmark "GejRescale" = 1115.9092245996635
rawBenchmark "GejXEquiv" = 627.1357118277799
rawBenchmark "GejYIsOdd" = 2495.366803492532
rawBenchmark "Generate" = 22217.525816706173
rawBenchmark "GenesisBlockHash" = 64.96301577240887
rawBenchmark "InputAmount" = 84.25074431546687
rawBenchmark "InputAmountsHash" = 62.90341332524756
rawBenchmark "InputAnnexHash" = 40.717761633839
rawBenchmark "InputAnnexesHash" = 57.08070819406762
rawBenchmark "InputAsset" = 65.568941550965
rawBenchmark "InputOutpointsHash" = 64.23301319040051
rawBenchmark "InputPegin" = 73.82455366301573
rawBenchmark "InputPrevOutpoint" = 61.75422274355804
rawBenchmark "InputScriptHash" = 68.91661586480123
rawBenchmark "InputScriptSigHash" = 71.01947453165256
rawBenchmark "InputScriptSigsHash" = 50.32728144624912
rawBenchmark "InputScriptsHash" = 71.07590989205612
rawBenchmark "InputSequence" = 40.74153753011921
rawBenchmark "InputSequencesHash" = 53.14463770651002
rawBenchmark "InputUtxosHash" = 59.594590802897216
rawBenchmark "InputsHash" = 52.03522476418275
rawBenchmark "InternalKey" = 49.360660535021914
rawBenchmark "Issuance" = 40.36971531924246
rawBenchmark "IssuanceAsset" = 67.83792138503796
rawBenchmark "IssuanceAssetAmount" = 64.50197080397984
rawBenchmark "IssuanceAssetAmountsHash" = 58.434775552125764
rawBenchmark "IssuanceAssetProof" = 60.50267471753845
rawBenchmark "IssuanceBlindingEntropyHash" = 64.6120836335202
rawBenchmark "IssuanceEntropy" = 75.06754370982935
rawBenchmark "IssuanceRangeProofsHash" = 63.57596008346966
rawBenchmark "IssuanceToken" = 80.10970404683115
rawBenchmark "IssuanceTokenAmount" = 69.11506740950209
rawBenchmark "IssuanceTokenAmountsHash" = 65.16073770335794
rawBenchmark "IssuanceTokenProof" = 63.14717417723799
rawBenchmark "IssuancesHash" = 56.467277855746325
rawBenchmark "Le32" = 44.823937142311
rawBenchmark "LinearCombination1" = 37667.09003695679
rawBenchmark "LinearVerify1" = 45129.002460662145
rawBenchmark "LockTime" = 27.075342321136212
rawBenchmark "Low32" = 26.155833867985073
rawBenchmark "Multiply32" = 39.62575760071405
rawBenchmark "NewIssuanceContract" = 87.44883721313728
rawBenchmark "NonceHash" = 196.56918660128488
rawBenchmark "NumInputs" = 27.44542347798504
rawBenchmark "NumOutputs" = 27.55320961734872
rawBenchmark "One32" = 24.314395226795472
rawBenchmark "OutpointHash" = 193.52390419231392
rawBenchmark "OutputAmount" = 75.43690788484608
rawBenchmark "OutputAmountsHash" = 57.734313912975324
rawBenchmark "OutputAsset" = 64.75607364850906
rawBenchmark "OutputNonce" = 33.83110327628045
rawBenchmark "OutputNoncesHash" = 50.583557172857006
rawBenchmark "OutputNullDatum" = 33.317612557677165
rawBenchmark "OutputRangeProof" = 105.66870802854868
rawBenchmark "OutputRangeProofsHash" = 50.731305808111074
rawBenchmark "OutputScriptHash" = 59.34351248712303
rawBenchmark "OutputScriptsHash" = 55.65029299370546
rawBenchmark "OutputSurjectionProof" = 57.920079192381756
rawBenchmark "OutputSurjectionProofsHash" = 74.05696868481724
rawBenchmark "OutputsHash" = 61.74547699660735
rawBenchmark "ParseLock" = 38.32941955601188
rawBenchmark "ParseSequence" = 37.50898314676539
rawBenchmark "PointVerify1" = 50895.23664612757
rawBenchmark "ReissuanceBlinding" = 37.555991151364154
rawBenchmark "ReissuanceEntropy" = 81.56440555844729
rawBenchmark "ScalarAdd" = 390.8726585535597
rawBenchmark "ScalarInvert" = 1746.3653514528473
rawBenchmark "ScalarIsZero" = 146.73796351898312
rawBenchmark "ScalarMultiply" = 485.1550512606823
rawBenchmark "ScalarMultiplyLambda" = 333.54205709012706
rawBenchmark "ScalarNegate" = 329.1323762948011
rawBenchmark "ScalarNormalize" = 335.58841346624416
rawBenchmark "ScalarSquare" = 372.72648339635964
rawBenchmark "Scale" = 34196.16016272863
rawBenchmark "ScriptCMR" = 50.29201395140244
rawBenchmark "Sha256Block" = 474.2694106173987
rawBenchmark "Sha256Ctx8Add1" = 205.99278770855858
rawBenchmark "Sha256Ctx8Add128" = 181.94035682870015
rawBenchmark "Sha256Ctx8Add16" = 154.12659513074527
rawBenchmark "Sha256Ctx8Add2" = 261.10144176151067
rawBenchmark "Sha256Ctx8Add256" = 259.51549364207773
rawBenchmark "Sha256Ctx8Add32" = 148.00802779890535
rawBenchmark "Sha256Ctx8Add4" = 258.4149137787725
rawBenchmark "Sha256Ctx8Add512" = 253.48113361788356
rawBenchmark "Sha256Ctx8Add64" = 215.63560733166457
rawBenchmark "Sha256Ctx8Add8" = 149.7601977392873
rawBenchmark "Sha256Ctx8AddBuffer511" = 186.8994081833699
rawBenchmark "Sha256Ctx8Finalize" = 546.2874650262119
rawBenchmark "Sha256Ctx8Init" = 107.71853051225241
rawBenchmark "Sha256Iv" = 48.53710248693044
rawBenchmark "SigAllHash" = 61.485988196529846
rawBenchmark "Subtract32" = 49.566418503347194
rawBenchmark "TapEnvHash" = 61.6463308739367
rawBenchmark "Tapbranch" = 42.91777089161113
rawBenchmark "TapbranchHash" = 62.06883735075261
rawBenchmark "TapleafHash" = 53.427243769277354
rawBenchmark "TapleafVersion" = 36.45363554727459
rawBenchmark "TxHash" = 74.19539621273046
rawBenchmark "TxIsFinal" = 30.608813255218468
rawBenchmark "TxLockDistance" = 32.98348877646163
rawBenchmark "TxLockDuration" = 28.951169045157723
rawBenchmark "TxLockHeight" = 32.48502494409075
rawBenchmark "TxLockTime" = 27.757312699406825
rawBenchmark "Verify" = 20.46853995788889
rawBenchmark "Version" = 79.99308762988846
rawBenchmark "GeNegate" = 723.6308629543321 -- :TODO: This value is missing.  Using made-up value instead.
rawBenchmark str = error $ "rawBenchmark missing " ++ str ++ "."

-- benchmark adjusts the raw benchmark by giving a discount to batch verifiable jets.
benchmark :: String -> Double
benchmark jetName = rawBenchmark jetName * adjustment
 where
  batchable = ["LinearVerify1", "PointVerify1", "CheckSigVerify", "Bip0340Verify"]
  adjustment | jetName `elem` batchable = 0.5
             | otherwise = 1

-- Normalized cost where cost "CheckSigVerify" = 50 Weight.
cost :: String -> Weight
cost jetName = realToFrac $ benchmark jetName * factor
 where
  factor = 50 / benchmark "CheckSigVerify"