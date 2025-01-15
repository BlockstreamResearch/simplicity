module GenPrimitives where

import Prelude hiding (sum)

import Control.Monad.Cont (Cont, cont, runCont)
import Data.Function (on)
import Data.Functor.Fixedpoint (Fix(..), cata)
import Data.List (intercalate, sortBy)
import Data.List.Split (chunksOf)
import Data.Maybe (isJust)
import qualified Data.Map as Map
import Numeric (showHex)

import NameWrangler
import Simplicity.Digest
import qualified Simplicity.Elements.Jets as Elements
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Weight

data JetInfo = JetInfo { name :: String
                       , cmr :: Hash256
                       , mw :: Integer
                       , sourceType :: Ty
                       , targetType :: Ty
                       }

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

cJetNode :: JetInfo -> String
cJetNode ji = unlines
  [ "[" ++ upperSnakeCase (name ji) ++ "] ="
  , "{ .tag = JET"
  , ", .jet = simplicity_" ++ lowerSnakeCase (name ji)
  , ", .cmr = {{" ++ showCHash (cmr ji) ++ "}}"
  , ", .sourceIx = " ++ compactCName (compactTy (sourceType ji)) ""
  , ", .targetIx = " ++ compactCName (compactTy (targetType ji)) ""
  , ", .cost = " ++ show (mw ji) ++ " /* milli weight units */"
  , "}"
  ]

mkTyList :: [JetInfo] -> [CompactTy]
mkTyList jetList = Map.keys . foldr combine wordMap $ (tys =<< jetList)
 where
  wordMap = Map.fromList [(CTyWord n, ty) | (n, ty) <- Prelude.take 32 words]
   where
    words = (1, sum one one) : [(2*n, prod ty ty) | (n, ty) <- words]
  tys ji = [sourceType ji, targetType ji]
  combine ty map | isJust (Map.lookup cTy map) = map
                 | otherwise = Map.insert cTy ty (foldr combine map (children ty))
   where
    cTy = compactTy ty
    children (Fix One) = []
    children (Fix (Sum x y)) = [x,y]
    children (Fix (Prod x y)) = [x,y]

cEnumTyFile :: [CompactTy] -> String
cEnumTyFile tyList = unlines . fmap item $ tyList
 where
  item ty@CTyOne = compactCName ty " = 0,"
  item ty@(CTyWord n) = compactCName ty " = " ++ show (1 + ln n) ++ ","
  item ty = compactCName ty ","
  ln n = length . Prelude.drop 1 . takeWhile (0 <) $ iterate (`div` 2) n

cInitializeTyFile :: [CompactTy] -> String
cInitializeTyFile tyList = unlines $ cInitializeTy <$> tyList

cEnumJetFile :: [JetInfo] -> String
cEnumJetFile jetList = unlines $ map f jetList
 where
  f ji = (upperSnakeCase (name ji)) ++ ","

cJetNodeFile :: [JetInfo] -> String
cJetNodeFile jetList = intercalate "," $ map cJetNode jetList

writeIncludeFile :: FilePath -> String -> IO ()
writeIncludeFile name content = writeFile name (header ++ content)
 where
  header = "/* This file has been automatically generated. */\n"

mkJetList :: (a -> JetInfo) -> [a] -> [JetInfo]
mkJetList f l = sortBy (compare `on` name) . map f $ l

writeFiles list = do
  writeIncludeFile ("primitiveEnumTy.inc") (cEnumTyFile tyList)
  writeIncludeFile ("primitiveInitTy.inc") (cInitializeTyFile tyList)
  writeIncludeFile ("primitiveEnumJet.inc") (cEnumJetFile list)
  writeIncludeFile ("primitiveJetNode.inc") (cJetNodeFile list)
 where
  tyList = mkTyList list

main = do
  writeFiles elementsJetList
 where
  elementsJetList = mkJetList fromElements $ Map.elems Elements.jetMap
  fromElements :: SomeArrow Elements.JetType -> JetInfo
  fromElements (SomeArrow jt) = JetInfo { name = mkName jt
                                        , cmr = commitmentRoot (Elements.asJet jt)
                                        , mw = milliWeight (Elements.jetCost jt)
                                        , sourceType = unreflect tyx
                                        , targetType = unreflect tyy
                                        }
   where
    (tyx, tyy) = reifyArrow jt
