module GenPrimitives where

import Prelude hiding (sum)

import Control.Monad.Cont (Cont, cont, runCont)
import Data.Char (isAlphaNum, isDigit, isUpper, toLower, toUpper)
import Data.Function (on)
import Data.Functor.Fixedpoint (Fix(..), cata)
import Data.List (groupBy, intercalate, sortBy)
import Data.List.Split (chunksOf, condense, dropInitBlank, keepDelimsL, split, whenElt)
import Data.Maybe (isJust)
import qualified Data.Map as Map
import Numeric (showHex)

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
  , "}"
  ]
 where
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
