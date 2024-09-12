-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Ty.Arbitrary ( maybeToTy
                               , HashElement(..), heAsTy, heAsSpec, toHE
                               , FieldElement(..), feAsTy, feAsSpec, toFE
                               , GroupElement(..), geAsTy, geAsSpec, toGE
                               , PointElement(..), pointAsTy, pointAsSpec, toPoint
                               , GroupElementJacobian(..), gejAsTy, gejAsSpec, toGEJ
                               , gen_inf, gen_half_curve, gen_half_curve_jacobian, gen_half_curve_inf
                               , ScalarElement(..), scalarAsTy, scalarAsSpec, toScalar
                               , WnafElement(..), wnafAsTy, traverseWnaf
                               , Sha256CtxElement(..), ctxAsTy, ctxAsSpec, toCtx
                               ) where

import qualified Data.ByteString as BS
import Lens.Family2 (review, over)
import Lens.Family2.Stock (both_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.+.), (.*.), (.^.))
import qualified Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.Programs.LibSecp256k1.Lib
import Simplicity.Ty.LibSecp256k1
import Simplicity.Ty.Word
import qualified Simplicity.Word as W

import Test.Tasty.QuickCheck (Arbitrary(..), Gen
                             , arbitraryBoundedIntegral, arbitrarySizedBoundedIntegral
                             , choose, elements, frequency, resize, sized, oneof, vectorOf
                             , shrinkIntegral
                             )

maybeToTy :: Maybe a -> Either () a
maybeToTy Nothing = Left ()
maybeToTy (Just x) = Right x

toW8 :: W.Word8 -> Word8
toW8 = toWord8 . fromIntegral

toW64 :: W.Word64 -> Word64
toW64 = toWord64 . fromIntegral

instance Arbitrary W.Word256 where
  arbitrary = arbitrarySizedBoundedIntegral
  shrink = shrinkIntegral

data HashElement = HashElement W.Word256 deriving Show

instance Arbitrary HashElement where
  arbitrary = do
    b <- arbitrary
    i <- arbitrarySizedBoundedIntegral
    return . HashElement $ if b then i else -i
  shrink (HashElement h) = HashElement <$> takeWhile (<h) [0, 1, 2^248, 2^255, 2^256-1]

heAsTy (HashElement h) = toWord256 (toInteger h)
heAsSpec (HashElement h) = review (over be256) h

toHE :: Hash256 -> Word256
toHE = toWord256 .integerHash256

genModularWord256 :: W.Word256 -> Gen W.Word256
genModularWord256 w = do
  b <- arbitrary
  i <- arbitrary
  return $ fromInteger i + if b then w else 0

data FieldElement = FieldElement W.Word256 deriving Show

instance Arbitrary FieldElement where
  arbitrary = FieldElement <$> genModularWord256 (fromInteger Spec.fieldOrder)
  shrink (FieldElement fe) = FieldElement <$> takeWhile (<fe) [0, 1, order - 1, order, order + 1]
   where
    order = fromInteger Spec.fieldOrder

feAsTy (FieldElement w) = toWord256 (toInteger w)
feAsSpec (FieldElement w) = Spec.fe (toInteger w)

data GroupElement = GroupElement FieldElement FieldElement deriving Show

lowOrderGE :: Gen GroupElement
lowOrderGE = elements (mkGE <$> [Spec.ge_3, Spec.ge_6, Spec.ge_7, Spec.ge_13, Spec.ge_14])
 where
  mkGE (Spec.GE x y) = GroupElement (FieldElement (Spec.fe_pack x)) (FieldElement (Spec.fe_pack y))

instance Arbitrary GroupElement where
  arbitrary = sized $ \n -> frequency [(1, lowOrderGE), (n `div` 10, GroupElement <$> arbitrary <*> arbitrary)]
  shrink (GroupElement x y) = [GroupElement x' y' | (x', y') <- shrink (x, y)]

geAsTy (GroupElement x y) = (feAsTy x, feAsTy y)
geAsSpec (GroupElement x y) = Spec.GE (feAsSpec x) (feAsSpec y)

data PointElement = PointElement Bool FieldElement deriving Show

instance Arbitrary PointElement where
  arbitrary = PointElement <$> arbitrary <*> arbitrary
  shrink (PointElement x y) = [PointElement x' y' | (x', y') <- shrink (x, y)]

pointAsTy (PointElement x y) = (toBit x, feAsTy y)
pointAsSpec (PointElement x y) = Spec.Point x (feAsSpec y)

toPoint :: Spec.Point -> Point
toPoint (Spec.Point b x) = (toBit b, toFE x)

data GroupElementJacobian = GroupElementJacobian FieldElement FieldElement FieldElement deriving Show

lowOrderGEJ :: Gen GroupElementJacobian
lowOrderGEJ = do
  Spec.GE x y <- geAsSpec <$> lowOrderGE
  z <- arbitrary
  let Spec.GEJ x' y' z' = Spec.gej_rescale (Spec.GEJ x y Spec.fe_one) (feAsSpec z)
  return $ GroupElementJacobian (FieldElement (Spec.fe_pack x')) (FieldElement (Spec.fe_pack y')) (FieldElement (Spec.fe_pack z'))

instance Arbitrary GroupElementJacobian where
  arbitrary = sized $ \n -> frequency [(1, lowOrderGEJ), (n `div` 10, GroupElementJacobian <$> arbitrary <*> arbitrary <*> arbitrary)]
  shrink (GroupElementJacobian x y z) = [GroupElementJacobian x' y' z' | (x', y', z') <- shrink (x, y, z)]

gejAsTy (GroupElementJacobian x y z) = ((feAsTy x, feAsTy y), feAsTy z)
gejAsSpec (GroupElementJacobian x y z) = Spec.GEJ (feAsSpec x) (feAsSpec y) (feAsSpec z)

gen_inf :: Gen GroupElementJacobian
gen_inf = GroupElementJacobian <$> arbitrary <*> arbitrary <*> pure (FieldElement 0)

gen_half_curve :: Gen GroupElement
gen_half_curve = half_curve <$> arbitrary
 where
  half_curve x = GroupElement x (FieldElement . Spec.fe_pack $ y')
   where
    x' = feAsSpec x
    y' = (x' .^. 3 .+. (Spec.fe 7)) .^. ((Spec.fieldOrder + 1) `div` 4)

gen_half_curve_jacobian :: Gen GroupElementJacobian
gen_half_curve_jacobian = half_curve_jacobian <$> gen_half_curve <*> arbitrary
 where
  half_curve_jacobian (GroupElement x y) z = GroupElementJacobian (FieldElement . Spec.fe_pack $ x' .*. z' .^. 2)
                                                                  (FieldElement . Spec.fe_pack $ y' .*. z' .^. 3)
                                                                  z
   where
    x' = feAsSpec x
    y' = feAsSpec y
    z' = feAsSpec z

gen_half_curve_inf :: Gen GroupElementJacobian
gen_half_curve_inf = half_curve_inf <$> arbitrary
 where
  half_curve_inf :: FieldElement -> GroupElementJacobian
  half_curve_inf x = GroupElementJacobian x (FieldElement . Spec.fe_pack $ y') (FieldElement 0)
   where
    x' = feAsSpec x
    y' = x' .^. (3 * ((Spec.fieldOrder + 1) `div` 4))

data ScalarElement = ScalarElement W.Word256 deriving Show

instance Arbitrary ScalarElement where
  arbitrary = sized $ \n -> if n == 0 then return case1 else resize (n-1) $ do
    i <- arbitrary
    j <- arbitrary
    e <- elements [0, 2^255, Spec.groupOrder, halforder]
    return . ScalarElement . fromInteger $ i + (j * Spec.lambda `mod` Spec.groupOrder) + e
   where
    -- This denormailzed scalar would produce a different result on split-lambda than the canonical scalar due to
    -- the approximate division used in the implementation.
    case1 = ScalarElement $ fromInteger Spec.groupOrder + c
     where
      c = 0x8f8da4d57dc094c4ecdd5448564d85f6 -- 2^383 `div` g2 + 1
    halforder = Spec.groupOrder `div` 2
  shrink (ScalarElement se) = ScalarElement <$> filter (<se) [0, 1, 2^256-1, 2^255-1, 2^255, 2^255+1, order - 1, order, order + 1, halforder -1, halforder, halforder + 1, halforder + 2]
   where
    order = fromInteger Spec.groupOrder
    halforder = order `div` 2

scalarAsTy (ScalarElement w) = toWord256 (toInteger w)
scalarAsSpec (ScalarElement w) = Spec.scalar (toInteger w)

toScalar :: Spec.Scalar -> Scalar
toScalar = toWord256 . Spec.scalar_repr

data WnafElement = WnafElement { wnafAsSpec :: Integer } deriving Show

instance Arbitrary WnafElement where
  arbitrary = WnafElement <$> choose (-2^128, 2^128-1)
  shrink (WnafElement we) = WnafElement <$> shrink we

wnafAsTy :: WnafElement -> (Bit, Word128)
wnafAsTy (WnafElement we) = (toBit (we < 0), toWord128 we)

traverseWnaf f (x,y) = (,) <$> f x <*> (both_.both_.both_.both_.both_.both_.both_) f y


data Sha256CtxElement = Sha256CtxElement [W.Word8] W.Word64 HashElement deriving Show

instance Arbitrary Sha256CtxElement where
  arbitrary = do
    preLen <- arbitrary
    count <- oneof [pure id, pure (2^55 +)] <*> ((`div` 256) <$> arbitrary)
    Sha256CtxElement <$> (vectorOf (preLen `mod` 64) arbitraryBoundedIntegral) <*> pure (fromInteger count) <*> arbitrary
  shrink (Sha256CtxElement l w h) = [Sha256CtxElement l w h | (l,w,h) <- shrink (l, w, h)]

ctxAsTy (Sha256CtxElement l w h) = (fst (bufferFill buffer63 (toW8 <$> l)), (toW64 w, heAsTy h))
ctxAsSpec (Sha256CtxElement l w h) = ctxBuild l (fromIntegral w) (heAsSpec h)
toCtx ctx = (buffer, (count, midstate))
 where
  buffer = fst $ bufferFill buffer63 (toWord8 . fromIntegral <$> BS.unpack (ctxBuffer ctx))
  count = toWord64 . fromIntegral $ ctxCounter ctx
  midstate = toHE . ivHash $ ctxIV ctx
