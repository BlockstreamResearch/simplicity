-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import qualified Data.List as L
import qualified Data.Word as W
import Lens.Family2 ((^..), allOf)
import Lens.Family2.Stock (both)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.*.), zipWithOf)
import qualified Simplicity.LibSecp256k1.Spec as LibSecp
import Simplicity.Programs.Bit
import Simplicity.Programs.Secp256k1
import Simplicity.Programs.Sha256
import Simplicity.Programs.Word
import Simplicity.Term.Core
import qualified Simplicity.Ty.Word as Ty

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Gen, Property, arbitrary, choose, elements, forAll, testProperty)

-- This collects the tests for the various Simplicity programs.
tests :: TestTree
tests = testGroup "Programs"
      [ testGroup "Arith"
        [ testProperty "fullAdder word8" prop_fullAdder8
        , testProperty "adder word8" prop_adder8
        , testProperty "fullSubtractor word8" prop_fullSubtractor8
        , testProperty "subtractor word8" prop_subtractor8
        , testProperty "fullMultiplier word8" prop_fullMultiplier8
        , testProperty "multiplier word8" prop_multiplier8
        , testProperty "bitwiseNot word8" prop_bitwiseNot8
        , testProperty "shift word8" prop_shift8
        , testProperty "rotate word8" prop_rotate8
        ]
      , testProperty "sha256" prop_sha256
      ]

-- The specification for full adder on Word8
prop_fullAdder8 :: Word8 -> Word8 -> Bit -> Bool
prop_fullAdder8 x y z = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y + if fromBit z then 1 else 0
 where
  (carry, result8) = fullAdder word8 ((x, y), z)

-- The specification for adder on Word8
prop_adder8 :: Word8 -> Word8 -> Bool
prop_adder8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y
 where
  (carry, result8) = adder word8 (x, y)

-- The specification for full subtractor on Word8
prop_fullSubtractor8 :: Word8 -> Word8 -> Bit -> Bool
prop_fullSubtractor8 x y z =  fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y - if fromBit z then 1 else 0
 where
  (borrow, result8) = fullSubtractor word8 ((x, y), z)

-- The specification for subtractor on Word8
prop_subtractor8 :: Word8 -> Word8 -> Bool
prop_subtractor8 x y =  fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y
 where
  (borrow, result8) = subtractor word8 (x, y)

-- The specification for full multiplier on Word8
prop_fullMultiplier8 :: Word8 -> Word8 -> Word8 -> Word8 -> Bool
prop_fullMultiplier8 w x y z = fromWord16 (fullMultiplier word8 ((x, y), (w, z))) == fromWord8 x * fromWord8 y + fromWord8 w + fromWord8 z

-- The specification for multiplier on Word8
prop_multiplier8 :: Word8 -> Word8 -> Bool
prop_multiplier8 x y = fromWord16 (multiplier word8 (x, y)) == fromWord8 x * fromWord8 y

-- The specification for bitwiseNot on Word8
prop_bitwiseNot8 :: Word8 -> Bool
prop_bitwiseNot8 x = conv (bitwiseNot word8 x) == W.complement (conv x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

-- The specification for shifts on Word8
prop_shift8 :: Word8 -> Property
prop_shift8 x = forAll small (\z -> convert (shift word8 z x) == W.shift (convert x) (-z))
 where
  convert :: Word8 -> W.Word8
  convert = fromInteger . fromWord8
  small = elements [-16..16]

-- The specification for rotates on Word8
prop_rotate8 :: Word8 -> Property
prop_rotate8 x = forAll small (\z -> convert (rotate word8 z x) == W.rotate (convert x) (-z))
 where
  convert :: Word8 -> W.Word8
  convert = fromInteger . fromWord8
  small = elements [-16..16]

-- The specification for SHA-256's block compression function.
prop_sha256 :: [W.Word8] -> Bool
prop_sha256 x0 = integerHash256 (bsHash (pack x)) == fromWord256 ((iv &&& iden >>> hashBlock) (toWord (DoubleW word256) paddedInteger))
 where
  x = L.take 55 x0
  len = length x
  mkInteger l = go l 0
   where
    go [] n     = n
    go (w:ws) n = go ws (W.shiftL n 8 .|. toInteger w)
  paddedInteger = W.shiftL (mkInteger (x ++ [0x80])) (8*(64 - (len + 1))) .|. toInteger len*8

fromFE :: FE -> LibSecp.FE
fromFE (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,(a8,a9))))))))) =
  LibSecp.FE (conv a0)
             (conv a1)
             (conv a2)
             (conv a3)
             (conv a4)
             (conv a5)
             (conv a6)
             (conv a7)
             (conv a8)
             (conv a9)
 where
  conv = fromInteger . fromWord32

toFE :: LibSecp.FE -> FE
toFE (LibSecp.FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) =
   (conv a0
  ,(conv a1
  ,(conv a2
  ,(conv a3
  ,(conv a4
  ,(conv a5
  ,(conv a6
  ,(conv a7
  ,(conv a8
  , conv a9)))))))))
 where
  conv = toWord32 . toInteger

eq_fe = zipWithOf (allOf LibSecp._fe) (==)

prop_normalizeWeak :: FE -> Bool
prop_normalizeWeak a = fromFE (normalizeWeak a) `eq_fe` LibSecp.normalizeWeak (fromFE a)

prop_normalize :: FE -> Bool
prop_normalize a = fromFE (normalize a) `eq_fe` LibSecp.normalize (fromFE a)
prop_normalize_over_low x y = prop_normalize a
 where
  a = toFE $ LibSecp.FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x03FFFFF
prop_normalize_over_high x y = prop_normalize a
 where
  a = toFE $ LibSecp.FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x07FFFFF

prop_add :: FE -> FE -> Bool
prop_add a b = fromFE (add (a, b)) `eq_fe` LibSecp.add (fromFE a) (fromFE b)

prop_mul :: FE -> FE -> Bool
prop_mul a b = fromFE (mul (a, b)) `eq_fe` LibSecp.mul (fromFE a) (fromFE b)

prop_sqr :: FE -> Bool
prop_sqr a = fromFE (sqr a) `eq_fe` LibSecp.sqr (fromFE a)

prop_mulInt :: FE -> Property
prop_mulInt a = forAll (choose (0, 32)) (\m -> fromFE (mulInt m a) `eq_fe` LibSecp.mulInt (fromInteger m) (fromFE a))

prop_neg :: FE -> Property
prop_neg a = forAll (choose (0, 32)) (\m -> fromFE (neg m a) `eq_fe` LibSecp.neg (fromInteger m) (fromFE a))

prop_inv :: FE -> Bool
prop_inv a = fromFE (inv a) `eq_fe` LibSecp.inv (fromFE a)

fromGE :: GE -> LibSecp.GE
fromGE (x, y) = LibSecp.GE (fromFE x) (fromFE y)

toGE :: LibSecp.GE -> GE
toGE (LibSecp.GE x y) = (toFE x, toFE y)

fromGEJ :: GEJ -> LibSecp.GEJ
fromGEJ ((x, y), z) = LibSecp.GEJ (fromFE x) (fromFE y) (fromFE z)

toGEJ :: LibSecp.GEJ -> GEJ
toGEJ (LibSecp.GEJ x y z) = ((toFE x, toFE y), toFE z)

eq_gej = zipWithOf (allOf LibSecp._gej) eq_fe

gen_inf :: Gen GEJ
gen_inf = (\xy -> (xy, feZero ())) <$> arbitrary

prop_double_inf :: Property
prop_double_inf = forAll gen_inf $ prop_double

prop_double :: GEJ -> Bool
prop_double a = fromGEJ (double a) `eq_gej` LibSecp.double (fromGEJ a)

prop_offsetPoint :: GEJ -> GE -> Bool
prop_offsetPoint a b = fromFE rz `eq_fe` rz' && fromGEJ c `eq_gej` c'
 where
  (rz,c) = offsetPoint (a, b)
  (rz',c') = LibSecp.offsetPoint (fromGEJ a) (fromGE b)

prop_offsetPoint_double z b = prop_offsetPoint a b
 where
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (b'y .*. z'3)), z)

prop_offsetPoint_opp z b = prop_offsetPoint a b
 where
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (LibSecp.neg 1 (b'y .*. z'3))), z)

prop_offsetPoint_inf b = forAll gen_inf $ \a -> prop_offsetPoint a b

prop_offsetPointZinv :: GEJ -> GE -> FE -> Bool
prop_offsetPointZinv a b zinv = fromGEJ (offsetPointZinv (a,(b,zinv))) `eq_gej` LibSecp.offsetPointZinv (fromGEJ a) (fromGE b) (fromFE zinv)

prop_offsetPointZinv_double z b bz = prop_offsetPointZinv a b bz
 where
  b'z = fromFE bz
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (b'y .*. z'3)), toFE (LibSecp.inv b'z .*. z'))

prop_offsetPointZinv_opp z b bz = prop_offsetPointZinv a b bz
 where
  b'z = fromFE bz
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (LibSecp.neg 1 (b'y .*. z'3))), toFE (LibSecp.inv b'z .*. z'))

prop_offsetPointZinv_inf :: GE -> FE -> Property
prop_offsetPointZinv_inf b zinv = forAll gen_inf $ \a -> prop_offsetPointZinv a b zinv

fromScalar :: Ty.Word256 -> LibSecp.Scalar
fromScalar ((n3,n2),(n1,n0)) = LibSecp.Scalar (conv n0) (conv n1) (conv n2) (conv n3)
 where
  conv = fromInteger . fromWord64


prop_wnaf5 :: Ty.Word256 -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (fmap unsign) (LibSecp.wnaf 5 (fromScalar n) ++ repeat Nothing))
 where
  lhs = either (const Nothing) (Just . fromInteger . fromWord (DoubleW (DoubleW BitW))) <$> wnaf5 n^..both.both.both.both.both.both.both.both
  unsign x | x < 0 = 2^4 + x
           | otherwise = x
prop_wnaf5_hi :: Ty.Word128 -> Bool
prop_wnaf5_hi n10 = prop_wnaf5 (Ty.toWord (Ty.DoubleW Ty.word64) (-1), n10)

prop_wnaf16 :: Ty.Word256 -> Bool
prop_wnaf16 n = L.and $ zipWith (==) lhs (fmap (fmap unsign) (LibSecp.wnaf 16 (fromScalar n) ++ repeat Nothing))
 where
  lhs = either (const Nothing) (Just . fromInteger . fromWord16) <$> wnaf16 n^..both.both.both.both.both.both.both.both
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1
prop_wnaf16_hi :: Ty.Word128 -> Bool
prop_wnaf16_hi n10 = prop_wnaf16 (Ty.toWord (Ty.DoubleW Ty.word64) (-1), n10)

prop_ecMult :: GEJ -> Word256 -> Word256 -> Bool
prop_ecMult a na ng = fromGEJ (ecMult ((a, na), ng)) `eq_gej` LibSecp.ecMult (fromGEJ a) (fromScalar na) (fromScalar ng)

prop_ecMult0 :: GEJ -> Word256 -> Bool
prop_ecMult0 a ng = prop_ecMult a na ng
 where
  na = toWord256 0
