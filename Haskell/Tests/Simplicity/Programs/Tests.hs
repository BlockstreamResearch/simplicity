-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Prelude hiding (sqrt, all)
import Control.Arrow ((***), right)
import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import Data.ByteString.Short (toShort)
import qualified Data.List as L
import Lens.Family2 ((^..), allOf, zipWithOf)
import Lens.Family2.Stock (backwards, both_)

import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.+.), (.*.), (.^.))
import qualified Simplicity.LibSecp256k1.Spec as Spec
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.LibSecp256k1.Lib
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.Word
import Simplicity.Term.Core
import Simplicity.Ty.Word as Ty
import qualified Simplicity.Word as W

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), Assertion, testCase)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property
                             , arbitraryBoundedIntegral, choose, elements, forAll, resize, sized, testProperty
                             , withMaxSuccess
                             )

-- This collects the tests for the various Simplicity programs.
tests :: TestTree
tests = testGroup "Programs"
      [ testGroup "Word"
        [ testCase "low word8" assert_low8
        , testCase "high word8" assert_high8
        , testProperty "compelment word8" prop_complement8
        , testProperty "and word8" prop_and8
        , testProperty "or word8" prop_or8
        , testProperty "xor word8" prop_xor8
        , testProperty "xor3 word8" prop_xor3_8
        , testProperty "maj word8" prop_maj8
        , testProperty "ch word8" prop_ch8
        , testProperty "some word4" prop_some4
        , testProperty "all word4" prop_all4
        , testProperty "shift_const_by false word8" prop_shift_const_by_false8
        , testProperty "rotate_const word8" prop_rotate_const8
        , testProperty "transpose zv2 zv8" prop_transpose_2x8
        , testProperty "transpose zv8 zv8" prop_transpose_8x8
        ]
      , testGroup "Arith"
        [ testCase "zero word8" assert_zero8
        , testCase "one word8" assert_one8
        , testProperty "full_add word8" prop_full_add8
        , testProperty "add word8" prop_fe_add8
        , testProperty "full_increment word8" prop_full_increment8
        , testProperty "increment word8" prop_increment8
        , testProperty "full_subtract word8" prop_full_subtract8
        , testProperty "subtract word8" prop_subtract8
        , testProperty "negate word8" prop_negateate8
        , testProperty "full_decrement word8" prop_full_decrement8
        , testProperty "decrement word8" prop_decrement8
        , testProperty "fullMultiply word8" prop_full_multiply8
        , testProperty "multiply word8" prop_fe_multiplytiply8
        , testProperty "is_zero word4" prop_is_zero4
        , testProperty "is_one word4" prop_is_one4
        , testProperty "lt word8" prop_lt8
        , testProperty "le word8" prop_le8
        , testProperty "min word8" prop_min8
        , testProperty "max word8" prop_max8
        , testProperty "median word8" prop_median8
        , testProperty "lsb word8" prop_lsb8
        , testProperty "msb word8" prop_msb8
        , testProperty "div_mod word8" prop_div_mod8
        , testProperty "divide word8" prop_divide8
        , testProperty "modulo word8" prop_modulo8
        , testProperty "divides word8" prop_divides8
        , testProperty "bezout word8" prop_bezout8
        , testProperty "cofactors word8" prop_cofactors8
        , testProperty "gcd word8" prop_gcd8
        , testProperty "lcm word8" prop_lcm8
        , testProperty "absolute_value word4" prop_absolute_value4
        , testProperty "sign word4" prop_sign4
        ]
      , testProperty "sha256" prop_sha256
      , testGroup "ellipticCurve"
        [ testProperty "fe_normalize" prop_fe_normalize
        , testProperty "fe_add" prop_fe_add
        , testProperty "fe_multiply" prop_fe_multiply
        , testProperty "fe_square" prop_fe_square
        , testProperty "fe_negate" prop_fe_negate
        , testProperty "fe_invert" (withMaxSuccess 10 prop_fe_invert)
        , testProperty "fe_square_root" (withMaxSuccess 10 prop_fe_square_root)
        , testProperty "gej_rescale" prop_gej_rescale
        , testProperty "gej_rescale_inf" prop_gej_rescale_inf
        , testProperty "gej_double" prop_gej_double
        , testProperty "gej_double_inf" prop_gej_double_inf
        , testProperty "gej_add_ex" prop_gej_add_ex
        , testProperty "gej_add_ex_double" prop_gej_add_ex_double
        , testProperty "gej_add_ex_opp" prop_gej_add_ex_opp
        , testProperty "gej_add_ex_infl" prop_gej_add_ex_infl
        , testProperty "gej_add_ex_infr" prop_gej_add_ex_infr
        , testProperty "gej_add" prop_gej_add
        , testProperty "gej_add_double" prop_gej_add_double
        , testProperty "gej_add_opp" prop_gej_add_opp
        , testProperty "gej_add_infl" prop_gej_add_infl
        , testProperty "gej_add_infr" prop_gej_add_infr
        , testProperty "gej_ge_add_ex" prop_gej_ge_add_ex
        , testProperty "gej_ge_add_ex_double" prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp" prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf" prop_gej_ge_add_ex_inf
        , testProperty "gej_x_equiv" prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf" prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true" prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero" prop_gej_x_equiv_inf_zero
        , testProperty "gej_is_on_curve" prop_gej_is_on_curve
        , testProperty "gej_is_on_curve_half" prop_gej_is_on_curve_half
        , testProperty "gej_is_on_curve_inf" prop_gej_is_on_curve_inf
        , testProperty "gej_is_on_curve_inf_half" prop_gej_is_on_curve_inf_half
        , testProperty "ge_is_on_curve" prop_ge_is_on_curve
        , testProperty "ge_is_on_curve_half" prop_ge_is_on_curve_half
        , testProperty "scalar_normalize" prop_scalar_normalize
        , testProperty "scalar_add" prop_scalar_add
        , testProperty "scalar_square" prop_scalar_square
        , testProperty "scalar_multiply" prop_scalar_multiply
        , testProperty "scalar_negate" prop_scalar_negate
        , testProperty "scalar_invert" prop_scalar_invert
        , testProperty "scalar_split_lambda" prop_scalar_split_lambda
        , testProperty "wnaf5" prop_wnaf5
        , testProperty "wnaf15" prop_wnaf15
        , testProperty "decompress" (withMaxSuccess 10 prop_decompress)
        ]
      , testGroup "bip0340"
        [ testProperty "pubkey_unpack" prop_pubkey_unpack
        , testProperty "pubkey_unpack_neg" prop_pubkey_unpack_neg
        , testProperty "signature_unpack" prop_signature_unpack
        ]
      ]

assert_low8 :: Assertion
assert_low8 = 0 @=? fromWord8 (low word8 ())

assert_high8 :: Assertion
assert_high8 = 0xff @=? fromWord8 (high word8 ())

prop_complement8 :: Word8 -> Bool
prop_complement8 x = W.complement (fromInteger . fromWord8 $ x) == (fromInteger . fromWord8 $ complement word8 x :: W.Word8)

prop_and8 :: Word8 -> Word8 -> Bool
prop_and8 x y = (fromInteger $ fromWord8 x) W..&. (fromInteger $ fromWord8 y)
             == (fromInteger . fromWord8 $ bitwise_and word8 (x, y) :: W.Word8)

prop_or8 :: Word8 -> Word8 -> Bool
prop_or8 x y = (fromInteger $ fromWord8 x) W..|. (fromInteger $ fromWord8 y)
            == (fromInteger . fromWord8 $ bitwise_or word8 (x, y) :: W.Word8)

prop_xor8 :: Word8 -> Word8 -> Bool
prop_xor8 x y = (fromInteger $ fromWord8 x) `W.xor` (fromInteger $ fromWord8 y)
             == (fromInteger . fromWord8 $ bitwise_xor word8 (x, y) :: W.Word8)

prop_xor3_8 :: Word8 -> Word8 -> Word8 -> Bool
prop_xor3_8 x y z = (fromInteger $ fromWord8 x) `W.xor` (fromInteger $ fromWord8 y) `W.xor` (fromInteger $ fromWord8 z)
                 == (fromInteger . fromWord8 $ bitwise_xor3 word8 (x, (y, z)) :: W.Word8)

prop_maj8 :: Word8 -> Word8 -> Word8 -> Bool
prop_maj8 x y z = zipWith3 maj (x^..bits8) (y^..bits8) (z^..bits8)
               == (fromBit <$> bitwise_maj word8 (x, (y, z))^..bits8)
 where
  maj a b c = 2 <= fromWord1 a + fromWord1 b + fromWord1 c
  bits8 x = (both_.both_.both_) x

prop_ch8 :: Word8 -> Word8 -> Word8 -> Bool
prop_ch8 x y z = zipWith3 ch (x^..bits8) (y^..bits8) (z^..bits8)
              == (fromBit <$> bitwise_ch word8 (x, (y, z))^..bits8)
 where
  ch a b c = if fromBit a then fromBit b else fromBit c
  bits8 x = (both_.both_.both_) x

prop_some4 :: Word4 -> Bool
prop_some4 x = (0 /= fromWord4 x)
            == fromBit (some word4 x)

prop_all4 :: Word4 -> Bool
prop_all4 x = (0xf == fromWord4 x)
           == fromBit (all word4 x)

prop_shift_const_by_false8 :: Word8 -> Property
prop_shift_const_by_false8 x = forAll (choose (-8,16)) $ \c ->
                               W.shift (conv x) c == conv (shift_const_by false word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_rotate_const8 :: Word8 -> Property
prop_rotate_const8 x = forAll (choose (-8,16)) $ \c ->
                       W.rotate (conv x) c == conv (rotate_const word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_transpose_2x8 :: Word16 -> Bool
prop_transpose_2x8 x = L.transpose (map (^..both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv2 zv8 x^..both_)
 where
  zv2 = DoubleZV SingleZV
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV

prop_transpose_8x8 :: Word64 -> Bool
prop_transpose_8x8 x = L.transpose (map (^..both_.both_.both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv8 zv8' x^..both_.both_.both_)
 where
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV
  zv8' = DoubleZV . DoubleZV . DoubleZV $ SingleZV -- monomorhpism restriction

assert_zero8 :: Assertion
assert_zero8 = 0 @=? fromWord8 (Arith.zero word8 ())

assert_one8 :: Assertion
assert_one8 = 0x1 @=? fromWord8 (Arith.one word8 ())

-- The specification for full adder on Word8
prop_full_add8 :: Bit -> Word8 -> Word8 -> Bool
prop_full_add8 z x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y + if fromBit z then 1 else 0
 where
  (carry, result8) = Arith.full_add word8 (z, (x, y))

-- The specification for adder on Word8
prop_fe_add8 :: Word8 -> Word8 -> Bool
prop_fe_add8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y
 where
  (carry, result8) = Arith.add word8 (x, y)

prop_full_increment8 :: Bit -> Word8 -> Bool
prop_full_increment8 z x = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + if fromBit z then 1 else 0
 where
  (carry, result8) = Arith.full_increment word8 (z, x)

prop_increment8 :: Word8 -> Bool
prop_increment8 x = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + 1
 where
  (carry, result8) = Arith.increment word8 x

-- The specification for full subtractor on Word8
prop_full_subtract8 :: Bit -> Word8 -> Word8 -> Bool
prop_full_subtract8 z x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y - if fromBit z then 1 else 0
 where
  (borrow, result8) = Arith.full_subtract word8 (z, (x, y))

-- The specification for subtractor on Word8
prop_subtract8 :: Word8 -> Word8 -> Bool
prop_subtract8 x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y
 where
  (borrow, result8) = Arith.subtract word8 (x, y)

prop_negateate8 :: Word8 -> Word8 -> Bool
prop_negateate8 x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) - fromWord8 x
 where
  (borrow, result8) = Arith.negate word8 x

prop_full_decrement8 :: Bit -> Word8 -> Bool
prop_full_decrement8 z x = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - if fromBit z then 1 else 0
 where
  (borrow, result8) = Arith.full_decrement word8 (z, x)

prop_decrement8 :: Word8 -> Bool
prop_decrement8 x = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - 1
 where
  (borrow, result8) = Arith.decrement word8 x

-- The specification for full multiplier on Word8
prop_full_multiply8 :: Word8 -> Word8 -> Word8 -> Word8 -> Bool
prop_full_multiply8 w x y z = fromWord16 (Arith.full_multiply word8 ((x, y), (w, z))) == fromWord8 x * fromWord8 y + fromWord8 w + fromWord8 z

-- The specification for multiplier on Word8
prop_fe_multiplytiply8 :: Word8 -> Word8 -> Bool
prop_fe_multiplytiply8 x y = fromWord16 (Arith.multiply word8 (x, y)) == fromWord8 x * fromWord8 y

prop_is_zero4 :: Word4 -> Bool
prop_is_zero4 x = (0 == fromWord4 x) == fromBit (Arith.is_zero word4 x)

prop_is_one4 :: Word4 -> Bool
prop_is_one4 x = (1 == fromWord4 x) == fromBit (Arith.is_one word4 x)

prop_lt8 :: Word8 -> Word8 -> Bool
prop_lt8 x y = (fromWord8 x < fromWord8 y) == fromBit (Arith.lt word8 (x,y))

prop_le8 :: Word8 -> Word8 -> Bool
prop_le8 x y = (fromWord8 x <= fromWord8 y) == fromBit (Arith.le word8 (x,y))

prop_min8 :: Word8 -> Word8 -> Bool
prop_min8 x y = (fromWord8 x `min` fromWord8 y) == fromWord8 (Arith.min word8 (x,y))

prop_max8 :: Word8 -> Word8 -> Bool
prop_max8 x y = (fromWord8 x `max` fromWord8 y) == fromWord8 (Arith.max word8 (x,y))

prop_median8 :: Word8 -> Word8 -> Word8 -> Bool
prop_median8 x y z = median (fromWord8 x) (fromWord8 y) (fromWord8 z) == fromWord8 (Arith.median word8 (x,(y,z)))
 where
  median a b c = head . tail . L.sort $ [a,b,c]

prop_lsb8 :: Word8 -> Bool
prop_lsb8 x = W.testBit (fromWord8 x) 0 == fromBit (Arith.lsb word8 x)

prop_msb8 :: Word8 -> Bool
prop_msb8 x = W.testBit (fromWord8 x) 7 == fromBit (Arith.msb word8 x)

prop_div_mod8 :: Word8 -> Word8 -> Bool
prop_div_mod8 x y = div_mod_spec (fromWord8 x) (fromWord8 y) == (fromWord8 a, fromWord8 b)
 where
  div_mod_spec x 0 = (0, x)
  div_mod_spec x y = divMod x y
  (a, b) = Arith.div_mod word8 (x, y)

prop_divide8 :: Word8 -> Word8 -> Bool
prop_divide8 x y = div_spec (fromWord8 x) (fromWord8 y) == fromWord8 (Arith.divide word8 (x, y))
 where
  div_spec x 0 = 0
  div_spec x y = div x y

prop_modulo8 :: Word8 -> Word8 -> Bool
prop_modulo8 x y = mod_spec (fromWord8 x) (fromWord8 y) == fromWord8 (Arith.modulo word8 (x, y))
 where
  mod_spec x 0 = x
  mod_spec x y = mod x y

prop_divides8 :: Word8 -> Word8 -> Bool
prop_divides8 x y = divides_spec (fromWord8 x) (fromWord8 y) == fromBit (Arith.divides word8 (x, y))
 where
  divides_spec 0 y = y == 0
  divides_spec x y = y `mod` x == 0

prop_bezout8 :: Word8 -> Word8 -> Bool
prop_bezout8 x y = a * x' + b * y' == d
                && if x' == y' then (a == 1 && b == 0)
                   else if y' == 0 then (a == 1 && b == 0)
                   else if x' == 0 then (a == 0 && b == 1)
                   else (if d == y' then a == 0 else abs a * 2 * d <= y')
                     && (if d == x' then b == 0 else abs b * 2 * d <= x')
 where
  x' = fromWord8 x
  y' = fromWord8 y
  d = x' `gcd` y'
  (a, b) = either f g $ Arith.bezout word8 (x, y)
  f (a, b) = (fromWord8 a, - fromWord8 b)
  g (a, b) = (- fromWord8 a, fromWord8 b)

prop_cofactors8 :: Word8 -> Word8 -> Bool
prop_cofactors8 x y = fromWord8 x == d * fromWord8 a
                   && fromWord8 y == d * fromWord8 b
 where
  d = fromWord8 x `gcd` fromWord8 y
  (a, b) = Arith.cofactors word8 (x, y)

prop_gcd8 :: Word8 -> Word8 -> Bool
prop_gcd8 x y = (fromWord8 x `gcd` fromWord8 y) == fromWord8 (Arith.gcd word8 (x,y))

prop_lcm8 :: Word8 -> Word8 -> Bool
prop_lcm8 x y = (fromWord8 x `lcm` fromWord8 y) == fromWord16 (Arith.lcm word8 (x,y))

prop_absolute_value4 :: Word4 -> Bool
prop_absolute_value4 x = abs (fromInt4 x) == fromWord4 (Arith.absolute_value word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x

prop_sign4 :: Word4 -> Bool
prop_sign4 x = signum (fromInt4 x) == fromInt2 (Arith.sign word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x
  fromInt2 x = if 2^1 <= w2 then w2 - 2^2 else w2
   where
    w2 = fromWord2 x

-- The specification for SHA-256's block compression function.
prop_sha256 :: [W.Word8] -> Bool
prop_sha256 x0 = integerHash256 (bsHash (pack x)) == fromWord256 ((iv &&& iden >>> hashBlock) (toWord512 paddedInteger))
 where
  x = L.take 55 x0
  len = length x
  mkInteger l = go l 0
   where
    go [] n     = n
    go (w:ws) n = go ws (W.shiftL n 8 .|. toInteger w)
  paddedInteger = W.shiftL (mkInteger (x ++ [0x80])) (8*(64 - (len + 1))) .|. toInteger len*8

toFE :: Spec.FE -> FE
toFE = toWord256 . toInteger . Spec.fe_pack

maybeToTy :: Maybe a -> Either () a
maybeToTy Nothing = Left ()
maybeToTy (Just x) = Right x

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

prop_fe_normalize :: FieldElement -> Bool
prop_fe_normalize a = fe_normalize (feAsTy a) == toFE (feAsSpec a)

fe_unary_prop f g = \a -> fastF (feAsTy a) == Just (toFE (g (feAsSpec a)))
 where
  fastF = fastCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == Just (toFE (g (feAsSpec a) (feAsSpec b)))
 where
  fastF = fastCoreEval f

prop_fe_add :: FieldElement -> FieldElement -> Bool
prop_fe_add = fe_binary_prop fe_add Spec.fe_add

prop_fe_multiply :: FieldElement -> FieldElement -> Bool
prop_fe_multiply = fe_binary_prop fe_multiply Spec.fe_multiply

prop_fe_square :: FieldElement -> Bool
prop_fe_square = fe_unary_prop fe_square Spec.fe_square

prop_fe_negate :: FieldElement -> Bool
prop_fe_negate = fe_unary_prop fe_negate Spec.fe_negate

prop_fe_invert :: FieldElement -> Bool
prop_fe_invert = fe_unary_prop fe_invert Spec.fe_invert

prop_fe_square_root :: FieldElement -> Bool
prop_fe_square_root = \a -> fastSqrt (feAsTy a) == Just ((fmap toFE . maybeToTy) (Spec.fe_square_root (feAsSpec a)))
 where
  fastSqrt = fastCoreEval fe_square_root

toGE :: Spec.GE -> GE
toGE (Spec.GE x y) = (toFE x, toFE y)

toGEJ :: Spec.GEJ -> GEJ
toGEJ (Spec.GEJ x y z) = ((toFE x, toFE y), toFE z)

toPoint :: Spec.Point -> Point
toPoint (Spec.Point b x) = (toBit b, toFE x)

data GroupElement = GroupElement FieldElement FieldElement deriving Show

instance Arbitrary GroupElement where
  arbitrary = GroupElement <$> arbitrary <*> arbitrary
  shrink (GroupElement x y) = [GroupElement x' y' | (x', y') <- shrink (x, y)]

geAsTy (GroupElement x y) = (feAsTy x, feAsTy y)
geAsSpec (GroupElement x y) = Spec.GE (feAsSpec x) (feAsSpec y)

data PointElement = PointElement Bool FieldElement deriving Show

instance Arbitrary PointElement where
  arbitrary = PointElement <$> arbitrary <*> arbitrary
  shrink (PointElement x y) = [PointElement x' y' | (x', y') <- shrink (x, y)]

pointAsTy (PointElement x y) = (toBit x, feAsTy y)
pointAsSpec (PointElement x y) = Spec.Point x (feAsSpec y)

data GroupElementJacobian = GroupElementJacobian FieldElement FieldElement FieldElement deriving Show

instance Arbitrary GroupElementJacobian where
  arbitrary = GroupElementJacobian <$> arbitrary <*> arbitrary <*> arbitrary
  shrink (GroupElementJacobian x y z) = [GroupElementJacobian x' y' z' | (x', y', z') <- shrink (x, y, z)]

gejAsTy (GroupElementJacobian x y z) = ((feAsTy x, feAsTy y), feAsTy z)
gejAsSpec (GroupElementJacobian x y z) = Spec.GEJ (feAsSpec x) (feAsSpec y) (feAsSpec z)

gen_inf :: Gen GroupElementJacobian
gen_inf = GroupElementJacobian <$> arbitrary <*> arbitrary <*> pure (FieldElement 0)

prop_gej_rescale :: GroupElementJacobian -> FieldElement -> Bool
prop_gej_rescale = \a c -> fast_gej_rescale (gejAsTy a, feAsTy c) == Just (toGEJ (Spec.gej_rescale (gejAsSpec a) (feAsSpec c)))
 where
  fast_gej_rescale = fastCoreEval gej_rescale

prop_gej_rescale_inf :: FieldElement -> Property
prop_gej_rescale_inf c = forAll gen_inf $ flip prop_gej_rescale c

prop_gej_double :: GroupElementJacobian -> Bool
prop_gej_double = \a -> fast_gej_double (gejAsTy a) == Just (toGEJ (Spec.gej_double (gejAsSpec a)))
 where
  fast_gej_double = fastCoreEval gej_double

prop_gej_double_inf :: Property
prop_gej_double_inf = forAll gen_inf $ prop_gej_double

prop_gej_add_ex :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add_ex = \a b ->
  let rzc = fast_gej_add_ex (gejAsTy a, gejAsTy b)
      (rz', c') = Spec.gej_add_ex (gejAsSpec a) (gejAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_add_ex = fastCoreEval gej_add_ex

prop_gej_add_ex_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_double z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_infl b = forAll gen_inf $ \a -> prop_gej_add_ex a b
prop_gej_add_ex_infr a = forAll gen_inf $ \b -> prop_gej_add_ex a b

prop_gej_add :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add = \a b -> fast_gej_add (gejAsTy a, gejAsTy b) == Just (toGEJ (gejAsSpec a <> gejAsSpec b))
 where
  fast_gej_add = fastCoreEval gej_add

prop_gej_add_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_double z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_infl b = forAll gen_inf $ \a -> prop_gej_add a b
prop_gej_add_infr a = forAll gen_inf $ \b -> prop_gej_add a b

prop_gej_ge_add_ex :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_add_ex = \a b ->
  let rzc = fast_gej_ge_add_ex (gejAsTy a, geAsTy b)
      (rz', c') = Spec.gej_ge_add_ex (gejAsSpec a) (geAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_ge_add_ex = fastCoreEval gej_ge_add_ex

prop_gej_ge_add_ex_double :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_double z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_opp :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_opp z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b

prop_gej_x_equiv :: FieldElement -> GroupElementJacobian -> Bool -- gej_x_equiv will essentially always be false on random inputs.
prop_gej_x_equiv = \x0 a -> fast_gej_x_equiv (feAsTy x0, gejAsTy a) == Just (toBit (Spec.gej_x_equiv (feAsSpec x0) (gejAsSpec a) ))
 where
  fast_gej_x_equiv = fastCoreEval gej_x_equiv

prop_gej_x_equiv_inf x0 = forAll gen_inf $ prop_gej_x_equiv x0
prop_gej_x_equiv_true y z x0 = prop_gej_x_equiv x0 a
  where
   z' = feAsSpec z
   x0' = feAsSpec x0
   a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x0' .*. z' .^. 2) y z

prop_gej_x_equiv_inf_zero = prop_gej_x_equiv_inf (FieldElement 0)

prop_ge_is_on_curve :: GroupElement -> Bool
prop_ge_is_on_curve = \a -> fast_ge_is_on_curve (geAsTy a) == Just (toBit (Spec.ge_is_on_curve (geAsSpec a)))
 where
  fast_ge_is_on_curve = fastCoreEval ge_is_on_curve

gen_half_curve :: Gen GroupElement
gen_half_curve = half_curve <$> arbitrary
 where
  half_curve x = GroupElement x (FieldElement . Spec.fe_pack $ y')
   where
    x' = feAsSpec x
    y' = (x' .^. 3 .+. (Spec.fe 7)) .^. ((Spec.fieldOrder + 1) `div` 4)

prop_ge_is_on_curve_half = forAll gen_half_curve prop_ge_is_on_curve

prop_gej_is_on_curve :: GroupElementJacobian -> Bool
prop_gej_is_on_curve = \a -> fast_gej_is_on_curve (gejAsTy a) == Just (toBit (Spec.gej_is_on_curve (gejAsSpec a)))
 where
  fast_gej_is_on_curve = fastCoreEval gej_is_on_curve

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

prop_gej_is_on_curve_inf = forAll gen_inf prop_gej_is_on_curve
prop_gej_is_on_curve_inf_half = forAll gen_half_curve_inf prop_gej_is_on_curve
prop_gej_is_on_curve_half = forAll gen_half_curve_jacobian prop_gej_is_on_curve

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

scalar_unary_prop f g = \a -> fastF (scalarAsTy a) == Just (toScalar (g (scalarAsSpec a)))
 where
  fastF = fastCoreEval f

scalar_binary_prop f g = \a b -> fastF (scalarAsTy a, scalarAsTy b) == Just (toScalar (g (scalarAsSpec a) (scalarAsSpec b)))
 where
  fastF = fastCoreEval f

prop_scalar_normalize :: ScalarElement -> Bool
prop_scalar_normalize a@(ScalarElement w) = scalar_normalize (scalarAsTy a) == toScalar (Spec.scalar (toInteger w))

prop_scalar_add :: ScalarElement -> ScalarElement -> Bool
prop_scalar_add = scalar_binary_prop scalar_add Spec.scalar_add

prop_scalar_square :: ScalarElement -> Bool
prop_scalar_square = scalar_unary_prop scalar_square Spec.scalar_square

prop_scalar_multiply :: ScalarElement -> ScalarElement -> Bool
prop_scalar_multiply = scalar_binary_prop scalar_multiply Spec.scalar_multiply

prop_scalar_negate :: ScalarElement -> Bool
prop_scalar_negate = scalar_unary_prop scalar_negate Spec.scalar_negate

prop_scalar_invert :: ScalarElement -> Bool
prop_scalar_invert = scalar_unary_prop scalar_invert Spec.scalar_invert

prop_scalar_split_lambda :: ScalarElement -> Bool
prop_scalar_split_lambda = \a -> ((interp *** interp) <$> fast_scalar_split_lambda (scalarAsTy a))
                            == Just (Spec.scalar_split_lambda (scalarAsSpec a))
 where
  interp (b,x) = fromWord128 x - if fromBit b then 2^128 else 0
  fast_scalar_split_lambda = fastCoreEval scalar_split_lambda

data WnafElement = WnafElement { wnafAsSpec :: Integer } deriving Show

instance Arbitrary WnafElement where
  arbitrary = WnafElement <$> choose (-2^128, 2^128-1)
  shrink (WnafElement we) = WnafElement <$> shrink we

wnafAsTy :: WnafElement -> (Bit, Word128)
wnafAsTy (WnafElement we) = (toBit (we < 0), toWord128 we)

traverseWnaf f (x,y) = (,) <$> f x <*> (both_.both_.both_.both_.both_.both_.both_) f y

prop_wnaf5 :: WnafElement -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 5 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap fromWord4 <$> wnaf5 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^4 + x
           | otherwise = x

prop_wnaf15 :: WnafElement -> Bool
prop_wnaf15 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 15 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap (fromWord16) <$> wnaf15 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1

prop_linear_combination_1 :: ScalarElement -> GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1 = \na a ng -> fast_linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
             == Just (toGEJ (Spec.linear_combination_1 (scalarAsSpec na) (gejAsSpec a) (scalarAsSpec ng)))
 where
  fast_linear_combination_1 = fastCoreEval linear_combination_1

prop_linear_combination_1_0 :: GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1_0 a ng = prop_linear_combination_1 na a ng
 where
  na = ScalarElement 0

prop_linear_combination_1_inf :: ScalarElement -> ScalarElement -> Property
prop_linear_combination_1_inf na ng = forAll gen_inf $ \a -> prop_linear_combination_1 na a ng

prop_linear_check_1 :: ScalarElement -> GroupElement -> ScalarElement -> GroupElement -> Bool
prop_linear_check_1 = \na a ng r -> fast_linear_check_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
             == Just (toBit (Spec.linear_check [(scalarAsSpec na, geAsSpec a)] (scalarAsSpec ng) (geAsSpec r)))
 where
  fast_linear_check_1 = fastCoreEval linear_check_1

prop_decompress :: PointElement -> Bool
prop_decompress = \a -> fast_decompress (pointAsTy a)
             == Just ((fmap toGE . maybeToTy) (Spec.decompress (pointAsSpec a)))
 where
  fast_decompress = fastCoreEval decompress

prop_point_check_1 :: ScalarElement -> PointElement -> ScalarElement -> PointElement -> Bool
prop_point_check_1 = \na a ng r -> fast_point_check_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
             == Just (toBit (Spec.point_check [(scalarAsSpec na, pointAsSpec a)] (scalarAsSpec ng) (pointAsSpec r)))
 where
  fast_point_check_1 = fastCoreEval point_check_1

prop_pubkey_unpack :: FieldElement -> Bool
prop_pubkey_unpack a@(FieldElement w) = fast_pubkey_unpack (feAsTy a)
                                     == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack (Spec.PubKey w)))
 where
  fast_pubkey_unpack = fastCoreEval pubkey_unpack

prop_pubkey_unpack_neg :: FieldElement -> Bool
prop_pubkey_unpack_neg a@(FieldElement w) = fast_pubkey_unpack_neg (feAsTy a)
                                         == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack_neg (Spec.PubKey w)))
 where
  fast_pubkey_unpack_neg = fastCoreEval pubkey_unpack_neg

prop_signature_unpack :: FieldElement -> ScalarElement -> Bool
prop_signature_unpack r@(FieldElement wr) s@(ScalarElement ws) =
  fast_signature_unpack (feAsTy r, scalarAsTy s) ==
  Just ((fmap (toFE *** toScalar) . maybeToTy) (Spec.signature_unpack (Spec.Sig wr ws)))
 where
  fast_signature_unpack = fastCoreEval signature_unpack

fast_bip0340_check = fromJust . fastCoreEval bip0340_check
 where
  fromJust (Just a) = fromBit a
  fromJust Nothing = False

bip0340_0 :: Bool
bip0340_0 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9
  m = toWord256 0
  sig = toWord512 0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0

bip0340_1 :: Bool
bip0340_1 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A

bip0340_2 :: Bool
bip0340_2 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8
  m = toWord256 0x7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7

bip0340_3 :: Bool
bip0340_3 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517
  m = toWord256 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  sig = toWord512 0x7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3

bip0340_4 :: Bool
bip0340_4 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9
  m = toWord256 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
  sig = toWord512 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4

bip0340_5 :: Bool
bip0340_5 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xEEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B

bip0340_6 :: Bool
bip0340_6 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2

bip0340_7 :: Bool
bip0340_7 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD

bip0340_8 :: Bool
bip0340_8 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6

bip0340_9 :: Bool
bip0340_9 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x0000000000000000000000000000000000000000000000000000000000000000123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051

bip0340_10 :: Bool
bip0340_10 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x00000000000000000000000000000000000000000000000000000000000000017615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197

bip0340_11 :: Bool
bip0340_11 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B

bip0340_12 :: Bool
bip0340_12 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B

bip0340_13 :: Bool
bip0340_13 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

bip0340_14 :: Bool
bip0340_14 = fast_bip0340_check ((pk,m),sig)
 where
  pk = toWord256 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B

bip0340_tests :: Bool
bip0340_tests = Prelude.and [bip0340_0, bip0340_1, bip0340_2, bip0340_3, bip0340_4]
             && Prelude.not (Prelude.or [bip0340_5, bip0340_6, bip0340_7, bip0340_8, bip0340_9, bip0340_10, bip0340_11, bip0340_12, bip0340_13, bip0340_14])
