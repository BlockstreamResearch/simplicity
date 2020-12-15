-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Prelude hiding (sqrt, all)
import Control.Arrow ((***))
import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import Data.ByteString.Short (toShort)
import qualified Data.List as L
import Lens.Family2 ((^..), allOf, zipWithOf)
import Lens.Family2.Stock (backwards, both_)

import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.*.), (.^.))
import qualified Simplicity.LibSecp256k1.Spec as LibSecpSpec
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.LibSecp256k1.Lib as LibSecp
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.Word
import Simplicity.Term.Core
import Simplicity.Ty.Word as Ty
import qualified Simplicity.Word as W

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), Assertion, testCase)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property,
                              arbitraryBoundedIntegral, choose, elements, forAll, resize, sized, testProperty)

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
        , testProperty "add word8" prop_add8
        , testProperty "full_increment word8" prop_full_increment8
        , testProperty "increment word8" prop_increment8
        , testProperty "full_subtract word8" prop_full_subtract8
        , testProperty "subtract word8" prop_subtract8
        , testProperty "negate word8" prop_negate8
        , testProperty "full_decrement word8" prop_full_decrement8
        , testProperty "decrement word8" prop_decrement8
        , testProperty "fullMultiply word8" prop_full_multiply8
        , testProperty "multiply word8" prop_multiply8
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
prop_add8 :: Word8 -> Word8 -> Bool
prop_add8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y
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

prop_negate8 :: Word8 -> Word8 -> Bool
prop_negate8 x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) - fromWord8 x
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
prop_multiply8 :: Word8 -> Word8 -> Bool
prop_multiply8 x y = fromWord16 (Arith.multiply word8 (x, y)) == fromWord8 x * fromWord8 y

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

toFE :: LibSecpSpec.FE -> FE
toFE = toWord256 . toInteger . LibSecpSpec.fePack

maybeToTy :: Maybe a -> Either () a
maybeToTy Nothing = Left ()
maybeToTy (Just x) = Right x

genModularWord256 w = do
  b <- arbitrary
  i <- arbitrary
  return $ fromInteger i + if b then w else 0

data FieldElement = FieldElement W.Word256 deriving Show

instance Arbitrary FieldElement where
  arbitrary = FieldElement <$> genModularWord256 (LibSecpSpec.fePack (LibSecpSpec.neg LibSecpSpec.feOne) + 1)
  shrink (FieldElement fe) = FieldElement <$> takeWhile (<fe) [0, 1, order - 1, order, order + 1]
   where
    order = LibSecpSpec.fePack (LibSecpSpec.neg LibSecpSpec.feOne) + 1

feAsTy (FieldElement w) = toWord256 (toInteger w)
feAsSpec (FieldElement w) = LibSecpSpec.unrepr (toInteger w)

prop_normalize :: FieldElement -> Bool
prop_normalize a = normalize (feAsTy a) == toFE (feAsSpec a)

fe_unary_prop f g = \a -> fastF (feAsTy a) == Just (toFE (g (feAsSpec a)))
 where
  fastF = fastCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == Just (toFE (g (feAsSpec a) (feAsSpec b)))
 where
  fastF = fastCoreEval f

prop_add :: FieldElement -> FieldElement -> Bool
prop_add = fe_binary_prop LibSecp.add LibSecpSpec.add

prop_mul :: FieldElement -> FieldElement -> Bool
prop_mul = fe_binary_prop mul LibSecpSpec.mul

prop_sqr :: FieldElement -> Bool
prop_sqr = fe_unary_prop sqr LibSecpSpec.sqr

prop_neg :: FieldElement -> Bool
prop_neg = fe_unary_prop neg LibSecpSpec.neg

prop_inv :: FieldElement -> Bool
prop_inv = fe_unary_prop inv LibSecpSpec.inv

prop_sqrt :: FieldElement -> Bool
prop_sqrt = \a -> fastSqrt (feAsTy a) == Just ((fmap toFE . maybeToTy) (LibSecpSpec.sqrt (feAsSpec a)))
 where
  fastSqrt = fastCoreEval sqrt

toGE :: LibSecpSpec.GE -> GE
toGE (LibSecpSpec.GE x y) = (toFE x, toFE y)

toGEJ :: LibSecpSpec.GEJ -> GEJ
toGEJ (LibSecpSpec.GEJ x y z) = ((toFE x, toFE y), toFE z)

data GroupElement = GroupElement FieldElement FieldElement deriving Show

instance Arbitrary GroupElement where
  arbitrary = GroupElement <$> arbitrary <*> arbitrary
  shrink (GroupElement x y) = [GroupElement x' y' | (x', y') <- shrink (x, y)]

geAsTy (GroupElement x y) = (feAsTy x, feAsTy y)
geAsSpec (GroupElement x y) = LibSecpSpec.GE (feAsSpec x) (feAsSpec y)

data GroupElementJacobian = GroupElementJacobian FieldElement FieldElement FieldElement deriving Show

instance Arbitrary GroupElementJacobian where
  arbitrary = GroupElementJacobian <$> arbitrary <*> arbitrary <*> arbitrary
  shrink (GroupElementJacobian x y z) = [GroupElementJacobian x' y' z' | (x', y', z') <- shrink (x, y, z)]

gejAsTy (GroupElementJacobian x y z) = ((feAsTy x, feAsTy y), feAsTy z)
gejAsSpec (GroupElementJacobian x y z) = LibSecpSpec.GEJ (feAsSpec x) (feAsSpec y) (feAsSpec z)

gen_inf :: Gen GroupElementJacobian
gen_inf = GroupElementJacobian <$> arbitrary <*> arbitrary <*> pure (FieldElement 0)

prop_double :: GroupElementJacobian -> Bool
prop_double = \a -> fastDouble (gejAsTy a) == Just (toGEJ (LibSecpSpec.double (gejAsSpec a)))
 where
  fastDouble = fastCoreEval double

prop_double_inf :: Property
prop_double_inf = forAll gen_inf $ prop_double

prop_offsetPointEx :: GroupElementJacobian -> GroupElement -> Bool
prop_offsetPointEx = \a b ->
  let rzc = fastOffsetPointEx (gejAsTy a, geAsTy b)
      (rz', c') = LibSecpSpec.offsetPointEx (gejAsSpec a) (geAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fastOffsetPointEx = fastCoreEval offsetPointEx

prop_offsetPointEx_double :: FieldElement -> GroupElement -> Bool
prop_offsetPointEx_double z b@(GroupElement bx by) = prop_offsetPointEx a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . LibSecpSpec.fePack $ bx' .*. z' .^. 2)
                           (FieldElement . LibSecpSpec.fePack $ by' .*. z' .^. 3)
                           z

prop_offsetPointEx_opp :: FieldElement -> GroupElement -> Bool
prop_offsetPointEx_opp z b@(GroupElement bx by) = prop_offsetPointEx a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . LibSecpSpec.fePack $ bx' .*. z' .^. 2)
                           (FieldElement . LibSecpSpec.fePack . LibSecpSpec.neg $ by' .*. z' .^. 3)
                           z

prop_offsetPointEx_inf b = forAll gen_inf $ \a -> prop_offsetPointEx a b

data ScalarElement = ScalarElement W.Word256 deriving Show

instance Arbitrary ScalarElement where
  arbitrary = sized $ \n -> if n == 0 then return . ScalarElement $ case1 else resize (n-1) $ do
    i <- arbitrary
    j <- arbitrary
    e <- elements [0, 2^255, order, halforder]
    return . ScalarElement $ fromInteger i + (fromInteger j * lambda `mod` order) + e
   where
    -- This denormailzed scalar would produce a different result on split-lambda than the canonical scalar due to
    -- the approximate division used in the implementation.
    case1 = order + c
     where
      c = 0x8f8da4d57dc094c4ecdd5448564d85f6 -- 2^383 `div` g2 + 1
    order = LibSecpSpec.scalarPack maxBound + 1
    halforder = order `div` 2
    lambda = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
  shrink (ScalarElement se) = ScalarElement <$> filter (<se) [0, 1, 2^256-1, 2^255-1, 2^255, 2^255+1, order - 1, order, order + 1, halforder -1, halforder, halforder + 1, halforder + 2]
   where
    order = LibSecpSpec.scalarPack maxBound + 1
    halforder = order `div` 2

scalarAsTy (ScalarElement w) = toWord256 (toInteger w)
scalarAsSpec (ScalarElement w) = LibSecpSpec.scalarUnrepr (toInteger w)

toScalar :: LibSecpSpec.Scalar -> FE
toScalar a = toWord256 . toInteger $ LibSecpSpec.scalarPack a

prop_scalarSplitLambda :: ScalarElement -> Bool
prop_scalarSplitLambda = \a -> ((interp *** interp) <$> fastSplit (scalarAsTy a))
                            == Just (LibSecpSpec.scalarSplitLambda (scalarAsSpec a))
 where
  interp (b,x) = fromWord128 x - if fromBit b then 2^128 else 0
  fastSplit = fastCoreEval scalarSplitLambda

data WnafElement = WnafElement { wnafAsSpec :: Integer } deriving Show

instance Arbitrary WnafElement where
  arbitrary = WnafElement <$> choose (-2^128, 2^128-1)
  shrink (WnafElement we) = WnafElement <$> shrink we

wnafAsTy :: WnafElement -> (Bit, Word128)
wnafAsTy (WnafElement we) = (toBit (we < 0), toWord128 we)

traverseWnaf f (x,y) = (,) <$> f x <*> (both_.both_.both_.both_.both_.both_.both_) f y

prop_wnaf5 :: WnafElement -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (LibSecpSpec.wnaf 5 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap fromWord4 <$> wnaf5 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^4 + x
           | otherwise = x

prop_wnaf15 :: WnafElement -> Bool
prop_wnaf15 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (LibSecpSpec.wnaf 15 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap (fromWord16) <$> wnaf15 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1

prop_ecMult :: GroupElementJacobian -> ScalarElement -> ScalarElement -> Bool
prop_ecMult = \a na ng -> fastEcMult ((gejAsTy a, scalarAsTy na), scalarAsTy ng) == Just (toGEJ (LibSecpSpec.ecMult (gejAsSpec a) (scalarAsSpec na) (scalarAsSpec ng)))
 where
  fastEcMult = fastCoreEval ecMult

prop_ecMult0 :: GroupElementJacobian -> ScalarElement -> Bool
prop_ecMult0 a ng = prop_ecMult a na ng
 where
  na = ScalarElement 0

prop_ecMult_inf :: ScalarElement -> ScalarElement -> Property
prop_ecMult_inf na ng = forAll gen_inf $ \a -> prop_ecMult a na ng

prop_pkPoint :: FieldElement -> Bool
prop_pkPoint a@(FieldElement w) = pkPoint (feAsTy a) == (fmap toGEJ . maybeToTy) (LibSecpSpec.pkPoint (LibSecpSpec.XOnlyPubKey w))

prop_sigUnpack :: FieldElement -> ScalarElement -> Bool
prop_sigUnpack r@(FieldElement wr) s@(ScalarElement ws) =
  sigUnpack (feAsTy r, scalarAsTy s) == (fmap (toFE *** toScalar) . maybeToTy) (LibSecpSpec.sigUnpack (LibSecpSpec.Sig wr ws))

prop_scalarUnrepr :: ScalarElement -> Bool
prop_scalarUnrepr a@(ScalarElement w) = scalarUnrepr (scalarAsTy a) == toScalar (LibSecpSpec.scalarUnrepr (toInteger w))

fastSchnorrVerify = fromJust . fastCoreEval schnorrVerify
 where
  fromJust (Just a) = fromBit a
  fromJust Nothing = False

schnorr0 :: Bool
schnorr0 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  m = toWord256 0
  sig = toWord512 0x528F745793E8472C0329742A463F59E58F3A3F1A4AC09C28F6F8514D4D0322A258BD08398F82CF67B812AB2C7717CE566F877C2F8795C846146978E8F04782AE

schnorr1 :: Bool
schnorr1 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E844160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr2 :: Bool
schnorr2 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x2D941B38E32624BF0AC7669C0971B990994AF6F9B18426BF4F4E7EC10E6CDF386CF646C6DDAFCFA7F1993EEB2E4D66416AEAD1DDAE2F22D63CAD901412D116C6

schnorr3 :: Bool
schnorr3 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517
  m = toWord256 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  sig = toWord512 0x8BD2C11604B0A87A443FCC2E5D90E5328F934161B18864FB48CE10CB59B45FB9B5B2A0F129BD88F5BDC05D5C21E5C57176B913002335784F9777A24BD317CD36

schnorr4 :: Bool
schnorr4 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9
  m = toWord256 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
  sig = toWord512 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63EE374AC7FAE927D334CCB190F6FB8FD27A2DDC639CCEE46D43F113A4035A2C7F

schnorr5 :: Bool
schnorr5 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xEEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E844160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr6 :: Bool
schnorr6 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9935554D1AA5F0374E5CDAACB3925035C7C169B27C4426DF0A6B19AF3BAEAB138

schnorr7 :: Bool
schnorr7 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x10AC49A6A2EBF604189C5F40FC75AF2D42D77DE9A2782709B1EB4EAF1CFE9108D7003B703A3499D5E29529D39BA040A44955127140F81A8A89A96F992AC0FE79

schnorr8 :: Bool
schnorr8 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E84BE9F4303C0B9913470532E6521A827951D39F5C631CFD98CE39AC4D7A5A83BA9

schnorr9 :: Bool
schnorr9 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000099D2F0EBC2996808208633CD9926BF7EC3DAB73DAAD36E85B3040A698E6D1CE0

schnorr10 :: Bool
schnorr10 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000124E81D89F01304695CE943F7D5EBD00EF726A0864B4FF33895B4E86BEADC5456

schnorr11 :: Bool
schnorr11 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000124E81D89F01304695CE943F7D5EBD00EF726A0864B4FF33895B4E86BEADC5456

schnorr12 :: Bool
schnorr12 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F4160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr13 :: Bool
schnorr13 = fastSchnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E84FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

schnorr_tests :: Bool
schnorr_tests = Prelude.and [schnorr0, schnorr1, schnorr2, schnorr3, schnorr4]
             && Prelude.not (Prelude.or [schnorr5, schnorr6, schnorr7, schnorr8, schnorr9, schnorr10, schnorr11, schnorr12, schnorr13])
