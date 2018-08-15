module Simplicity.LibSecp256k1.FFI.Tests
 ( tests
 , main
 ) where

import Lens.Family2 ((^.), (^..), allOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), choose, forAll, testProperty)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import Simplicity.LibSecp256k1.FFI as C
import Simplicity.LibSecp256k1.Spec as Spec

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "field"
        [ hunit_feIsZero_true "C" C.feIsZero
        , hunit_feIsZero_true "Spec" Spec.feIsZero
        , testProperty "normalizeWeak" prop_normalizeWeak
        , testProperty "normalize" prop_normalize
        , testProperty "feIsZero" prop_feIsZero
        , testProperty "neg" prop_neg
        , testProperty "mulInt" prop_mulInt
        , testProperty "add" prop_add
        , testProperty "mul" prop_mul
        , testProperty "sqr" prop_sqr
        , testProperty "inv" prop_inv
        , testProperty "sqrt" prop_sqrt
        ]
      , testGroup "group"
        [ testProperty "double_inf" prop_double_inf
        , testProperty "double" prop_double
        , testProperty "addPoint" prop_addPoint
        , testProperty "addPoint_double" prop_addPoint_double
        , testProperty "addPoint_opp" prop_addPoint_opp
        , testProperty "addPoint_inf" prop_addPoint_inf
        , testProperty "addPoint_inf_l" prop_addPoint_inf_l
        , testProperty "addPoint_inf_r" prop_addPoint_inf_r
        , testProperty "offsetPoint" prop_offsetPoint
        , testProperty "offsetPoint_double" prop_offsetPoint_double
        , testProperty "offsetPoint_opp" prop_offsetPoint_opp
        , testProperty "offsetPoint_inf" prop_offsetPoint_inf
        , testProperty "offsetPoint_inf_l" prop_offsetPoint_inf_l
        , testProperty "offsetPoint_inf_r" prop_offsetPoint_inf_r
        , testProperty "offsetPointZinv" prop_offsetPointZinv
        , testProperty "offsetPointZinv_double" prop_offsetPointZinv_double
        , testProperty "offsetPointZinv_opp" prop_offsetPointZinv_opp
        , testProperty "offsetPointZinv_inf" prop_offsetPointZinv_inf
        , testProperty "offsetPointZinv_inf_l" prop_offsetPointZinv_inf_l
        , testProperty "offsetPointZinv_inf_r" prop_offsetPointZinv_inf_r
        , testProperty "eqXCoord" prop_eqXCoord
        , testProperty "eqXCoord_true" prop_eqXCoord_true
        , testProperty "hasQuadY" prop_hasQuadY
        ]
      , testGroup "scalar"
        [ hunit_scalarNegate_zero
        , testProperty "scalarNegate" prop_scalarNegate
        ]
      , testGroup "ecMult"
        [ testProperty "wnaf 5" (prop_wnaf 5)
        , testProperty "wnaf 16" (prop_wnaf 16)
        , testProperty "ecMult" prop_ecMult
      ] ]

instance Arbitrary FE where
  arbitrary = review _fe arbitrary

instance Arbitrary GEJ where
  arbitrary = review _gej arbitrary

instance Arbitrary Scalar where
  arbitrary = review _scalar arbitrary

eq_fe = zipWithOf (allOf _fe) (==)
eq_gej = zipWithOf (allOf (_gej._fe)) (==)
eq_fe_gej (a0,a1) (b0,b1) = (eq_fe a0 b0) && (eq_gej a1 b1)

hunit_feIsZero_true name isZero = testGroup ("feIsZero_true: " ++ name)
                           $ [ testCase (show i ++ " * bigZero1") (assertBool "feIsZero" $ isZero (C.mulInt i bigZero1)) | i <- [0..64]]
                          ++ [ testCase (show i ++ " * bigZero2") (assertBool "feIsZero" $ isZero (C.mulInt i bigZero2)) | i <- [1..16]]
                          ++ [ testCase (show (2^i) ++ " * bigZero3 + " ++ show (2^i-1) ++ " * R")
                                        (assertBool "feIsZero" $ isZero (C.mulInt (2^i) bigZero3 .+. C.mulInt (2^i-1) r)) | i <- [0..6]]
                          ++ [ testCase ("zeroIsALie "++show i) (assertBool "feIsZero" $ isZero z) | (i,z) <- zip [1..] zeroIsALie]
 where
  bigZero1 = bigZero
  bigZero2 = FE 0x3FF0BC0 0x3FFEFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0xFFFFFFF
  bigZero3 = FE 0x3F0BC00 0x3FEFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0xFFFFFFFF
  r = FE 0xF4400 0x10000 0 0 0 0 0 0 0 0
  zeroIsALie = [ FE 0xFFF0BFD1 0XFFFF0040 0 0 0 0 0 0 0 0xFFC00000
               , FE 0x3F0BFD1 0XFFFF003F 0 0 0 0 0 0 0 0xFFC00000
               , FE 0x4000000 0XFFFFFFFF 0 0 0 0 0 0 0 0
               , FE 0x7F0BFD1 0XFFFF003E 0 0 0 0 0 0 0 0xFFC00000
               ]

prop_normalizeWeak a = C.normalizeWeak a `eq_fe` Spec.normalizeWeak a
prop_normalize a = C.normalize a `eq_fe` Spec.normalize a
prop_feIsZero a = C.feIsZero a == Spec.feIsZero a -- feIsZero will essentially always be false on random inputs.
prop_neg a = forAll (choose (0, 32)) (\m -> C.neg (fromIntegral m) a `eq_fe` Spec.neg m a)
prop_mulInt a = forAll (choose (0, 32)) (\m -> C.mulInt (fromIntegral m) a `eq_fe` Spec.mulInt m a)
prop_add a b = C.add a b `eq_fe` Spec.add a b
prop_mul a b = C.mul a b `eq_fe` Spec.mul a b
prop_sqr a = C.sqr a `eq_fe` Spec.sqr a
prop_inv a = C.inv a `eq_fe` Spec.inv a
prop_sqrt a = C.sqrt a^..(traverse.fe) == Spec.sqrt a^..(traverse.fe)

gen_inf = GEJ <$> arbitrary <*> arbitrary <*> pure feZero

prop_double_inf = forAll gen_inf $ \a -> C.double a `eq_fe_gej` Spec.double a
prop_double a = C.double a `eq_fe_gej` Spec.double a
prop_addPoint a b = C.addPoint a b `eq_fe_gej` Spec.addPoint a b
prop_addPoint_double z a = C.addPoint a b `eq_fe_gej` Spec.addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (a^._y .*. z3) (a^._z .*. z)
prop_addPoint_opp z a = C.addPoint a b `eq_fe_gej` Spec.addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (C.neg 1 (a^._y .*. z3)) (a^._z .*. z)
prop_addPoint_inf = forAll gen_inf $ \a -> forAll gen_inf $ \b -> C.addPoint a b `eq_fe_gej` Spec.addPoint a b
prop_addPoint_inf_l b = forAll gen_inf $ \a -> C.addPoint a b `eq_fe_gej` Spec.addPoint a b
prop_addPoint_inf_r a = forAll gen_inf $ \b -> C.addPoint a b `eq_fe_gej` Spec.addPoint a b
prop_offsetPoint a bx by = C.offsetPoint a b `eq_fe_gej` Spec.offsetPoint a b
 where
  b = GE bx by
prop_offsetPoint_double z bx by = C.offsetPoint a b `eq_fe_gej` Spec.offsetPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) z
  b = GE bx by
prop_offsetPoint_opp z bx by = C.offsetPoint a b `eq_fe_gej` Spec.offsetPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg 1 (by .*. z3)) z
  b = GE bx by
prop_offsetPoint_inf = forAll gen_inf $ \a -> C.offsetPoint a Infinity `eq_fe_gej` Spec.offsetPoint a Infinity
prop_offsetPoint_inf_l bx by = forAll gen_inf $ \a -> C.offsetPoint a b `eq_fe_gej` Spec.offsetPoint a b
 where
  b = GE bx by
prop_offsetPoint_inf_r a = C.offsetPoint a Infinity `eq_fe_gej` Spec.offsetPoint a Infinity
prop_offsetPointZinv a b = C.offsetPointZinv a (GE bx by) bz `eq_gej` Spec.offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_offsetPointZinv_double z b = C.offsetPointZinv a (GE bx by) bz `eq_gej` Spec.offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_opp z b = C.offsetPointZinv a (GE bx by) bz `eq_gej` Spec.offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg 1 (by .*. z3)) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_inf bzinv = forAll gen_inf $ \a -> C.offsetPointZinv a Infinity bzinv `eq_gej` Spec.offsetPointZinv a Infinity bzinv
prop_offsetPointZinv_inf_l b = forAll gen_inf $ \a -> C.offsetPointZinv a (GE bx by) bz `eq_gej` Spec.offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_offsetPointZinv_inf_r a bz = C.offsetPointZinv a Infinity bz `eq_gej` Spec.offsetPointZinv a Infinity bz
prop_eqXCoord x a = C.eqXCoord x a == Spec.eqXCoord x a -- eqXCoord will essentially always be false on random inputs.
prop_eqXCoord_true x y z = C.eqXCoord x (GEJ (x .*. z2) y z) == Spec.eqXCoord x (GEJ (x .*. z2) y z)
 where
  z2 = C.sqr z
prop_hasQuadY a = C.hasQuadY a == Spec.hasQuadY a

hunit_scalarNegate_zero = testCase "scalarNegate_zero" (assertEqual "" (C.scalarNegate scalarZero) (Spec.scalarNegate scalarZero))
prop_scalarNegate a = C.scalarNegate a == Spec.scalarNegate a

prop_wnaf n a = C.wnaf n a == Spec.wnaf n a
prop_ecMult x y z = C.ecMult x y z `eq_gej` Spec.ecMult x y z
