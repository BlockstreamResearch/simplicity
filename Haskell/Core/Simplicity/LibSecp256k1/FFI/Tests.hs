module Simplicity.LibSecp256k1.FFI.Tests
 ( tests
 , main
 ) where

import Control.Arrow ((***))
import Lens.Family2 ((^.), (^..), over, allOf, review, zipWithOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck ( Arbitrary(..), arbitrarySizedBoundedIntegral, shrinkIntegral
                             , choose, forAll, testProperty
                             )
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import Simplicity.Digest
import Simplicity.LibSecp256k1.FFI as C
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.Word

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "field"
        [ -- hunit_feIsZero_true "C" C.feIsZero
--        , hunit_feIsZero_true "Spec" Spec.feIsZero
--        , testProperty "fePack" prop_fePack
--        , testProperty "feUnpack" prop_feUnpack
        {-,-} testProperty "feIsZero" prop_feIsZero
        , testProperty "neg" prop_neg
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
        , testProperty "offsetPointEx_all" prop_offsetPointEx_all
        , testProperty "offsetPointEx_double" prop_offsetPointEx_double
        , testProperty "offsetPointEx_opp" prop_offsetPointEx_opp
        , testProperty "offsetPointEx_inf" prop_offsetPointEx_inf
        , testProperty "offsetPointZinv_all" prop_offsetPointZinv_all
        , testProperty "offsetPointZinv_double" prop_offsetPointZinv_double
        , testProperty "offsetPointZinv_opp" prop_offsetPointZinv_opp
        , testProperty "offsetPointZinv_inf" prop_offsetPointZinv_inf
        , testProperty "pointMulLambda" prop_pointMulLambda
        , testProperty "eqXCoord" prop_eqXCoord
        , testProperty "eqXCoord_true" prop_eqXCoord_true
        ]
      , testGroup "scalar"
        [ hunit_scalarNegate_zero
        , testProperty "scalarNegate" prop_scalarNegate
        , testProperty "scalarSplitLambda" prop_scalarSplitLambda
        , testProperty "scalarSplit128" prop_scalarSplit128
        ]
      , testGroup "ecMult"
        [ testProperty "wnaf 5" (prop_wnaf 5)
        , testProperty "wnaf 15" (prop_wnaf 15)
        , testProperty "ecMult_inf" prop_ecMult_inf
        , testProperty "ecMult0" prop_ecMult0
        , testProperty "ecMult" prop_ecMult
        ]
--      , testGroup "ecMult"
--        [ testProperty "schnorr_almost_always_false" schnorr_almost_always_false
--        , hunit_schnorr
      ] -- ]

instance Arbitrary Word256 where
  arbitrary = arbitrarySizedBoundedIntegral
  shrink = shrinkIntegral

instance Arbitrary FE where
  arbitrary = mkFE <$> arbitrary
   where
    mkFE :: Word256 -> FE
    mkFE = unrepr . toInteger

instance Arbitrary GE where
  arbitrary = GE <$> arbitrary <*> arbitrary

instance Arbitrary GEJ where
  arbitrary = review gej arbitrary

instance Arbitrary Scalar where
  arbitrary = mkScalar <$> arbitrary
   where
    mkScalar :: Word256 -> Scalar
    mkScalar = scalarUnrepr . toInteger

eq_fe = (==)
eq_ge (GE x1 y1) (GE x2 y2) = (eq_fe x1 x2) && (eq_fe y1 y2)
eq_gej = zipWithOf (allOf gej) eq_fe
eq_fe_gej (a0,a1) (b0,b1) = (eq_fe a0 b0) && (eq_gej a1 b1)

{-
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
-}

-- prop_fePack a = C.fePack a == Spec.fePack a
-- prop_feUnpack w = C.feUnpack w `eq_fe` Spec.feUnpack w
prop_feIsZero a = C.feIsZero a == Spec.feIsZero a -- feIsZero will essentially always be false on random inputs.
prop_neg a = C.neg a `eq_fe` Spec.neg a
prop_add a b = C.add a b `eq_fe` Spec.add a b
prop_mul a b = C.mul a b `eq_fe` Spec.mul a b
prop_sqr a = C.sqr a `eq_fe` Spec.sqr a
prop_inv a = C.inv a `eq_fe` Spec.inv a
prop_sqrt a = C.sqrt a == Spec.sqrt a

gen_inf = GEJ <$> arbitrary <*> arbitrary <*> pure feZero

prop_double_inf = forAll gen_inf prop_double
prop_double a = C.double a `eq_gej` Spec.double a

prop_addPoint a b = C.addPoint a b `eq_gej` mappend a b
prop_addPoint_double z a = prop_addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (a^._y .*. z3) (a^._z .*. z)
prop_addPoint_opp z a = prop_addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (C.neg (a^._y .*. z3)) (a^._z .*. z)
prop_addPoint_inf = forAll gen_inf $ \a -> forAll gen_inf $ \b -> prop_addPoint a b
prop_addPoint_inf_l b = forAll gen_inf $ \a -> prop_addPoint a b
prop_addPoint_inf_r a = forAll gen_inf $ \b -> prop_addPoint a b
prop_offsetPointEx a b = C.offsetPointEx a b `eq_fe_gej` Spec.offsetPointEx a b
prop_offsetPointEx_all a bx by = prop_offsetPointEx a b
 where
  b = GE bx by
prop_offsetPointEx_double z bx by = prop_offsetPointEx a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) z
  b = GE bx by
prop_offsetPointEx_opp z bx by = prop_offsetPointEx a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg (by .*. z3)) z
  b = GE bx by
prop_offsetPointEx_inf bx by = forAll gen_inf $ \a -> prop_offsetPointEx a b
 where
  b = GE bx by
prop_offsetPointZinv a b bz = C.offsetPointZinv a b bz `eq_gej` Spec.offsetPointZinv a b bz
prop_offsetPointZinv_all a b = prop_offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_offsetPointZinv_double z b = prop_offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_opp z b = prop_offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg (by .*. z3)) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_inf b = forAll gen_inf $ \a -> prop_offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b

prop_pointMulLambda a = C.pointMulLambda a `eq_ge` Spec.pointMulLambda a

prop_eqXCoord x a = C.eqXCoord x a == Spec.eqXCoord x a -- eqXCoord will essentially always be false on random inputs.
prop_eqXCoord_true x y z = prop_eqXCoord x (GEJ (x .*. z2) y z)
 where
  z2 = C.sqr z

hunit_scalarNegate_zero = testCase "scalarNegate_zero" (assertEqual "" (C.scalarNegate scalarZero) (Spec.scalarNegate scalarZero))
prop_scalarNegate a = C.scalarNegate a == Spec.scalarNegate a

prop_wnaf n a = C.wnaf n (scalarUnrepr a) == map f (Spec.wnaf n a)
 where
  f Nothing = 0
  f (Just x) = 2*x+1

prop_scalarSplitLambda x = C.scalarSplitLambda x == (scalarUnrepr *** scalarUnrepr) (Spec.scalarSplitLambda x)
prop_scalarSplit128 x = C.scalarSplit128 x == (scalarUnrepr *** scalarUnrepr) (Spec.scalarSplit128 x)

prop_ecMult x y z = C.ecMult x y z `eq_gej` Spec.ecMult x y z
prop_ecMult0 x z = prop_ecMult x y z
 where
  y = scalarZero
prop_ecMult_inf y z = forAll gen_inf $ \x -> prop_ecMult x y z

schnorr_almost_always_false px m r s = not $ schnorr (XOnlyPubKey px) (review (over be256) m) (Sig r s)

hunit_schnorr = testGroup "schnorr"
              $ [ testCase "vector 0" (assertBool "schnorr" $ 
                  schnorr (XOnlyPubKey 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9)
                          (conv 0)
                          (Sig 0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215
                               0x25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0))
                , testCase "vector 1" (assertBool "schnorr" $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv pi)
                          (Sig 0x6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE3341
                               0x8906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A))
                , testCase "vector 2" (assertBool "schnorr" $
                  schnorr (XOnlyPubKey 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8)
                          (conv 0x7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1B
                               0xAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7))
                , testCase "vector 3" (assertBool "schnorr" $
                  schnorr (XOnlyPubKey 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517)
                          (conv (-1))
                          (Sig 0x7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC
                               0x97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3))
                , testCase "vector 4" (assertBool "schnorr" $
                  schnorr (XOnlyPubKey 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9)
                          (conv bla)
                          (Sig 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63
                               0x76AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4))
                , testCase "vector 5" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xEEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34)
                          (conv pi)
                          (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                               0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 6" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A1460297556
                               0x3CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2))
                , testCase "vector 7" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F
                               0x28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD))
                , testCase "vector 8" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                               0x961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6))
                , testCase "vector 9" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x0000000000000000000000000000000000000000000000000000000000000000
                               0x123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051))
                , testCase "vector 10" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x0000000000000000000000000000000000000000000000000000000000000001
                               0x7615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197))
                , testCase "vector 11" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D
                               0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 12" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
                               0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 13" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                               0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141))
                , testCase "vector 14" (assertBool "not schnorr" . not $
                  schnorr (XOnlyPubKey 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30)
                          (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                          (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                               0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                ]
 where
  conv :: Word256 -> Hash256
  conv = review (over be256)
  pi = 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  bla = 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
