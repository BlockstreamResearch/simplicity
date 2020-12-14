module Simplicity.LibSecp256k1.Spec
 ( fieldOrder, groupOrder, beta, lambda
 , FE, fe, fe_repr, fe_pack
 , fe_zero, fe_one
 , fe_is_zero, fe_is_odd
 , fe_negate, fe_add, fe_multiply, fe_square, fe_invert, fe_square_root
 , (.+.), (.-.), (.*.), (.^.)
 , GEJ(..), _gej, gej, _x, _y, _z
 , GE(..)
 , gej_normalize
 , gej_double, gej_add_ex, gej_ge_add_ex, gej_ge_add_zinv
 , ge_negate, ge_scale_lambda
 , gej_x_equiv, gej_y_is_odd
 , Scalar, scalar, scalar_repr, scalar_pack
 , scalar_zero, scalar_negate, scalar_split_lambda, scalar_split_128
 , wnaf, linear_combination_1
 , PubKey(..), pubkey_unpack, pubkey_unpack_neg, pubkey_unpack_quad
 , Sig(..), signature_unpack
 , bip0340_check
 ) where


import Control.Monad (guard)
import Control.Monad.Trans.RWS hiding (put)
import Control.Monad.Trans.State (state, evalState)
import Data.Bits ((.&.), (.|.), finiteBitSize)
import Data.ByteString.Short (ShortByteString, pack)
import qualified Data.ByteString.Char8 as BSC
import Data.Ix (inRange)
import Data.List (mapAccumL, mapAccumR, unfoldr)
import Data.Maybe (isJust)
import Data.Serialize (put)
import Data.Serialize.Put (putShortByteString, runPut)
import qualified Data.Vector as V
import Lens.Family2 ((^.), (^..), (&), (+~), (*~), (%~), over, review, under, zipWithOf)
import Lens.Family2.Stock (_1, lend_, some_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

infixl 6 .+., .-.
infixl 7 .*.
infixr 8 .^.

fieldOrder :: Integer
fieldOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

groupOrder :: Integer
groupOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

beta :: Integer
beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

lambda :: Integer
lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

data FE = FE { fe_pack :: Word256 }
  deriving (Eq, Show)

fe_repr :: FE -> Integer
fe_repr = toInteger . fe_pack

fe :: Integer -> FE
fe n = FE . fromInteger $ n `mod` fieldOrder

fe_zero :: FE
fe_zero = fe 0

fe_one :: FE
fe_one = fe 1

fe_seven :: FE
fe_seven = fe 7

fe_beta :: FE
fe_beta = fe beta

fe_unpack :: Word256 -> Maybe FE
fe_unpack x0 = guard (x == fe_repr a) >> return a
 where
  x = toInteger x0
  a = fe x

fe_is_odd :: FE -> Bool
fe_is_odd = odd . fe_repr

fe_is_zero :: FE -> Bool
fe_is_zero = (0 ==) . fe_repr

fe_negate :: FE -> FE
fe_negate = fe . negate . fe_repr

fe_add :: FE -> FE -> FE
fe_add a b = fe (fe_repr a + fe_repr b)

fe_multiply :: FE -> FE -> FE
fe_multiply a b = fe (fe_repr a * fe_repr b)

fe_square :: FE -> FE
fe_square a = fe_multiply a a

mulInt :: Integer -> FE -> FE
mulInt i a = fe_multiply (fe i) a

(.+.) = fe_add
(.*.) = fe_multiply
x .-. y = fe_add x (fe_negate y)
x .^. n = go x (n `mod` (fieldOrder - 1))
 where
  go x 0 = fe_zero
  go x 1 = x
  go x n | even n = go (fe_square x) (n `div` 2)
         | odd n = fe_multiply x (go (fe_square x) (n `div` 2))

fe_invert :: FE -> FE
fe_invert a = a .^. (fieldOrder - 2)

fe_square_root :: FE -> Maybe FE
fe_square_root a | 0 == (fieldOrder + 1) `mod` 4 = do
  let res = a .^. ((fieldOrder + 1) `div` 4)
  guard $ fe_is_zero (fe_square res .-. a)
  return res

isQuad :: FE -> Bool
isQuad = isJust . fe_square_root

data GEJ = GEJ !FE !FE !FE
  deriving Show

-- GEJ has a traversal.
_gej :: Applicative f => (FE -> f FE) -> GEJ -> f GEJ
_gej = under gej

-- GEJ has both a traversal and a grate.
gej :: (Functor g, Applicative f) => (g FE -> f FE) -> g GEJ -> f GEJ
gej f a = GEJ <$> f ((^._x) <$> a)
              <*> f ((^._y) <$> a)
              <*> f ((^._z) <$> a)

_x f (GEJ x y z) = (\x -> GEJ x y z) <$> f x
_y f (GEJ x y z) = (\y -> GEJ x y z) <$> f y
_z f (GEJ x y z) = (\z -> GEJ x y z) <$> f z

isInf :: GEJ -> Bool
isInf a = fe_is_zero (a^._z)

gej_double :: GEJ -> GEJ
gej_double a@(GEJ x y z) | isInf a = mempty
                     | otherwise = GEJ x' y' z'
 where
  x' = mulInt 9 (x .^. 4) .+. mulInt (-8) (x .*. y .^. 2)
  y' = mulInt 36 (x .^. 3 .*. y .^. 2) .+. mulInt (-27) (x .^. 6) .+. mulInt (-8) (y .^. 4)
  z' = mulInt 2 (y .*. z)

gej_add_ex :: GEJ -> GEJ -> (FE, GEJ)
gej_add_ex a@(GEJ ax ay az) b@(GEJ bx by bz) | isInf a = (fe_zero, GEJ bx by bz)
                                                       | isInf b = (fe_one, a)
                                                       | isZeroH && isZeroI = (mulInt 2 ay, gej_double a)
                                                       | isZeroH = (fe_zero, mempty)
                                                       | otherwise = (bz .*. h, GEJ x y z)
 where
  u1 = ax .*. bz .^. 2
  u2 = bx .*. az .^. 2
  s1 = ay .*. bz .^. 3
  s2 = by .*. az .^. 3
  h = u2 .-. u1
  i = s2 .-. s1
  isZeroH = fe_is_zero h
  isZeroI = fe_is_zero i
  z = az .*. bz .*. h
  t = u1 .*. h .^. 2
  x = i .^. 2 .+. mulInt (-2) t .-. h .^. 3
  y = (t .-. x) .*. i .-. h .^. 3 .*. s1

instance Semigroup GEJ where
  (<>) = mappend

instance Monoid GEJ where
  mempty = GEJ fe_zero fe_zero fe_zero
  mappend a b = snd $ gej_add_ex a b

gej_x_equiv :: GEJ -> FE -> Bool
gej_x_equiv a x = fe_is_zero $ (fe_square (a^._z) .*. x) .-. (a^._x)

gej_y_is_odd :: GEJ -> Bool
gej_y_is_odd a@(GEJ _ y z) | isInf a = False
                           | otherwise = fe_is_odd $ y .*. invz .^. 3
 where
  invz = fe_invert z

data GE = GE !FE !FE -- Infinity not included.
        deriving Show

gej_ge_add_ex :: GEJ -> GE -> (FE, GEJ)
gej_ge_add_ex a (GE bx by) = gej_add_ex a (GEJ bx by fe_one)

gej_ge_add_zinv :: GEJ -> GE -> FE -> GEJ
gej_ge_add_zinv a (GE bx by) bzinv = snd $ gej_ge_add_ex a (GE (bx .*. bzinv .^. 2) (by .*. bzinv .^. 3))

gej_normalize :: GEJ -> GE
gej_normalize (GEJ x y z) = GE (x .*. invz .^. 2) (y .*. invz .^. 3)
 where
  invz = fe_invert z

ge_negate :: GE -> GE
ge_negate (GE x y) = GE x (fe_negate y)

ge_scale_lambda :: GE -> GE
ge_scale_lambda (GE x y) = GE (x .*. fe_beta) y

newtype Scalar = Scalar { scalar_pack :: Word256 } deriving (Eq, Show)

instance Bounded Scalar where
  minBound = scalar 0
  maxBound = scalar $ groupOrder - 1

scalar_lambda :: Scalar
scalar_lambda = scalar lambda

scalar_repr :: Scalar -> Integer
scalar_repr = toInteger . scalar_pack

scalar :: Integer -> Scalar
scalar x = Scalar $ fromInteger (x `mod` groupOrder)

scalar_unpack :: Word256 -> Maybe Scalar
scalar_unpack x0 = guard (x == scalar_repr s) >> return s
 where
  x = toInteger x0
  s = scalar x

scalar_zero :: Scalar
scalar_zero = Scalar 0

scalar_is_zero :: Scalar -> Bool
scalar_is_zero a = scalar_repr a == 0

scalar_negate :: Scalar -> Scalar
scalar_negate = scalar . negate . scalar_repr

scalar_multiply :: Scalar -> GEJ -> GEJ
scalar_multiply na a = linear_combination_1 na a scalar_zero

scalar_split_lambda :: Scalar -> (Integer, Integer)
scalar_split_lambda k0 = (k1, k2)
 where
  n = groupOrder
  n2 = n `div` 2
  k = scalar_repr k0
  g1 = 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
  g2 = 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
  b1 = -0xe4437ed6010e88286f547fa90abfe4c3
  b2 =  0x3086d221a7d46bcde86c90e49284eb15
  c1 = (k * g1 + 2^383) `div` (2^384)
  c2 = (k * g2 + 2^383) `div` (2^384)
  k2 = - c1*b1 - c2*b2
  k1 = (k - k2 * lambda + n2) `mod` n - n2

scalar_split_128 :: Scalar -> (Integer, Integer)
scalar_split_128 k0 = (k1, k2)
 where
  k = scalar_repr k0
  (k2, k1) = k `divMod` (2^128)

linear_combination_1 :: Scalar -> GEJ -> Scalar -> GEJ
linear_combination_1 na0 a ng = foldr f mempty zips & _z %~ (.*. globalZ)
 where
  na = if isInf a then scalar_zero else na0
  (na1, na2) = scalar_split_lambda na
  (ng1, ng2) = scalar_split_128 ng
  wa = 5
  (tableA, globalZ) | scalar_is_zero na = (V.empty, fe_one)
                    | otherwise = scalarTable wa a
  tableAlam = ge_scale_lambda <$> tableA
  f (Nothing, Nothing, Nothing, Nothing) r0 = gej_double r0
  f (Just a1, Nothing, Nothing, Nothing) r0
                   = snd $ f (Nothing, Nothing, Nothing, Nothing) r0 `gej_ge_add_ex` (tableA ! a1)
  f (a1, Just a2, Nothing, Nothing) r0
                   = snd $ f (a1, Nothing, Nothing, Nothing) r0 `gej_ge_add_ex` (tableAlam ! a2)
  f (a1, a2, Just g1, Nothing) r0
                   = gej_ge_add_zinv (f (a1, a2, Nothing, Nothing) r0) (tableG ! g1) globalZ
  f (a1, a2, g1, Just g2) r0
                   = gej_ge_add_zinv (f (a1, a2, g1, Nothing) r0) (tableG128 ! g2) globalZ
  zipEx [] [] [] [] = []
  zipEx [] bs cs ds = zipEx [Nothing] bs cs ds
  zipEx as [] cs ds = zipEx as [Nothing] cs ds
  zipEx as bs [] ds = zipEx as bs [Nothing] ds
  zipEx as bs cs [] = zipEx as bs cs [Nothing]
  zipEx (a:as) (b:bs) (c:cs) (d:ds) = (a,b,c,d) : zipEx as bs cs ds
  zips = zipEx (wnaf wa na1) (wnaf wa na2) (wnaf wg ng1) (wnaf wg ng2)

wnafInteger :: Int -> Integer -> [Int]
wnafInteger w | 0 < w && w <= finiteBitSize w = unfoldr f
 where
  f 0 = Nothing
  f i = Just (fromInteger x, (i - x) `div` 2)
   where
    x | odd i = ((i + 2^(w-1)) `mod` 2^w) - 2^(w-1)
      | otherwise = 0

wnaf5Simplicity :: Word256 -> [Maybe Int]
wnaf5Simplicity w = snd $ execRWS (mapM_ step4M (ws ++ [ext])) () (False, ws0)
 where
  ws0 : ws = take 64 $ unfoldr (\x -> Just (fromIntegral (x `mod` 16), x `div` 16)) w
  ext | 2^255 <= w = 0xff
      | otherwise  = 0x00

step4M new = rws (\() s -> let (x,y) = step4 new s in ((),x,y))

step4 :: Word8 -> (Bool, Word8) -> ((Bool, Word8), [Maybe Int])
step4 x (carry, new) | new .&. 1 /= carryBit * 1 = run 1
                     | new .&. 2 /= carryBit * 2 = run 2
                     | new .&. 4 /= carryBit * 4 = run 3
                     | new .&. 8 /= carryBit * 8 = run 4
                     | otherwise = ((carry, x), replicate 4 Nothing)
   where
    carryBit = if carry then 1 else 0
    run n = ((newCarry, maskedX), replicate (n-1) Nothing ++ [Just (x1 `div` 2)] ++ replicate (4-n) Nothing)
     where
      x0 = (16*x + new) `div` 2^(n-1)
      x1 | newCarry  = fromIntegral (x0 .&. 31) - 32
         | otherwise = fromIntegral (x0 .&. 31)
      newCarry = x0 .&. 16 /= 0
      maskedX | newCarry = x .|. (2^n - 1)
              | otherwise = x - (x .&. (2^n - 1))

wnaf :: Int -> Integer -> [Maybe Int]
wnaf w s = post <$> wnafInteger w s
 where
  post 0 = Nothing
  post i | odd i = Just $ i `div` 2
         | otherwise = error "Simplicity.LibSecp256k1.Spec: invalid result from wnafInteger"

-- a must not be infinity
scalarTable :: Int -> GEJ -> (V.Vector GE, FE)
scalarTable w a = (V.fromList r, globalZ)
 where
  d = gej_double a
  z = d^._z
  len = 2^(w-2)
  l = take len $ iterate (\p -> gej_ge_add_ex (snd p) (GE (d^._x) (d^._y))) (error "scalarTable: Impossible to access", a')
   where
    a' = a & _x %~ (.*. (z .^. 2))
           & _y %~ (.*. (z .^. 3))
  (Right (globalZ, _), r) = mapAccumR acc (Left z) l
  acc (Left z0) (zr, b) = (Right (b^._z .*. z0, zr), GE (b^._x) (b^._y))
  acc (Right (globalZ, z0)) (zr, b) = (Right (globalZ, z0 .*. zr), GE (b^._x .*. z0 .^. 2) (b^._y .*. z0 .^. 3))

g :: GEJ
g = GEJ (fe 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
        (fe 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
        fe_one

g128 :: GEJ
g128 = iterate gej_double g !! 128

wg = 15

tableG = table wg g

tableG128 = table wg g128

table w p = t & traverse %~ norm
 where
  (t,z) = scalarTable w p
  zinv = fe_invert z
  norm (GE x y) = GE (x .*. zinv .^. 2) (y .*. zinv .^. 3)

(!) :: V.Vector GE -> Int -> GE
t ! i | i >= 0 = t V.! i
      | otherwise = ge_negate (t V.! (-i-1))

pubkey_unpack_quad :: PubKey -> Maybe GEJ
pubkey_unpack_quad (PubKey px) = do
  x <- fe_unpack px
  y <- fe_square_root (x .^. 3 .+. fe_seven)
  return (GEJ x y fe_one)

pubkey_unpack :: PubKey -> Maybe GEJ
pubkey_unpack = (some_ . _y %~ mkEven) . pubkey_unpack_quad
 where
  mkEven y | fe_is_odd y = fe_negate y
           | otherwise = y

pubkey_unpack_neg :: PubKey -> Maybe GEJ
pubkey_unpack_neg = (some_ . _y %~ mkOdd) . pubkey_unpack_quad
 where
  mkOdd y | fe_is_odd y = y
          | otherwise = fe_negate y

signature_unpack :: Sig -> Maybe (FE, Scalar)
signature_unpack (Sig r s) = (,) <$> fe_unpack r <*> scalar_unpack s

bip0340_check :: PubKey  -- ^ public key
              -> Hash256 -- ^ message
              -> Sig     -- ^ signature
              -> Bool
bip0340_check pk m sg = Just () == do
  negp <- pubkey_unpack_neg pk
  (rx, s) <- signature_unpack sg
  let tag = bsHash (BSC.pack "BIP0340/challenge")
  let h = bsHash . runPut $ put tag >> put tag >> put (fe_pack rx) >> put pk >> put m
  let e = scalar . integerHash256 $ h
  let r = linear_combination_1 e negp s
  guard . not $ gej_y_is_odd r
  guard $ gej_x_equiv r rx
