module Simplicity.LibSecp256k1.Spec
 ( FE, unrepr, feZero, feOne
 , GEJ(..), _gej, gej, _x, _y, _z
 , GE(..)
 , Scalar, scalarUnrepr, scalarZero
 , fePack, scalarPack
 , feIsZero, feOdd, neg, add, mul, sqr, inv, sqrt, (.+.), (.-.), (.*.), (.^.)
 , pointNormalize
 , double, offsetPointEx, offsetPointZinv
 , pointMulLambda
 , eqXCoord, hasQuadY
 , scalarNegate, scalarSplitLambda, scalarSplit128
 , wnaf, ecMult
 , XOnlyPubKey(..), pkPoint
 , Sig(..), sigUnpack
 , schnorr
 ) where

import Data.Bits
import Control.Monad.Trans.RWS hiding (put)

import Prelude hiding (sqrt)
import Control.Monad (guard)
import Control.Monad.Trans.State (state, evalState)
import Data.Bits (finiteBitSize)
import Data.ByteString.Short (ShortByteString, pack)
import qualified Data.ByteString.Char8 as BSC
import Data.Ix (inRange)
import Data.List (mapAccumL, mapAccumR, unfoldr)
import Data.Maybe (isJust)
import Data.Serialize (put)
import Data.Serialize.Put (putShortByteString, runPut)
import qualified Data.Vector as V
import Lens.Family2 ((^.), (^..), (&), (+~), (*~), (%~), over, review, under, zipWithOf)
import Lens.Family2.Stock (_1, lend_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

infixl 6 .+., .-.
infixl 7 .*.
infixr 8 .^.

fieldOrder :: Integer
fieldOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

data FE = FE { fePack :: Word256 }
  deriving (Eq, Show)

repr :: FE -> Integer
repr (FE a) = toInteger a

unrepr :: Integer -> FE
unrepr n = FE . fromInteger $ n `mod` fieldOrder

feZero :: FE
feZero = unrepr 0

feOne :: FE
feOne = unrepr 1

feSeven :: FE
feSeven = unrepr 7

feBeta :: FE
feBeta = unrepr 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

-- :TODO: export this.
normalize :: FE -> FE
normalize = unrepr . repr

feUnpack :: Word256 -> Maybe FE
feUnpack x0 = guard (x == repr a) >> return a
 where
  x = toInteger x0
  a = unrepr x

feOdd :: FE -> Bool
feOdd = odd . repr . normalize

feIsZero :: FE -> Bool
feIsZero = (0 ==) . repr . normalize

neg :: FE -> FE
neg = unrepr . negate . repr

add :: FE -> FE -> FE
add a b = unrepr (repr a + repr b)

mul :: FE -> FE -> FE
mul a b = unrepr (repr a * repr b)

sqr :: FE -> FE
sqr a = mul a a

mulInt :: Integer -> FE -> FE
mulInt i a = mul (unrepr i) a

(.+.) = add
(.*.) = mul
x .-. y = add x (neg y)
x .^. n = go x (n `mod` (fieldOrder - 1))
 where
  go x 0 = feZero
  go x 1 = x
  go x n | even n = go (sqr x) (n `div` 2)
         | odd n = mul x (go (sqr x) (n `div` 2))

inv :: FE -> FE
inv a = a .^. (fieldOrder - 2)

sqrt :: FE -> Maybe FE
sqrt a | 0 == (fieldOrder + 1) `mod` 4 = do
  let res = a .^. ((fieldOrder + 1) `div` 4)
  guard $ feIsZero (sqr res .-. a)
  return res

isQuad :: FE -> Bool
isQuad = isJust . sqrt

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
isInf a = feIsZero (a^._z)

double :: GEJ -> GEJ
double a@(GEJ x y z) | isInf a = mempty
                     | otherwise = GEJ x' y' z'
 where
  x' = mulInt 9 (x .^. 4) .+. mulInt (-8) (x .*. y .^. 2)
  y' = mulInt 36 (x .^. 3 .*. y .^. 2) .+. mulInt (-27) (x .^. 6) .+. mulInt (-8) (y .^. 4)
  z' = mulInt 2 (y .*. z)

addPointEx :: GEJ -> GEJ -> (FE, GEJ)
addPointEx a@(GEJ ax ay az) b@(GEJ bx by bz) | isInf a = (feZero, GEJ bx by bz)
                                                       | isInf b = (feOne, a)
                                                       | isZeroH && isZeroI = (mulInt 2 ay, double a)
                                                       | isZeroH = (feZero, mempty)
                                                       | otherwise = (bz .*. h, GEJ x y z)
 where
  u1 = ax .*. bz .^. 2
  u2 = bx .*. az .^. 2
  s1 = ay .*. bz .^. 3
  s2 = by .*. az .^. 3
  h = u2 .-. u1
  i = s2 .-. s1
  isZeroH = feIsZero h
  isZeroI = feIsZero i
  z = az .*. bz .*. h
  t = u1 .*. h .^. 2
  x = i .^. 2 .+. mulInt (-2) t .-. h .^. 3
  y = (t .-. x) .*. i .-. h .^. 3 .*. s1

instance Semigroup GEJ where
  (<>) = mappend

instance Monoid GEJ where
  mempty = GEJ feZero feZero feZero
  mappend a b = snd $ addPointEx a b

eqXCoord :: FE -> GEJ -> Bool
eqXCoord x a = feIsZero $ (sqr (a^._z) .*. x) .-. (a^._x)

hasQuadY :: GEJ -> Bool
hasQuadY a@(GEJ _ y z) | isInf a = False
                       | otherwise = isQuad (y .*. z)

data GE = GE !FE !FE -- Infinity not included.
        deriving Show

offsetPointEx :: GEJ -> GE -> (FE, GEJ)
offsetPointEx a (GE bx by) = addPointEx a (GEJ bx by feOne)

offsetPointZinv :: GEJ -> GE -> FE -> GEJ
offsetPointZinv a (GE bx by) bzinv = snd $ offsetPointEx a (GE (bx .*. bzinv .^. 2) (by .*. bzinv .^. 3))

pointNormalize :: GEJ -> Maybe GE
pointNormalize (GEJ x y z) | feIsZero z = Nothing
                           | otherwise = Just $ GE (x .*. invz .^. 2) (y .*. invz .^. 3)
 where
  invz = inv z

pointNegate :: GE -> GE
pointNegate (GE x y) = GE x (neg y)

pointMulLambda :: GE -> GE
pointMulLambda (GE x y) = GE (x .*. feBeta) y

scalarModulus :: Word256
scalarModulus = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

newtype Scalar = Scalar { scalarPack :: Word256 } deriving (Eq, Show)

instance Bounded Scalar where
  minBound = Scalar 0
  maxBound = Scalar $ scalarModulus - 1

lambda :: Scalar
lambda = scalarUnrepr 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

scalarUnrepr :: Integer -> Scalar
scalarUnrepr x = Scalar $ fromInteger (x `mod` toInteger scalarModulus)

scalarUnpack :: Word256 -> Maybe Scalar
scalarUnpack x = guard (x == scalarPack s) >> return s
 where
  s = scalarUnrepr (toInteger x)

scalarZero :: Scalar
scalarZero = Scalar 0

scalarIsZero :: Scalar -> Bool
scalarIsZero a = scalarPack a == 0

scalarNegate :: Scalar -> Scalar
scalarNegate = scalarUnrepr . negate . toInteger . scalarPack

scalarMult :: Scalar -> GEJ -> GEJ
scalarMult na a = ecMult a na scalarZero

scalarSplitLambda :: Scalar -> (Integer, Integer)
scalarSplitLambda k0 = (k1, k2)
 where
  n = toInteger scalarModulus
  n2 = n `div` 2
  k = toInteger (scalarPack k0)
  g1 = 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
  g2 = 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
  b1 = -0xe4437ed6010e88286f547fa90abfe4c3
  b2 =  0x3086d221a7d46bcde86c90e49284eb15
  c1 = (k * g1 + 2^383) `div` (2^384)
  c2 = (k * g2 + 2^383) `div` (2^384)
  k2 = - c1*b1 - c2*b2
  k1 = (k - k2 * toInteger (scalarPack lambda) + n2) `mod` n - n2

scalarSplit128 :: Scalar -> (Integer, Integer)
scalarSplit128 k0 = (k1, k2)
 where
  k = toInteger (scalarPack k0)
  (k2, k1) = k `divMod` (2^128)

ecMult :: GEJ -> Scalar -> Scalar -> GEJ
ecMult a na0 ng = foldr f mempty zips & _z %~ (.*. globalZ)
 where
  na = if isInf a then scalarZero else na0
  (na1, na2) = scalarSplitLambda na
  (ng1, ng2) = scalarSplit128 ng
  wa = 5
  (tableA, globalZ) | scalarIsZero na = (V.empty, feOne)
                    | otherwise = scalarTable wa a
  tableAlam = pointMulLambda <$> tableA
  f (Nothing, Nothing, Nothing, Nothing) r0 = double r0
  f (Just a1, Nothing, Nothing, Nothing) r0
                   = snd $ f (Nothing, Nothing, Nothing, Nothing) r0 `offsetPointEx` (tableA ! a1)
  f (a1, Just a2, Nothing, Nothing) r0
                   = snd $ f (a1, Nothing, Nothing, Nothing) r0 `offsetPointEx` (tableAlam ! a2)
  f (a1, a2, Just g1, Nothing) r0
                   = offsetPointZinv (f (a1, a2, Nothing, Nothing) r0) (tableG ! g1) globalZ
  f (a1, a2, g1, Just g2) r0
                   = offsetPointZinv (f (a1, a2, g1, Nothing) r0) (tableG128 ! g2) globalZ
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
  d = double a
  z = d^._z
  len = 2^(w-2)
  l = take len $ iterate (\p -> offsetPointEx (snd p) (GE (d^._x) (d^._y))) (error "scalarTable: Impossible to access", a')
   where
    a' = a & _x %~ (.*. (z .^. 2))
           & _y %~ (.*. (z .^. 3))
  (Right (globalZ, _), r) = mapAccumR acc (Left z) l
  acc (Left z0) (zr, b) = (Right (b^._z .*. z0, zr), GE (b^._x) (b^._y))
  acc (Right (globalZ, z0)) (zr, b) = (Right (globalZ, z0 .*. zr), GE (b^._x .*. z0 .^. 2) (b^._y .*. z0 .^. 3))

g :: GEJ
g = GEJ (unrepr 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
        (unrepr 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
        feOne

g128 :: GEJ
g128 = iterate double g !! 128

wg = 15

tableG = table wg g

tableG128 = table wg g128

table w p = t & traverse %~ norm
 where
  (t,z) = scalarTable w p
  zinv = inv z
  norm (GE x y) = GE (x .*. zinv .^. 2) (y .*. zinv .^. 3)

(!) :: V.Vector GE -> Int -> GE
t ! i | i >= 0 = t V.! i
      | otherwise = pointNegate (t V.! (-i-1))

pkPoint :: XOnlyPubKey -> Maybe GEJ
pkPoint (XOnlyPubKey px) = do
  x <- feUnpack px
  y <- sqrt (x .^. 3 .+. feSeven)
  return (GEJ x y feOne)

sigUnpack :: Sig -> Maybe (FE, Scalar)
sigUnpack (Sig r s) = (,) <$> feUnpack r <*> scalarUnpack s

schnorr :: XOnlyPubKey  -- ^ public key
        -> Hash256      -- ^ message
        -> Sig          -- ^ signature
        -> Bool
schnorr pk m sg = Just () == do
  p <- pkPoint pk
  (rx, s) <- sigUnpack sg
  let tag = bsHash (BSC.pack "BIPSchnorr")
  let h = bsHash . runPut $ put tag >> put tag >> put (fePack rx) >> put pk >> put m
  let nege = scalarNegate . scalarUnrepr . integerHash256 $ h
  let r = ecMult p nege s
  guard $ hasQuadY r
  guard $ eqXCoord rx r
