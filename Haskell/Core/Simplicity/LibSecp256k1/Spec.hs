module Simplicity.LibSecp256k1.Spec
 ( FE, unrepr, feZero, feOne
 , GEJ(..), _gej, gej, _x, _y, _z
 , GE(..)
 , Scalar, scalarUnrepr, scalarZero
 , fePack, scalarPack
 , feIsZero, neg, add, mul, sqr, inv, sqrt, (.+.), (.-.), (.*.), (.^.)
 , double, offsetPointEx, offsetPointZinv
 , eqXCoord, hasQuadY
 , scalarNegate
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

-- :TODO: export this.
normalize :: FE -> FE
normalize = unrepr . repr

feUnpack :: Word256 -> Maybe FE
feUnpack x0 = guard (x == repr a) >> return a
 where
  x = toInteger x0
  a = unrepr x

feIsZero :: FE -> Bool
feIsZero a = 0 == repr (normalize a)

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
  mempty = GEJ feOne feOne feZero
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

pointNegate :: GE -> GE
pointNegate (GE x y) = GE x (neg y)

scalarModulus :: Word256
scalarModulus = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

newtype Scalar = Scalar { scalarPack :: Word256 } deriving (Eq, Show)

instance Bounded Scalar where
  minBound = Scalar 0
  maxBound = Scalar $ scalarModulus - 1

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

ecMult :: GEJ -> Scalar -> Scalar -> GEJ
ecMult a na0 ng = foldr f mempty (zipEx wnafa (wnaf wg ng)) & _z %~ (.*. globalZ)
 where
  na = if isInf a then scalarZero else na0
  wa = 5
  wnafa = wnaf wa na
  (tableA, globalZ) | null wnafa = (V.empty, feOne)
                    | otherwise = scalarTable wa a
  f (Nothing, Nothing) r0 = double r0
  f (Just x, Nothing) r0 | x >= 0 = snd $ f (Nothing, Nothing) r0 `offsetPointEx` (tableA V.! x)
                         | otherwise = snd $ f (Nothing, Nothing) r0 `offsetPointEx` pointNegate (tableA V.! (-x-1))
  f (x, Just y) r0 | y >= 0 = offsetPointZinv (f (x, Nothing) r0) (tableG V.! y) globalZ
                   | otherwise = offsetPointZinv (f (x, Nothing) r0) (pointNegate (tableG V.! (-y-1))) globalZ
  zipEx [] [] = []
  zipEx [] bs = map (\b -> (Nothing,b)) bs
  zipEx as [] = map (\a -> (a,Nothing)) as
  zipEx (a:as) (b:bs) = (a,b) : zipEx as bs

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

wnaf :: Int -> Scalar -> [Maybe Int]
wnaf w s = post <$> wnafInteger w i
 where
  -- covert 's' to an integer i such that '2^255 - scalarModulus <= i < 2^255' and i is equivalent to s modulo the scalar Modulus.
  i = ((toInteger (scalarPack s) - 2^255) `mod` toInteger scalarModulus) + 2^255 - toInteger scalarModulus
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

wg = 16
tableG = t & traverse %~ norm
 where
  (t,z) = scalarTable wg g
  zinv = inv z
  norm (GE x y) = GE (x .*. zinv .^. 2) (y .*. zinv .^. 3)

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
