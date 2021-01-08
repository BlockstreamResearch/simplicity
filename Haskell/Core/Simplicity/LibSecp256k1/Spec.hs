module Simplicity.LibSecp256k1.Spec
 ( -- * Field operations.
   FE, fe, fe_repr, fe_pack
 , fe_zero, fe_one
 , fe_is_zero, fe_is_odd
 , fe_negate, fe_add, fe_multiply, fe_square, fe_invert, fe_square_root
 , (.+.), (.-.), (.*.), (.^.)
   -- * Group operations.
 , GEJ(..), _gej, gej, _x, _y, _z, g
 , gej_double, gej_add_ex
 , gej_x_equiv, gej_y_is_odd
 , GE(..)
 , gej_normalize
 , gej_ge_add_ex, gej_ge_add_zinv
 , ge_negate, ge_scale_lambda
   -- * Scalar operations
 , Scalar, scalar, scalar_repr, scalar_pack
 , scalar_zero, scalar_negate, scalar_multiply, scalar_split_lambda, scalar_split_128
 , wnaf, linear_combination_1
   -- * Public key / Signature operations
 , PubKey(..), pubkey_unpack, pubkey_unpack_neg, pubkey_unpack_quad
 , Sig(..), signature_unpack
 , bip0340_check
 -- * Some large integer constants for secp256k1.
 , fieldOrder, groupOrder, beta, lambda
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

-- | The secp256k1 field is @GF[p]@ where p is this prime number.
fieldOrder :: Integer
fieldOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

-- | The secp256k1 group has order @n@ where @n@ is this prime number.
groupOrder :: Integer
groupOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

-- | The canonical primitive cube root of 1 in @GF[p]@.
--
-- @
--    mod (beta ^ 2 + beta + 1) fieldOrder == 0
-- @
--
-- Note that @mod (beta ^ 2) fieldOrder@ is the other, non-canonical, cube root of 1.
beta :: Integer
beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

-- | The canonical primitive cube root of 1 in the scalar field @GF[n]@.
--
-- @
--    mod (lambda ^ 2 + lambda + 1) groupOrder == 0
-- @
--
-- and
--
-- @
--    'gej_normalize' ('scalar_mulitply' ('scalar' 'lambda') p) == 'GE' ('fe' 'beta' .*. x) y
--      where (x, y) = 'gej_normalize' p
-- @
--
-- Note that @mod (lambda ^ 2) groupOrder@ is the other, non-canonical, cube root of 1.
lambda :: Integer
lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

-- | An element of secp256k1's field is represented as a normalized value.
data FE = FE { fe_pack :: Word256 -- ^ Return the normalized represenative of a field element as a 'Word256'.
             }
  deriving (Eq, Show)

-- | Return the normalized integer representative of a field element.
fe_repr :: FE -> Integer
fe_repr = toInteger . fe_pack

-- | Construct a field element from an integer.
fe :: Integer -> FE
fe n = FE . fromInteger $ n `mod` fieldOrder

-- | The zero value of the field.
fe_zero :: FE
fe_zero = fe 0

-- | The one value of the field.
fe_one :: FE
fe_one = fe 1

-- | @'fe' 7@
fe_seven :: FE
fe_seven = fe 7

-- | @'fe' 'beta'@
fe_beta :: FE
fe_beta = fe beta

-- | Decode a 256-bit word value as a field element, failing if the value is non-canonical.
fe_unpack :: Word256 -> Maybe FE
fe_unpack x0 = guard (x == fe_repr a) >> return a
 where
  x = toInteger x0
  a = fe x

-- | Checks if the field element's represenative is odd.
fe_is_odd :: FE -> Bool
fe_is_odd = odd . fe_repr

-- | Checks if the field element is 0.
fe_is_zero :: FE -> Bool
fe_is_zero = (0 ==) . fe_repr

-- | Negate a field element.
fe_negate :: FE -> FE
fe_negate = fe . negate . fe_repr

-- | Add two field elements.
fe_add :: FE -> FE -> FE
fe_add a b = fe (fe_repr a + fe_repr b)

-- | Multiply two field elements.
fe_multiply :: FE -> FE -> FE
fe_multiply a b = fe (fe_repr a * fe_repr b)

-- | Square a field elements.
fe_square :: FE -> FE
fe_square a = fe_multiply a a

-- | Multiply a field element by an integer.
--
-- @
--    mulInt i a == fe i .*. a
-- @
mulInt :: Integer -> FE -> FE
mulInt i a = fe_multiply (fe i) a

-- | Add two field elements.
(.+.) = fe_add

-- | Multiply two field elements.
(.*.) = fe_multiply

-- | Difference of two field elements.
x .-. y = fe_add x (fe_negate y)

-- | A field element raised to a given power.
x .^. n = go x (n `mod` (fieldOrder - 1))
 where
  go x 0 = fe_zero
  go x 1 = x
  go x n | even n = go (fe_square x) (n `div` 2)
         | odd n = fe_multiply x (go (fe_square x) (n `div` 2))

-- | The modulular inverse of a field element, with 'fe_zero' mapping to 'fe_zero'.
fe_invert :: FE -> FE
fe_invert a = a .^. (fieldOrder - 2)

-- | A modular square root of a field element if it exists.
-- If it exists it returns a value that is itself a square.
fe_square_root :: FE -> Maybe FE
fe_square_root a | 0 == (fieldOrder + 1) `mod` 4 = do
  let res = a .^. ((fieldOrder + 1) `div` 4)
  guard $ fe_is_zero (fe_square res .-. a)
  return res

-- | Checks if a field element has a square root.
isQuad :: FE -> Bool
isQuad = isJust . fe_square_root

-- | A point in Jacobian coordinates.
-- A '_z' component of 'fe_zero' represents a point at infinity.
--
-- A value @p :: 'GEJ'@ where @p^.'_z'@ is not 'fe_zero' represents a point with x-coordinate @p.^'_x' .*. ('fe_invert' p.^_z) .^. 2@
-- and with y-coordinate @p.^'_y' .*. ('fe_invert' p.^_z) .^. 3@.
--
-- A canonical point has a z-component of 1, except for the point at infinity whose canonical value has all components 0.
data GEJ = GEJ !FE !FE !FE
  deriving Show

-- | A traversal of the 3 'GEJ' components.
_gej :: Applicative f => (FE -> f FE) -> GEJ -> f GEJ
_gej = under gej

-- | A grid of the 3 'GEJ' components.
gej :: (Functor g, Applicative f) => (g FE -> f FE) -> g GEJ -> f GEJ
gej f a = GEJ <$> f ((^._x) <$> a)
              <*> f ((^._y) <$> a)
              <*> f ((^._z) <$> a)

-- | A lens for the x-component of 'GEJ'.
_x :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_x f (GEJ x y z) = (\x -> GEJ x y z) <$> f x

-- | A lens for the y-component of 'GEJ'.
_y :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_y f (GEJ x y z) = (\y -> GEJ x y z) <$> f y

-- | A lens for the z-component of 'GEJ'.
_z :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_z f (GEJ x y z) = (\z -> GEJ x y z) <$> f z

-- | Checks if the point is a representation of infinity.
isInf :: GEJ -> Bool
isInf a = fe_is_zero (a^._z)

-- | Compute the point doubling formula for a 'GEJ'.
gej_double :: GEJ -> GEJ
gej_double a@(GEJ x y z) | isInf a = mempty
                         | otherwise = GEJ x' y' z'
 where
  x' = mulInt 9 (x .^. 4) .+. mulInt (-8) (x .*. y .^. 2)
  y' = mulInt 36 (x .^. 3 .*. y .^. 2) .+. mulInt (-27) (x .^. 6) .+. mulInt (-8) (y .^. 4)
  z' = mulInt 2 (y .*. z)

-- | Compute the point addition formula for a 'GEJ'.
-- This also returns the ratio between z-component of 'a' and z-component of the result.
--
-- @
--    a^.'_z' .*. r = p^.'_z'
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
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

-- | Check if the x-coordinate of the point represented by a 'GEJ' has a given value.
gej_x_equiv :: GEJ -> FE -> Bool
-- :TODO: Perhaps should return false for the point at infinity.
gej_x_equiv a x = fe_is_zero $ (fe_square (a^._z) .*. x) .-. (a^._x)

-- | Check if the y-coordinate of the point represented by a 'GEJ' is odd.
gej_y_is_odd :: GEJ -> Bool
gej_y_is_odd a@(GEJ _ y z) | isInf a = False
                           | otherwise = fe_is_odd $ y .*. invz .^. 3
 where
  invz = fe_invert z

-- | A point.  Infinity not included
data GE = GE !FE !FE -- Infinity not included.
        deriving Show

-- | Compute the point addition formula for a 'GEJ' and a 'GE'.
-- This also returns the ratio between z-component of 'a' and z-component of the result.
--
-- @
--    a^.'_z' .*. r = p^.'_z'
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
gej_ge_add_ex :: GEJ -> GE -> (FE, GEJ)
gej_ge_add_ex a (GE bx by) = gej_add_ex a (GEJ bx by fe_one)

-- | Compute a point addition formula for a 'GEJ' and another point with an inverted z coordinate.
--
-- @
--    'gej_is_inf' $ ('gej_ge_add_zinv' a (GE bx by) bzinv) <> ('gej_negate' (a <> ('GEJ' bx by ('fe_invert' bzinf))))
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
gej_ge_add_zinv :: GEJ -> GE -> FE -> GEJ
gej_ge_add_zinv a (GE bx by) bzinv = snd $ gej_ge_add_ex a (GE (bx .*. bzinv .^. 2) (by .*. bzinv .^. 3))

-- | Convert a 'GEJ' to a 'GE'.
-- This sends a point at infinity the the point @(GE fe_zero fe_zero)@.
gej_normalize :: GEJ -> GE
gej_normalize (GEJ x y z) = GE (x .*. invz .^. 2) (y .*. invz .^. 3)
 where
  invz = fe_invert z

-- | Negates a 'GE'.
ge_negate :: GE -> GE
ge_negate (GE x y) = GE x (fe_negate y)

-- | Scale a 'GE' by 'lambda'.
--
-- @
--    'ge_scale_lambda' ('ge_normalze' p) == 'ge_normalize' ('scalar_multiply' 'scalar_lambda' p)
-- @
ge_scale_lambda :: GE -> GE
ge_scale_lambda (GE x y) = GE (x .*. fe_beta) y

-- | An element of secp256k1's scalar field is represented as a normalized value.
newtype Scalar = Scalar { scalar_pack :: Word256 -- ^ Return the normalized represenative of a scalar element as a 'Word256'.
                        } deriving (Eq, Show)

instance Bounded Scalar where
  minBound = scalar 0
  maxBound = scalar $ groupOrder - 1

-- | The zero value of the scalar field.
scalar_zero :: Scalar
scalar_zero = Scalar 0

-- | @'scalar' 'lambda'@
scalar_lambda :: Scalar
scalar_lambda = scalar lambda

-- | Construct a scalar element from an integer.
scalar :: Integer -> Scalar
scalar x = Scalar $ fromInteger (x `mod` groupOrder)

-- | Return the normalized integer representative of a scalar element.
scalar_repr :: Scalar -> Integer
scalar_repr = toInteger . scalar_pack

-- | Decode a 256-bit word value as a scalar element, failing if the value is non-canonical.
scalar_unpack :: Word256 -> Maybe Scalar
scalar_unpack x0 = guard (x == scalar_repr s) >> return s
 where
  x = toInteger x0
  s = scalar x

-- | Checks if the scalar element is 0.
scalar_is_zero :: Scalar -> Bool
scalar_is_zero a = scalar_repr a == 0

-- | Negate a scalar element.
scalar_negate :: Scalar -> Scalar
scalar_negate = scalar . negate . scalar_repr

-- | Scale a 'GEJ' by a scalar element.
scalar_multiply :: Scalar -> GEJ -> GEJ
scalar_multiply na a = linear_combination_1 na a scalar_zero

-- | Decompose a scalar value in short components.
--
-- @
--    'scalar' (k1 + 'lambda' * k2) == a
--    abs k1 < 2^128 && abs k2 < 2^128
-- @
--
-- where
--
-- @
--    (k1, k2) = 'scalar_split_lambda' a
-- @
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

-- | Decompose a scalar value in short components.
--
-- @
--    'scalar' (k1 + 2^128 * k2) == a
--    0 <= k1 < 2^128 && 0 <= k2 < 2^128
-- @
--
-- where
--
-- @
--    (k1, k2) = 'scalar_split_128' a
-- @
scalar_split_128 :: Scalar -> (Integer, Integer)
scalar_split_128 k0 = (k1, k2)
 where
  k = scalar_repr k0
  (k2, k1) = k `divMod` (2^128)

-- | Fast computation of a linear combination of the secp256k1 curve generator and another point.
--
-- @
--    'gej_is_inf' $ 'linear_combination_1' na a ng <> ('scalar_multiply' ('scalar_negate' na) a) <> ('scalar_multiply' ('scalar_negate' ng) 'g')
-- @
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

-- | Decompose an integer in windowed non-adjacent form
wnafInteger :: Int -> Integer -> [Int]
wnafInteger w | 0 < w && w <= finiteBitSize w = unfoldr f
 where
  f 0 = Nothing
  f i = Just (fromInteger x, (i - x) `div` 2)
   where
    x | odd i = ((i + 2^(w-1)) `mod` 2^w) - 2^(w-1)
      | otherwise = 0

-- | Decompose an integer in windowed non-adjacent form.
-- Odd values have their least significant bit dropped.
-- Zero values are returned as Nothing.
wnaf :: Int -> Integer -> [Maybe Int]
wnaf w s = post <$> wnafInteger w s
 where
  post 0 = Nothing
  post i | odd i = Just $ i `div` 2
         | otherwise = error "Simplicity.LibSecp256k1.Spec: invalid result from wnafInteger"

-- | Precompute small odd muliplies of a 'GEJ' and give them a common z-coordinate.
-- The point must not be at infinity.
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

-- | The specified generator of the secp256k1 curve.
g :: GEJ
g = GEJ (fe 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
        (fe 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
        fe_one

-- | A representation of 2^128 * 'g'.
g128 :: GEJ
g128 = iterate gej_double g !! 128

-- | The default window size for scalars multiplying by 'g'.
wg = 15

-- | A precomputate table of odd multiples of 'g'.
tableG = table wg g

-- | A precomputate table of odd multiples of 'g128'.
tableG128 = table wg g128

-- | Compute a table of odd multiple of a point and 'gej_normalize' all of them.
table w p = t & traverse %~ norm
 where
  (t,z) = scalarTable w p
  zinv = fe_invert z
  norm (GE x y) = GE (x .*. zinv .^. 2) (y .*. zinv .^. 3)

-- | An index into a precomputed odd multiple table of 'GE'.
-- Negative indexes are accepted and automatically return the negation of the corresponding point.
(!) :: V.Vector GE -> Int -> GE
t ! i | i >= 0 = t V.! i
      | otherwise = ge_negate (t V.! (-i-1))

-- | Given an (x-only) public key, returns a GEJ with that x-coordinate whose y-coordinate is a square, if such a point exists.
pubkey_unpack_quad :: PubKey -> Maybe GEJ
pubkey_unpack_quad (PubKey px) = do
  x <- fe_unpack px
  y <- fe_square_root (x .^. 3 .+. fe_seven)
  return (GEJ x y fe_one)

-- | Given an (x-only) public key, returns a GEJ with that x-coordinate whose y-coordinate is even, if such a point exists.
pubkey_unpack :: PubKey -> Maybe GEJ
pubkey_unpack = (some_ . _y %~ mkEven) . pubkey_unpack_quad
 where
  mkEven y | fe_is_odd y = fe_negate y
           | otherwise = y

-- | Given an (x-only) public key, returns a GEJ with that x-coordinate whose y-coordinate is odd, if such a point exists.
pubkey_unpack_neg :: PubKey -> Maybe GEJ
pubkey_unpack_neg = (some_ . _y %~ mkOdd) . pubkey_unpack_quad
 where
  mkOdd y | fe_is_odd y = y
          | otherwise = fe_negate y

-- | Given a bip0340 signature, unpack it r value as an 'FE', and its s value as a 'Scalar'.
-- Fails if the signature components are out of range.
signature_unpack :: Sig -> Maybe (FE, Scalar)
signature_unpack (Sig r s) = (,) <$> fe_unpack r <*> scalar_unpack s

-- | Verify a bip0340 signature for a given public key on a given message.
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
