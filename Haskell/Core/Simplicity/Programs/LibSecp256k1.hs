{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines a library of Simplicity expressions that replicate the functional behaviour of (a specific version of) libsecp256k1's elliptic curve operations <https://github.com/bitcoin-core/secp256k1/tree/1e6f1f5ad5e7f1e3ef79313ec02023902bf8175c>.
-- The functions defined here return precisely the same field and point representatives that the corresponding libsecp256k1's functions do, with a few exceptions with the way the point at infinity is handled.
-- This makes these expressions suitable for being jetted by using libsecp256k1 functions.
module Simplicity.Programs.LibSecp256k1
  (
    Lib(Lib), mkLib
  -- * Field operations
  , FE, feZero, feOne, feIsZero
  , normalize
  , add, neg, sqr, mul, inv, sqrt
  , isQuad
  -- * Point operations
  , GE, GEJ, inf, isInf
  , normalizePoint
  , geNegate, double, offsetPointEx, offsetPoint
  , eqXCoord, hasQuadY
  -- * Elliptic curve multiplication related operations
  , Scalar
  , normalizeScalar
  , wnaf5, wnaf16
  , ecMult
  -- * Schnorr signature operations
  , XOnlyPubKey, pkPoint
  , Sig, sigUnpack
  , scalarUnrepr
  , schnorrVerify, schnorrAssert
  -- * Example instances
  , lib
  ) where

import Prelude hiding (drop, take, and, or, not, sqrt, Word)

import Simplicity.Functor
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)
import Simplicity.Ty
import Simplicity.Term.Core

-- The number of elements in secp256k1's field.
feOrder :: Integer
feOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

-- The number of points on secp256k1's elliptic curve.
scalarOrder :: Integer
scalarOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- | Simplicity's representation of 'fe' (field) elements in libsecp256k1's 10x26-bit form.
type FE = Word256

-- | A point in affine coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity isn't representable.
type GE = (FE, FE)

-- | A point in Jacobian coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity's representatives are of the form @((a^2, a^3), 0)@, with @((1, 1), 0)@ being the canonical representative.
type GEJ = (GE, FE)

-- | Scalar values, those less than the order of secp256's elliptic curve, are represented by a 256-bit word type.
type Scalar = Word256

-- | A format for (Schnorr) elliptic curve x-only public keys.
-- The y-coordinate is implicity the one on the curve that is positive (i.e it is a quadratic residue).
-- The point at infinity isn't representable (nor is it a valid public key to begin with).
type XOnlyPubKey = Word256

-- | A format for Schnorr signatures.
type Sig = (Word256, Word256)

-- | A collection of core Simplicity expressions for LibSecp256k1.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Reduce the representation of a field element to its canonical represenative.
    --
    -- Corresponds to @secp256k1_fe_normalize_var@ (and @secp256k1_fe_normalize@).
    normalize :: term Word256 FE

    -- | The normalized reprsentative for the field element 0.
  , feZero :: term () FE

    -- | The normalized reprsentative for the field element 1.
  , feOne :: term () FE

    -- | Tests if the input value is a representative of the field element 0.
    -- Some preconditions apply.
    --
    -- Corresponds to @secp256k1_fe_is_zero@.
  , feIsZero :: term FE Bit

    -- | Adds two field elements.
    -- The resulting magnitude is the sum of the input magnitudes.
    --
    -- Corresponds to @secp256k1_fe_add@.
  , add :: term (FE, FE) FE

    -- | Negates a field element.
    -- The resulting magnitude is one more than the input magnitude.
    --
    -- Corresponds to @secp256k1_fe_negate@.
  , neg :: term FE FE

    -- | Multiplies two field elements.
    -- The input magnitudes must be at most 8 (okay maybe up to 10).
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    --
    -- Corresponds to @secp256k1_fe_mul@.
  , mul :: term (FE, FE) FE

    -- | Squares a field element.
    -- The input magnitude must be at most 8.
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    --
    -- Corresponds to @secp256k1_fe_sqr@.
  , sqr :: term FE FE

    -- | Computes the modular inverse of a field element.
    -- The input magnitude must be at most 8.
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    -- Returns a represenative of 0 when given 0.
    --
    -- Corresponds to @secp256k1_fe_inv@.
  , inv :: term FE FE

    -- | Computes the modular square root of a field element if it exists.
    -- The input magnitude must be at most 8.
    -- If the result exists, magnitude is 1 (which isn't necessarily normalized) and it is a quadratic residue
    --
    -- Corresponds to @secp256k1_fe_sqrt@.
    -- If @secp256k1_fe_sqrt@ would return 0, then @'Left' ()@ is returned by 'sqrt'.
    -- If @secp256k1_fe_sqrt@ would return 1, then @'Right' r@ is returned by 'sqrt' where @r@ is the result from @secp256k1_fe_sqrt@.
  , sqrt :: term FE (Either () FE)

    -- | Tests if the field element is a quadratic residue.
    --
    -- Corresponds to @secp256k1_fe_is_quad_var@.
  , isQuad :: term FE Bit

    -- | Returns the canonical represenative of the point at infinity.
  , inf :: term () GEJ

    -- | Given a point on curve, or a represenativie of infinity, tests if the point is a representative of infinity.
  , isInf :: term GEJ Bit

    -- | Adds a point with itself.
    --
    -- Corresponds to @secp256k1_gej_double_var@.
    -- However if the input is infinity, it returns infinity in canonical form.
  , double :: term GEJ GEJ

    -- | Adds a point in Jacobian coordinates with a point in affine coordinates.
    -- Returns the result in Jacobian coordinates and the ratio of z-coordinates between the output and the input that is in Jacobain coordinates.
    -- If the input point in Jacobian coordinates is the point at infinity, the ratio returned is set to 0.
    --
    -- Corresponds to @secp256k1_gej_add_ge_var@ with a non-null @rzr@.
    -- If the result is the point at infinity, it is returned in canonical form.
  , offsetPointEx :: term (GEJ, GE) (FE, GEJ)

    -- | Adds a point in Jacobian coordinates with a point in affine coordinates.
    -- Returns the result in Jacobian coordinates.
    --
    -- If the result is the point at infinity, it is returned in canonical form.
  , offsetPoint :: term (GEJ, GE) GEJ

    -- | Negates a point in affine coordinates.
    --
    -- Corresponds to @secp256k1_ge_neg@.
  , geNegate :: term GE GE

    -- | Converts a point in Jacobian coordintes to the same point in affine coordinates, and normalizes the field represenatives.
    -- Returns the point (0, 0) when given the point at infinity.
  , normalizePoint :: term GEJ GE

    -- | Given a field element and a point in Jacobian coordiantes, test if the point represents one whose affine x-coordinate is equal to the given field element.
    --
    -- Corresponds to @secp256k1_gej_eq_x_var@.
  , eqXCoord :: term (FE, GEJ) Bit

    -- | Given a point in Jacobian coordiantes, test if the point represents one whose affine y-coordinate is a quadratic residue.
    --
    -- Corresponds to @secp256k1_gej_has_quad_y_var@.
  , hasQuadY :: term GEJ Bit

  , normalizeScalar :: term Word256 Scalar

  , scalarIsZero :: term Scalar Bit

    -- | Convert a scalar value to wnaf form, with a window of 5 bits.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult_wnaf@ with @w@ parameter set to 5.
  , wnaf5 :: term Scalar (Vector256 (Either () Word4))

    -- | Convert a scalar value to wnaf form, with a window of 16 bits.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult_wnaf@ with @w@ parameter set to 16.
  , wnaf16 :: term Scalar (Vector256 (Either () Word16))

    -- | Returns an integer multiple of the secp256k1's generator.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
  , generator :: term Scalar GEJ

    -- | Given an elliptic curve point, @a@, and two scalar values @na@ and @ng@, return @na * a + ng * g@ where @g@ is secp256k1's generator.
    -- The scalar inputs must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult@.
    -- If the result is the point at infinity, it is returned in canonical form.
  , ecMult :: term ((GEJ, Scalar), Scalar) GEJ

    -- | This function unpacks a 'XOnlyPubKey' as a elliptic curve point in Jacobian coordinates.
    --
    -- If the x-coordinate isn't on the elliptice curve, the funtion returns @Left ()@.
    -- If the x-coordinate is greater than or equal the field order, the function returns @Left ()@.
  , pkPoint :: term XOnlyPubKey (Either () GEJ)

    -- | This function unpackes a 'Sig' as a pair of a field element and a scalar value.
    --
    -- If the field element's value is greater than or equal to the field order, the function return @Left ()@.
    -- If the scalar element's value is greater than or equal to secp256k1's curve order, the function returns @Left ()@.
  , sigUnpack :: term Sig (Either () (FE, Scalar))

    -- | This function reduces a 256-bit unsigned integer module the order of the secp256k1 curve, yielding a scalar value.
  , scalarUnrepr :: term Word256 Scalar

    -- | This function is given a public key, a 256-bit message, and a signature, and checks if the signature is valid for the given message and public key.
  , schnorrVerify :: term ((XOnlyPubKey, Word256), Sig) Bit
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { normalize = m normalize
    , feZero = m feZero
    , feOne = m feOne
    , feIsZero = m feIsZero
    , add = m add
    , neg = m neg
    , mul = m mul
    , sqr = m sqr
    , inv = m inv
    , sqrt = m sqrt
    , isQuad = m isQuad
    , inf = m inf
    , isInf = m isInf
    , double = m double
    , offsetPointEx = m offsetPointEx
    , offsetPoint = m offsetPoint
    , geNegate = m geNegate
    , normalizePoint = m normalizePoint
    , eqXCoord = m eqXCoord
    , hasQuadY = m hasQuadY
    , normalizeScalar = m normalizeScalar
    , scalarIsZero = m scalarIsZero
    , wnaf5 = m wnaf5
    , wnaf16 = m wnaf16
    , generator = m generator
    , ecMult = m ecMult
    , pkPoint = m pkPoint
    , sigUnpack = m sigUnpack
    , scalarUnrepr = m scalarUnrepr
    , schnorrVerify = m schnorrVerify
    }

-- | Build the LibSecp256k1 'Lib' library from its dependencies.
mkLib :: forall term. Core term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  -- A constant expression for a 64-bit value.
  scribe64 :: TyC a => Integer -> term a Word64
  scribe64 = scribe . toWord64

  -- A constant expression for a 128-bit value.
  scribe128 :: TyC a => Integer -> term a Word128
  scribe128 = scribe . toWord128

  -- A constant expression for a 256-bit value.
  scribe256 :: TyC a => Integer -> term a Word256
  scribe256 = scribe . toWord256

  scribeFeOrder :: term () Word256
  scribeFeOrder = scribe256 feOrder

  scribeScalarOrder :: term () Word256
  scribeScalarOrder = scribe256 scalarOrder

  -- Multiplication modulo 2^64.
  mul64 :: term (Word64, Word64) Word128
  mul64 = multiplier word64

  -- 256 bit addition.
  add256 :: term (Word256, Word256) (Bit, Word256)
  add256 = adder word256

  -- 256 bit subtraction.
  sub256 :: term (Word256, Word256) (Bit, Word256)
  sub256 = subtractor word256

  -- | adds 2^256 to a 128 bit value modulo the field order.  This is guarenteed to be normalized.
  add2256modp :: TyC a => term a Word128 -> term a FE
  add2256modp k = (unit >>> (zero word64 &&& scribe64 (2^256 - feOrder))) &&& k >>> adder word128
              >>> cond (scribe128 1 &&& iden) (zero word128 &&& iden)

  -- | adds a 256-bit and a 128-bit value modulo the field order.
  add256_128modp :: term (Word256, Word128) FE
  add256_128modp = oh &&& (zero word128 &&& ih) >>> add256
               >>> cond (add2256modp ih) iden
               >>> normalize

  -- | multiplies 2^256 by a 64 bit value modulo the field order.
  mul2256_64modp :: TyC a => term a Word64 -> term a Word128
  mul2256_64modp k = (unit >>> scribe64 (2^256 - feOrder)) &&& k >>> mul64

  -- | computes a 512 bit number modulo the field order.
  normalize512 :: term Word512 FE
  normalize512 = (((unit >>> (zero word128 &&& (zero word64 &&& scribe64 (2^256 - feOrder)))) &&& oh) &&& (zero word256 &&& ih))
             >>> fullMultiplier word256
             >>> ih &&& mul2256_64modp oiih
             >>> add256_128modp

  signResize4 = signedResize word4 word256
  signResize16 = signedResize word16 word256

  wnaf5step1 :: term Word256 (Word256, (Either () Word4))
  wnaf5step1 = signedResize word256 word1 &&& signedShift word256 1
           >>> cond body (iden &&& injl unit)
   where
    body = iden &&& (drop . drop . drop $ iiih) >>> (oh &&& drop signResize4 >>> sub256 >>> ih) &&& drop (injr iden)

  wnaf16step1 :: term Word256 (Word256, (Either () Word16))
  wnaf16step1 = signedResize word256 word1 &&& iden
           >>> cond body (signedShift word256 1 &&& injl unit)
   where
    body = signedShift word256 1 &&& drop iiih >>> (oh &&& drop (signResize16 >>> signedShift word256 1) >>> sub256 >>> ih) &&& drop (injr iden)

  wnafstepD :: TyC v => term Word256 (Word256, v) -> term Word256 (Word256, (v, v))
  wnafstepD rec = rec >>> take rec &&& ih >>> ooh &&& (ih &&& oih)

  wnaf5step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf5step1
  wnaf5step256 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf5step16
  wnaf16step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf16step1
  wnaf16step256 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf16step16

  wnaf5Short :: term Word16 (Vector16 (Either () Word4))
  wnaf5Short = signResize16 >>> wnaf5step16 >>> ih

  wnafpre :: term Scalar Word256
  wnafpre = (take . take . take . take . take $ oooh) &&& iden
        >>> cond (iden &&& (unit >>> scribeScalarOrder) >>> sub256 >>> ih) iden

  generator0 :: term () GE
  generator0 = scribe g
   where
     g = (toWord256 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, toWord256 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

  generator1 :: Word a -> term (a, GEJ) GEJ
  generator1 SingleV = cond (double &&& (unit >>> generator0) >>> offsetPoint) double
  generator1 (DoubleV w) = oih &&& (ooh &&& ih >>> rec) >>> rec
   where
    rec = generator1 w

  lib@Lib{..} = Lib {
    normalize = (iden &&& (unit >>> scribeFeOrder) >>> sub256) &&& iden
            >>> ooh &&& (oih &&& ih)
            >>> cond ih oh

  , feZero = zero word256

  , feOne = scribe256 1

  , feIsZero = or ((unit >>> feZero) &&& iden >>> eq)
                  ((unit >>> scribeFeOrder) &&& iden >>> eq)

  , add = add256
      >>> cond ((iden &&& (zero word64 &&& scribe64 (2^256 - feOrder))) >>> add256_128modp) normalize

  , neg = mulInt (-1)

  , mul = multiplier word256 >>> normalize512

  , sqr = iden &&& iden >>> mul

  , inv = iden &&& tower
      >>> oh &&& (ioh &&& (oh &&& iih >>> mul >>> sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr) >>> mul

  , sqrt = iden &&& tower
       >>> oh &&& drop ((oh &&& drop sqr >>> mul) >>> sqr >>> sqr)
       >>> (take neg &&& drop sqr >>> add >>> feIsZero) &&& ih
       >>> cond (injr iden) (injl unit)

  , isQuad = elimS sqrt false true

  , inf =
     let
      one = feOne
     in
      (one &&& one) &&& feZero

  , isInf = drop feIsZero

  , double =
     let
      body = (take (oh &&& (take sqr >>> mulInt (-3)) &&& (drop sqr >>> mulInt 2))                                                                               -- (x, (-3*x^2, 2*y^2))
          >>> (((drop (take sqr)) &&& (iih &&& oh >>> mul)) &&& drop (oh &&& (drop sqr >>> mulInt (-2))))                                                        -- ((9*x^4, 2*x*y^2), (-3*x^2, -8*y^4))
          >>> take (oh &&& (drop (mulInt (-4))) >>> add) &&& (iih &&& (ioh &&& take (oh &&& drop (mulInt (-6)) >>> add) >>> mul) >>> add))                       -- (9*x^4 - 8*x*y^2, 36*x^3*y^2 - 27*x^6 - 8*y^4)
         &&& (oih &&& ih >>> mul >>> mulInt 2)                                                                                                                   -- 2*y*z
     in
      isInf &&& iden >>> cond (unit >>> inf) body

  , offsetPointEx =
     let
      body = ((take (take (take neg))) &&& (ioh &&& (oih >>> sqr) >>> mul) >>> add)
         &&& ((take (take (drop neg))) &&& (iih &&& (oih >>> cub) >>> mul) >>> add) &&& oh                                                                       -- (h,(i,a))
         >>> take feIsZero &&& iden >>> cond (drop zeroH) nonZeroH
      zeroH = take feIsZero &&& ih >>> cond (take (drop (mulInt 2)) &&& double) (unit >>> feZero &&& inf)
      nonZeroH = (oh &&& (oh &&& iiih >>> mul)) &&& ((take sqr &&& drop iooh >>> mul) &&& drop (oh &&& ioih))                                                    -- ((h,z),(t,(i,s1)))
             >>> oh &&& (((take (take neg) >>> cub) &&& ioh) &&& iih)                                                                                            -- ((h,z),((-h^3,t),(i,s1)))
             >>> ooh &&& drop ((((take (oh &&& drop (mulInt (-2)) >>> add) &&& drop (take sqr) >>> add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> mul)))            -- (h,(((x,t),(i,(-h^3*s1))),z))
                          >>> ooh &&& (iih &&& (ioh &&& (oih &&& take (take neg) >>> add) >>> mul) >>> add))                                                     -- ..,(x,y),...
                     &&& oih
     in
      take isInf &&& iden >>> cond ((unit >>> feZero) &&& (drop ((take normalize &&& drop normalize) &&& (unit >>> feOne)))) body

  , offsetPoint = offsetPointEx >>> ih

  , geNegate = take normalize &&& drop neg

  , normalizePoint = oh &&& (ih >>> inv)
                 >>> (ooh &&& drop sqr >>> mul) &&& (oih &&& drop cub >>> mul)

  , eqXCoord = drop (take (take neg)) &&& (drop (drop sqr) &&& oh >>> mul)
           >>> add >>> feIsZero

  , hasQuadY = and (not isInf) (oih &&& ih >>> mul >>> isQuad)

  , normalizeScalar = (iden &&& (unit >>> scribeScalarOrder) >>> sub256) &&& iden
                  >>> ooh &&& (oih &&& ih)
                  >>> cond ih oh

  , scalarIsZero = or ((unit >>> zero word256) &&& iden >>> eq)
                  ((unit >>> scribeScalarOrder) &&& iden >>> eq)

  , wnaf5 = wnafpre >>> wnaf5step256 >>> ih

  , wnaf16 = wnafpre >>> wnaf16step256 >>> ih

  , generator =
     let
      step = match (drop double) (drop double &&& take generatorSmall >>> offsetPoint)
      step2 = ooh &&& (oih &&& ih >>> step) >>> step
      step4 = ooh &&& (oih &&& ih >>> step2) >>> step2
      step8 = ooh &&& (oih &&& ih >>> step4) >>> step4
      step16 = ooh &&& (oih &&& ih >>> step8) >>> step8
      step32 = ooh &&& (oih &&& ih >>> step16) >>> step16
      step64 = ooh &&& (oih &&& ih >>> step32) >>> step32
      step128 = ooh &&& (oih &&& ih >>> step64) >>> step64
      step256 = ooh &&& (oih &&& ih >>> step128) >>> step128
     in
      wnaf16 &&& (unit >>> inf) >>> step256

  , ecMult =
     let
      body = (unit >>> inf) &&& (ooh >>> scalarTable5) &&& (oih >>> wnaf5) &&& (ih >>> wnaf16)
         >>> iooh &&& step256
         >>> ioh &&& (oh &&& iih >>> mul)
      step = iiih &&& (iioh &&& take double &&& ioih >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5) >>> offsetPoint)) &&& iooh
         >>> match ioh (ioh &&& (take generatorSmall &&& iih >>> zinv) >>> offsetPoint)
      step2 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step) &&& drop (oh &&& iooh &&& iioh) >>> step
      step4 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step2) &&& drop (oh &&& iooh &&& iioh) >>> step2
      step8 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step4) &&& drop (oh &&& iooh &&& iioh) >>> step4
      step16 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step8) &&& drop (oh &&& iooh &&& iioh) >>> step8
      step32 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step16) &&& drop (oh &&& iooh &&& iioh) >>> step16
      step64 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step32) &&& drop (oh &&& iooh &&& iioh) >>> step32
      step128 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step64) &&& drop (oh &&& iooh &&& iioh) >>> step64
      step256 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step128) &&& drop (oh &&& iooh &&& iioh) >>> step128
     in
      -- In the case that the 'a' parameter is infinity or the 'na' parameter is 0, then scalarTable5 is not built.
      -- In particular the globalZ is set to 1 instead of whatever would have been generated by the table.
      or (take (take isInf)) (take (drop scalarIsZero)) &&& iden
  >>> cond (drop generator) body

  , pkPoint =
     let
      k1 = (scribe256 7 &&& cub >>> add >>> sqrt) &&& iden
       >>> match (injl unit) (injr k2)
      k2 = swapP &&& (unit >>> feOne)
      lt = sub256 >>> oh
     in
      (iden &&& scribe (toWord256 feOrder) >>> lt) &&& iden
  >>> cond k1 (injl unit)

  , sigUnpack =
     let
      lt = subtractor word256 >>> oh
     in
      and (oh &&& scribe (toWord256 feOrder) >>> lt)
          (ih &&& scribe (toWord256 scalarOrder) >>> lt)
  &&& iden
  >>> cond (injr iden) (injl unit)

  , scalarUnrepr = (iden &&& scribe (toWord256 scalarOrder) >>> subtractor word256) &&& iden
               >>> ooh &&& (oih &&& ih)
               >>> cond ih oh

  , schnorrVerify =
     let
      k1 = ioh &&& (iih &&& oh)
       >>> match false k2
      k2 = iioh &&& ((oh &&& ioh) &&& iiih >>> ecMult)
       >>> and eqXCoord (drop hasQuadY)
      nege = (scribe (toWord256 scalarOrder) &&& (h >>> scalarUnrepr) >>> sub256 >>> ih)
      iv = scribe (toWord256 0x048d9a59fe39fb0528479648e4a660f9814b9e660469e80183909280b329e454)
      h = m >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock
      m = (ioh &&& ooh) &&& (oih &&& (scribe (toWord256 0x8000000000000000000000000000000000000000000000000000000000000500)))
     in
      drop sigUnpack &&& (take (take pkPoint) &&& nege)
  >>> match false k1
  }
   where
    cub = iden &&& sqr >>> mul

    mulInt i = scribe256 (i `mod` feOrder) &&& iden >>> mul

    -- Common code shared between 'inv' and 'sqrt'.
    tower = iden &&& cub
        >>> ih &&& (oh &&& drop sqr >>> mul)
        >>> oh &&& ((ih &&& (oh &&& (drop (iden &&& (iden &&& (sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr >>> sqr) >>> mul) >>> sqr >>> sqr) >>> mul -- (x2,(x3,x11))
                          >>> iden &&& foldr1 (>>>) (replicate 11 sqr) >>> mul))                      -- (x2,(x3,x22))
                 >>> ih &&& (oh &&& drop (iden &&& foldr1 (>>>) (replicate 22 sqr) >>> mul            -- (x2,(x22,(x3,x44)))
                                     >>> (iden &&& (iden &&& foldr1 (>>>) (replicate 44 sqr) >>> mul  -- (x2,(x22,(x3,(x44,x88))))
                                                 >>> iden &&& foldr1 (>>>) (replicate 88 sqr) >>> mul -- (x2,(x22,(x3,(x44,x176))))
                                           >>> foldr1 (>>>) (replicate 44 sqr)) >>> mul)              -- (x2,(x22,(x3,x220)))
                                    >>> sqr >>> sqr >>> sqr) >>> mul                                  -- (x2,(x22,x223))
                           >>> foldr1 (>>>) (replicate 23 sqr)) >>> mul                               -- (x2,t1)
                 >>> foldr1 (>>>) (replicate 5 sqr))

    zinv = (ooh &&& drop sqr >>> mul) &&& (oih &&& drop cub >>> mul)

    -- Compute odd-multiples of a point for small (5-bit) multiples.
    -- The result is in Jacobian coordinates but the z-coordinate is identical for all outputs.
    scalarTable5 :: term GEJ (FE, Vector8 GE)
    scalarTable5 = iden &&& double
               >>> iih &&& (((ooh &&& iih >>> zinv) &&& oih) &&& ioh -- (dz, (a', (dx,dy)))
                        >>> pass1_8)
               >>> (oh &&& iih >>> mul) &&& drop (take pass2_8)
     where
      pass1_2 = iden &&& offsetPointEx >>> (ioh &&& (oooh &&& iioh)) &&& (iih &&& oih)
      pass1_4 = pass1_2 >>> oh &&& drop (offsetPointEx &&& ih >>> ooh &&& (oih &&& ih >>> pass1_2)) >>> (ioh &&& (oh &&& iioh)) &&& iiih
      pass1_8 = pass1_4 >>> oh &&& drop (offsetPointEx &&& ih >>> ooh &&& (oih &&& ih >>> pass1_4)) >>> (ioh &&& (oh &&& iioh)) &&& drop (drop ioih)
      pass2_1 = oh &&& ih >>> zinv
      pass2_2 = (oioh &&& (ooh &&& ih >>> mul)) &&& (oiih &&& ih >>> pass2_1) >>> (take pass2_1 &&& ih) &&& oih
      pass2_4 = (ooh &&& oioh) &&& (oiih &&& ih >>> pass2_2) >>> (oih &&& (ooh &&& iih >>> mul) >>> pass2_2) &&& ioh >>> (ooh &&& ih) &&& oih
      pass2_8 = ( oh &&&  ioh) &&& ( iih &&& (unit >>> feOne) >>> pass2_4) >>> (oih &&& (ooh &&& iih >>> mul) >>> pass2_4) &&& ioh >>> ooh &&& ih

    -- Given an odd-multiples table of affinte points, extract the @i@th element of the table.
    -- If the index is negative @i@, then return the point negation of the @i@th element of the table.
    lookupTable5 :: term (Word4, Vector8 GE) GE
    lookupTable5 = oooh &&& ooih &&& oih &&& ih
               >>> cond neg pos
     where
      pos = ioih &&& (iooh &&& (oh &&& iih >>> cond ih oh) >>> cond ih oh) >>> cond ih oh
      neg = ioih &&& (iooh &&& (oh &&& iih >>> cond oh ih) >>> cond oh ih) >>> cond (take geNegate) (drop geNegate)

    -- Returns a small, signed integer multiple of the secp256k1's generator as a normalized affine point.
    generatorSigned :: Word a -> term a GEJ
    generatorSigned SingleV = copair inf ((generator0 >>> geNegate) &&& feOne)
    generatorSigned (DoubleV w) = ih &&& take rec >>> generator1 w
     where
      rec = generatorSigned w

    generatorSmall :: term Word16 GE
    generatorSmall = generatorSigned word16 >>> normalizePoint

-- | This function is given a public key, a 256-bit message, and a signature, and asserts that the signature is valid for the given message and public key.
schnorrAssert :: Assert term => Lib term -> term ((XOnlyPubKey, Word256), Sig) ()
schnorrAssert m = assert (schnorrVerify m)

-- | An instance of the Sha256 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: Core term => Lib term
lib = mkLib Sha256.lib
