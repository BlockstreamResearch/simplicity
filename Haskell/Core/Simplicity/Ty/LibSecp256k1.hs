module Simplicity.Ty.LibSecp256k1
 ( FE, GE, GEJ, Scalar, Point
 , PubKey, Sig
 , fromFE, toFE
 , fromGE, toGE
 , fromGEJ, toGEJ
 ) where

import qualified Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.Ty.Word

-- | Simplicity's representation of field elements.
type FE = Word256

-- | A point in compressed coordinates.
-- The point at infinity isn't representable.
type Point = (Bit, FE)

-- | A point in affine coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity isn't representable.
type GE = (FE, FE)

-- | A point in Jacobian coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity's representatives are of the form @((a^2, a^3), 0)@, with @((0, 0), 0)@ being the canonical representative.
type GEJ = (GE, FE)

-- | Scalar values, those less than the order of secp256's elliptic curve, are represented by a 256-bit word type.
type Scalar = Word256

-- | A format for (Schnorr) elliptic curve x-only public keys.
-- The y-coordinate is implicity the one on the curve that has an even y coordinate.
-- The point at infinity isn't representable (nor is it a valid public key to begin with).
type PubKey = Word256

-- | A format for Schnorr signatures.
type Sig = (Word256, Word256)

fromFE :: FE -> Spec.FE
fromFE = Spec.fe . fromWord256

toFE :: Spec.FE -> FE
toFE = toWord256 . toInteger . Spec.fe_pack

fromGE :: GE -> Spec.GE
fromGE (x,y) = Spec.GE (fromFE x) (fromFE y)

toGE :: Spec.GE -> GE
toGE (Spec.GE x y) = (toFE x, toFE y)

fromGEJ :: GEJ -> Spec.GEJ
fromGEJ ((x,y),z) = Spec.GEJ (fromFE x) (fromFE y) (fromFE z)

toGEJ :: Spec.GEJ -> GEJ
toGEJ (Spec.GEJ x y z) = ((toFE x, toFE y), toFE z)
