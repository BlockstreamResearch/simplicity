module Simplicity.Arbitrary
 ( genBoundaryCases,
   genSignature
 ) where

import Data.Serialize (encode)

import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.LibSecp256k1.Spec
import Simplicity.Ty.Word

import Test.Tasty.QuickCheck (Arbitrary(..), Gen, chooseBoundedIntegral, chooseInteger, growingElements, oneof)

genBoundaryCases :: (Bounded w, Integral w) => w -> Gen w
genBoundaryCases 0 = oneof [return 0, chooseBoundedIntegral (1, maxBound)]
genBoundaryCases 1 = oneof [return 0, return 1, chooseBoundedIntegral (2, maxBound)]
genBoundaryCases boundary = oneof [return 0, chooseBoundedIntegral (1, boundary-1), return boundary, chooseBoundedIntegral (boundary + 1, maxBound)]

genSignature :: Hash256 -> Gen (PubKey, Sig)
genSignature msg = do
  priv <- scalar <$> chooseInteger (1, scalar_repr maxBound)
  k <- scalar <$> chooseInteger (1, scalar_repr maxBound)
  let Just (GE px py) = gej_normalize $ off_curve_linear_combination [] priv
  let Just (GE rx ry) = gej_normalize $ off_curve_linear_combination [] k
  let pub = PubKey (fe_pack px)
  let msgBody = encode (fe_pack rx) <> encode pub <> encode msg
  let e = scalar . integerHash256 $ taggedHash "BIP0340/challenge" msgBody
  let s = (if fe_is_odd ry then scalar_negate k else k) `scalar_add`
          (scalar_multiply e (if fe_is_odd py then scalar_negate priv else priv))
  return $ (pub, Sig (fe_pack rx) (scalar_pack s))

instance Arbitrary SomeConstWordContent where
  arbitrary = do
    n <- growingElements [0..10]
    v <- chooseInteger (0, 2^n - 1)
    return $ scwc v n
   where
    scwc v 0 = SomeConstWordContent (ConstWordContent SingleV v)
    scwc v n | 0 < n = case scwc v (n - 1) of SomeConstWordContent (ConstWordContent w _) -> SomeConstWordContent (ConstWordContent (DoubleV w) v)
