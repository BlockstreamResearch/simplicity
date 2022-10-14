-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Arbitrary
 ( genBoundaryCases,
   genSignature
 ) where

import Data.Serialize (encode)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.LibSecp256k1.Spec

import Test.Tasty.QuickCheck (Gen, chooseBoundedIntegral, chooseInteger, oneof)

genBoundaryCases :: (Bounded w, Integral w) => w -> Gen w
genBoundaryCases 0 = oneof [return 0, chooseBoundedIntegral (1, maxBound)]
genBoundaryCases 1 = oneof [return 0, return 1, chooseBoundedIntegral (2, maxBound)]
genBoundaryCases boundary = oneof [return 0, chooseBoundedIntegral (1, boundary-1), return boundary, chooseBoundedIntegral (boundary + 1, maxBound)]

genSignature :: Hash256 -> Gen (PubKey, Sig)
genSignature msg = do
  priv <- scalar <$> chooseInteger (1, scalar_repr maxBound)
  k <- scalar <$> chooseInteger (1, scalar_repr maxBound)
  let Just (GE px py) = gej_normalize $ linear_combination [] priv
  let Just (GE rx ry) = gej_normalize $ linear_combination [] k
  let pub = PubKey (fe_pack px)
  let msgBody = encode (fe_pack rx) <> encode pub <> encode msg
  let e = scalar . integerHash256 $ taggedHash "BIP0340/challenge" msgBody
  let s = (if fe_is_odd ry then scalar_negate k else k) `scalar_add`
          (scalar_multiply e (if fe_is_odd py then scalar_negate priv else priv))
  return $ (pub, Sig (fe_pack rx) (scalar_pack s))
