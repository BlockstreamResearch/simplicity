-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Arbitrary
 ( genBoundaryCases,
 ) where

import Test.Tasty.QuickCheck (Gen, chooseBoundedIntegral, oneof)

genBoundaryCases :: (Bounded w, Integral w) => w -> Gen w
genBoundaryCases 0 = oneof [return 0, chooseBoundedIntegral (1, maxBound)]
genBoundaryCases 1 = oneof [return 0, return 1, chooseBoundedIntegral (2, maxBound)]
genBoundaryCases boundary = oneof [return 0, chooseBoundedIntegral (1, boundary-1), return boundary, chooseBoundedIntegral (boundary + 1, maxBound)]
