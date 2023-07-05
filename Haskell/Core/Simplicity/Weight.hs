module Simplicity.Weight
 ( Weight, milli, milliWeight
 ) where

import Data.Fixed (Milli)

-- | Simplicity CPU cost is measured in 'Weight' units, the same units as Bitcoin transaction size.
-- Simplicity expressions are weighed to 3 decimal places of accuracy.
type Weight = Milli

-- | Construct a weight from a value in mulliWUs.
milli :: Real a => a -> Weight
milli n = realToFrac n / 1000

-- | Return a 'Weight' value as an integer in milliWUs.
milliWeight :: Weight -> Integer
milliWeight = round . (1000*)
