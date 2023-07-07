{-# LANGUAGE GADTs #-}
module Simplicity.BitMachine.StaticAnalysis.Cost
  ( TermWeight(..)
  , overhead
  , milliWeigh
-- * Reexports
  , Weight
  ) where

import Simplicity.BitMachine.Ty
import Simplicity.Term.Core
import Simplicity.Weight

-- | The CPU weight of a Simplicity expression.
--
-- Note that serializing an expression could generalize the types of expressions and sub-expressions, lowering the weight.
newtype TermWeight a b = TermWeight { weigh :: Weight }

-- | Cost of a term in milli weight units
milliWeigh :: TermWeight a b -> Integer
milliWeigh = milliWeight . weigh

instance Core TermWeight where
  iden = result
    where
     result = TermWeight $ overhead + milli (bitSizeR (reifyProxy result))
  comp s0@(TermWeight s) (TermWeight t) = TermWeight $ overhead + milli (bitSizeR (reifyProxy s0)) + s + t
  unit = TermWeight overhead
  injl (TermWeight s) = TermWeight $ overhead + s
  injr (TermWeight s) = TermWeight $ overhead + s
  match (TermWeight s) (TermWeight t) = TermWeight $ overhead + max s t
  pair (TermWeight s) (TermWeight t) = TermWeight $ overhead + s + t
  take (TermWeight s) = TermWeight $ overhead + s
  drop (TermWeight s) = TermWeight $ overhead + s

instance Assert TermWeight where
  assertl s _ = match s (TermWeight 0)
  assertr _ t = match (TermWeight 0) t
  fail _ = TermWeight 0

instance Witness TermWeight where
  witness _ = result
   where
    result = TermWeight $ overhead + milli (bitSizeR (reifyProxy result))

instance Delegate TermWeight where
  disconnect s0@(TermWeight s) t0@(TermWeight t) = TermWeight $ overhead + milli (2 * bitSizeR w256a + bitSizeR bc + bitSizeR b) + s + t
   where
    (w256a, bc@(ProdR b _c)) = reifyArrow s0

-- :TODO: This overhead is just estimated.  It needs to be replaced with a measured value.
-- :TODO: Perhaps fold this into a generic 'mkTermWeight' or 'withOverhead' constructor that adds in the overhead.
-- | Helper value for creating 'TermWeight' instaces.
overhead :: Weight
overhead = 0.01
