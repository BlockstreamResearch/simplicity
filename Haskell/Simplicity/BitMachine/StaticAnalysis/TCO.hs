module Simplicity.BitMachine.StaticAnalysis.TCO 
 ( ExtraCellsBnd, extraCellsBnd, cellsBnd
 ) where

import Simplicity.Term
import Simplicity.BitMachine.Ty

data ExtraCellsBnd a b = ExtraCellsBnd Int Int

extraCellsBnd r (ExtraCellsBnd n m) = max (n - r) m

instance Core ExtraCellsBnd where
  iden = ExtraCellsBnd 0 0
  comp arrS@(ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd (maximum [s + sn, tn, s + tm]) (s + sm)
   where
    s = bitSizeR b
    b = reifyProxy arrS
  unit = ExtraCellsBnd 0 0
  injl (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  injr (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  match (ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd (max sn tn) (max sm tm)
  pair (ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd tn (maximum [sn, sm, tm])
  take (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  drop (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm

cellsBnd :: (TyC a, TyC b) => ExtraCellsBnd a b -> Int
cellsBnd t = bitSizeR a + bitSizeR b + extraCellsBnd 0 t
 where
  (a,b) = reifyArrow t
