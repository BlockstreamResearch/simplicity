module Simplicity.BitMachine.StaticAnalysis 
 ( ExtraCellsBnd, extraCellsBnd, cellsBnd
 ) where

import Simplicity.Term
import Simplicity.BitMachine.Ty

newtype ExtraCellsBnd a b = ExtraCellsBnd { extraCellsBnd :: Int }

instance Core ExtraCellsBnd where
  iden = ExtraCellsBnd 0
  comp arrS@(ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (bitSizeR b + max s t)
   where
    b = reifyProxy arrS
  unit = ExtraCellsBnd 0
  injl (ExtraCellsBnd t) = ExtraCellsBnd t
  injr (ExtraCellsBnd t) = ExtraCellsBnd t
  match (ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (max s t)
  pair (ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (max s t)
  take (ExtraCellsBnd t) = ExtraCellsBnd t
  drop (ExtraCellsBnd t) = ExtraCellsBnd t

cellsBnd :: (TyC a, TyC b) => ExtraCellsBnd a b -> Int
cellsBnd t = bitSizeR a + bitSizeR b + extraCellsBnd t
 where
  (a,b) = reifyArrow t
