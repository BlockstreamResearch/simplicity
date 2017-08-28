module Simplicity.BitMachine.Ty
 ( bitSize, bitSizeR
 , padL, padR, padLR, padRR
 ) where

import Data.Functor.Fixedpoint (cata)

import Simplicity.Ty

bitSize :: Ty -> Int
bitSize = cata bitSizeF
 where
  bitSizeF One = 0
  bitSizeF (Sum a b) = 1 + max a b
  bitSizeF (Prod a b) = a + b

bitSizeR :: TyReflect a -> Int
bitSizeR = bitSize . unreflect

padL :: Ty -> Ty -> Int
padL a b = max bsa bsb - bsa
 where
  bsa = bitSize a
  bsb = bitSize b

padLR :: TyReflect a -> TyReflect b -> Int
padLR a b = padL (unreflect a) (unreflect b)

padR :: Ty -> Ty -> Int
padR a b = max bsa bsb - bsb
 where
  bsa = bitSize a
  bsb = bitSize b

padRR :: TyReflect a -> TyReflect b -> Int
padRR a b = padR (unreflect a) (unreflect b)
