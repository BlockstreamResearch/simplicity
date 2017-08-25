{-# LANGUAGE GADTs #-}
module Simplicity.BitMachine.Ty
 ( encode, decode
 , bitSize, bitSizeR
 , padL, padR, padLR, padRR
 , executeUsing
 ) where

import Control.Monad (guard)
import Data.Functor.Fixedpoint (cata)

import Simplicity.BitMachine
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

safeSplitAt :: Int -> [a] -> Maybe ([a], [a])
safeSplitAt n l = do
  guard $ 0 <= n && n <= length l
  return (splitAt n l)

encode :: TyC a => a -> [Cell]
encode x = encodeR reify x []
 where
  encodeR :: TyReflect a -> a -> [Cell] -> [Cell]
  encodeR OneR () = id
  encodeR (SumR a b) (Left x) = ([Just False] ++) . (replicate (padLR a b) Nothing ++) . encodeR a x
  encodeR (SumR a b) (Right y) = ([Just True] ++) . (replicate (padRR a b) Nothing ++) . encodeR b y
  encodeR (ProdR a b) (x, y) = encodeR a x . encodeR b y

decode :: TyC a => [Cell] -> Maybe a
decode = decodeR reify
 where
  decodeR :: TyReflect a -> [Cell] -> Maybe a
  decodeR OneR [] = Just ()
  decodeR (SumR a b) (Just v:l) = do
    (l0, l1) <- safeSplitAt (pad a b) l
    guard (all (==Nothing) l0)
    if v then Right <$> decodeR b l1 else Left <$> decodeR a l1
   where
    pad = if v then padRR else padLR
  decodeR (ProdR a b) l = do
    (l0, l1) <- safeSplitAt (bitSizeR a) l
    (,) <$> decodeR a l0 <*> decodeR b l1
  decodeR _ _ = Nothing

executeUsing :: (TyC a, TyC b) => (arr a b -> [Cell] -> Int -> Maybe [Cell]) -> arr a b -> a -> Maybe b
executeUsing make program input = result
 where
  result = make program (encode input) (bitSizeR (reifyProxy result)) >>= decode
