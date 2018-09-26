{-# LANGUAGE DeriveFunctor #-}
module Simplicity.LensEx
 ( review, under, zipWithOf
 , FromG, FromF, from
 , _bits, bits
 ) where

import Data.Functor.Constant (Constant(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Product (Product(..))
import Data.List (foldl')
import Data.Proxy (asProxyTypeOf)
import Data.Bits (FiniteBits, finiteBitSize, setBit, testBit, zeroBits)

review :: ((Constant () a -> b) -> Constant () s -> t) -> b -> t
review l b = l (const b) (Constant ())

under :: ((Identity a -> b) -> Identity s -> t) -> (a -> b) -> (s -> t)
under l f = l (f . runIdentity) . Identity

zipWithOf :: ((Product Identity Identity a -> b) -> (Product Identity Identity s -> t)) -> (a -> a -> b) -> (s -> s -> t)
zipWithOf l f s0 s1 = l f' (Pair (Identity s0) (Identity s1))
 where
  f' (Pair (Identity a0) (Identity a1)) = f a0 a1

newtype FromG r f x = FromG (r -> f x) deriving Functor
newtype FromF r1 r2 g x = FromF ((g x -> r1) -> r2) deriving Functor

from :: (Functor g, Functor f) => ((FromG (g s) g a -> FromF (g s) (f b -> g a) f b) -> (FromG (g s) g s -> FromF (g s) (f b -> g a) f t)) -> (f t -> g s) -> f b -> g a
from l = l'
 where
  FromF l' = l (\(FromG f) -> FromF (f .)) (FromG id)

_bits :: (FiniteBits b, Applicative f) => (Bool -> f Bool) -> b -> f b
_bits = under bits

bits :: (FiniteBits b, Functor g, Applicative f) => (g Bool -> f Bool) -> g b -> f b
bits f a = r
 where
  p i = flip testBit i <$> a
  x = undefined `asProxyTypeOf` r
  assemble l = foldl' setBit zeroBits [i | (i,b) <- zip [0..] l, b]
  r = assemble <$> sequenceA [f (p i) | i<-[0..finiteBitSize x-1]]
