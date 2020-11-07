{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.MultiBit
  ( fill, low, high
  , complement
  , bitwise_and, bitwise_or, bitwise_xor
  , bitwise_maj, bitwise_xor3, bitwise_ch
  , some, all, eq
  , leftmost, left_pad_low, left_pad_high, left_extend
  , rightmost, right_pad_low, right_pad_high, right_extend
  , full_left_shift1, full_right_shift1, full_shift
  , shift_const_by, left_rotate1, right_rotate1, rotate_const
  , mapZV, transpose
  , module Simplicity.Ty.Word
  ) where

import Prelude hiding (Word, drop, take, not, or, and, last, all)

import qualified Data.Bits as Bits
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Bit
import Simplicity.Term.Core
import Simplicity.Ty.Word

fill :: (Core term, TyC c) => term c a -> Vector a b -> term c b
fill t SingleV = t
fill t (DoubleV w) = rec &&& rec
 where
  rec = fill t w

low :: Core term => Word a -> term () a
low = fill false

high :: Core term => Word a -> term () a
high = fill true

complement :: Core term => Word a -> term a a
complement SingleV = not iden
complement (DoubleV w) = take rec &&& drop rec
 where
  rec = complement w

bitwise_bin :: forall term a v. Core term => term (a, a) a -> Vector a v -> term (v, v) v
bitwise_bin op = go
 where
  go :: forall v. Vector a v -> term (v, v) v
  go SingleV = op
  go (DoubleV w) = (ooh &&& ioh >>> rec) &&& (oih &&& iih >>> rec)
   where
    rec = go w

bitwise_tri :: forall term a v. Core term => term (a, (a, a)) a -> Vector a v -> term (v, (v, v)) v
bitwise_tri op = go
 where
  go :: forall v. Vector a v -> term (v, (v, v)) v
  go SingleV = op
  go (DoubleV w) = (ooh &&& (iooh &&& iioh) >>> rec) &&& (oih &&& (ioih &&& iiih) >>> rec)
   where
    rec = go w

bitwise_and :: Core term => Word a -> term (a, a) a
bitwise_and = bitwise_bin (and oh ih)

bitwise_or :: Core term => Word a -> term (a, a) a
bitwise_or = bitwise_bin (or oh ih)

bitwise_xor :: Core term => Word a -> term (a, a) a
bitwise_xor = bitwise_bin (xor oh ih)

bitwise_maj :: Core term => Word a -> term (a, (a, a)) a
bitwise_maj = bitwise_tri maj

bitwise_xor3 :: Core term => Word a -> term (a, (a, a)) a
bitwise_xor3 = bitwise_tri xor3

bitwise_ch :: Core term => Word a -> term (a, (a, a)) a
bitwise_ch = bitwise_tri ch

some :: Core term => Word a -> term a Bit
some SingleV = iden
some (DoubleV w) = or (take rec) (drop rec)
 where
  rec = some w

all :: Core term => Word a -> term a Bit
all SingleV = iden
all (DoubleV w) = and (take rec) (drop rec)
 where
  rec = all w

leftmost :: (Core term, TyC a, TyC b) => Vector a b -> term b a
leftmost SingleV = iden
leftmost (DoubleV v) = take (leftmost v)

rightmost :: (Core term, TyC a, TyC b) => Vector a b -> term b a
rightmost SingleV = iden
rightmost (DoubleV v) = drop (rightmost v)

left_pad_pad :: Core term => term a a -> Vector a b -> term a b
left_pad_pad _ SingleV = iden
left_pad_pad t (DoubleV v) = fill t v &&& left_pad_pad t v

left_pad_low :: (Core term, TyC a) => Word a -> Vector a b -> term a b
left_pad_low w v = left_pad_pad (unit >>> low w) v

left_pad_high :: (Core term, TyC a) => Word a -> Vector a b -> term a b
left_pad_high w v = left_pad_pad (unit >>> high w) v

left_extend :: (Core term, TyC a, TyC b) => Word a -> Vector a b -> term a b
left_extend w v = leftmost w &&& iden >>> cond (left_pad_high w v) (left_pad_low w v)

right_pad_pad :: Core term => term a a -> Vector a b -> term a b
right_pad_pad _ SingleV = iden
right_pad_pad t (DoubleV v) = right_pad_pad t v &&& fill t v

right_pad_low :: (Core term, TyC a) => Word a -> Vector a b -> term a b
right_pad_low w v = right_pad_pad (unit >>> low w) v

right_pad_high :: (Core term, TyC a) => Word a -> Vector a b -> term a b
right_pad_high w v = right_pad_pad (unit >>> high w) v

right_extend :: (Core term, TyC a, TyC b) => Word a -> Vector a b -> term a b
right_extend w v = rightmost w &&& iden >>> cond (right_pad_high w v) (right_pad_low w v)

full_left_shift1 :: Core term => Vector a va -> term (va, a) (a, va)
full_left_shift1 SingleV = iden
full_left_shift1 (DoubleV v) = ooh &&& (oih &&& ih >>> rec) >>> (oh &&& ioh >>> rec) &&& iih >>> ooh &&& (oih &&& ih)
 where
  rec = full_left_shift1 v

full_right_shift1 :: Core term => Vector a va -> term (a, va) (va, a)
full_right_shift1 SingleV = iden
full_right_shift1 (DoubleV v) = (oh &&& ioh >>> rec) &&& iih >>> ooh &&& (oih &&& ih >>> rec) >>> (oh &&& ioh) &&& iih
 where
  rec = full_right_shift1 v

full_shift :: (Core term, TyC a, TyC b) => Vector x a -> Vector x b -> term (a, b) (b, a)
full_shift wa wb = go (compareVectorSize wb wa)
 where
  go :: (Core term, TyC a, TyC b) => Either (Vector (a, a) b) (Either (b :~: a) (Vector (b, b) a)) -> term (a, b) (b, a)
  go (Left v) = full_right_shift1 (vectorComp vector2 v)
  go (Right (Left Refl)) = iden
  go (Right (Right v)) = full_left_shift1 (vectorComp vector2 v)

shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b b
shift_const_by t v n | wordSize v <= n = unit >>> fill t v
                     | n < 0 = right_shift_const_by t v (-n)
                     | otherwise = compose (go t v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
  go t SingleV 0 = []
  go t v@(DoubleV v') n | even n = rec (n `div` 2)
                        | otherwise = left_shift1 : rec ((n-1) `div` 2)
   where
    left_shift1 = iden &&& (unit >>> t) >>> full_left_shift1 v >>> ih
    rec = go (t &&& t) (vectorPromote v')

right_shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b b
right_shift_const_by t v n | wordSize v <= n = unit >>> fill t v
                           | n < 0 = shift_const_by t v (-n)
                           | otherwise = compose (go t v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
  go t SingleV 0 = []
  go t v@(DoubleV v') n | even n = rec (n `div` 2)
                        | otherwise = right_shift1 : rec ((n-1) `div` 2)
   where
    right_shift1 = (unit >>> t) &&& iden >>> full_right_shift1 v >>> oh
    rec = go (t &&& t) (vectorPromote v')

left_rotate1 :: (Core term, TyC a, TyC b) => Vector a b -> term b b
left_rotate1 v = iden &&& leftmost v >>> full_left_shift1 v >>> ih

right_rotate1 :: (Core term, TyC a, TyC b) => Vector a b -> term b b
right_rotate1 v = rightmost v &&& iden >>> full_right_shift1 v >>> oh

-- left rotate by a constant
rotate_const :: (Core term, TyC a, TyC b) => Vector a b -> Int -> term b b
rotate_const v n = compose (go v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => Vector a b -> Int -> [term b b]
  go SingleV n = []
  go v@(DoubleV v') n | even n = rec (n `div` 2)
                      | 1 == n `mod` 4 = left_rotate1 v : rec ((n-1) `div` 2)
                      | 3 == n `mod` 4 = right_rotate1 v : rec ((n+1) `div` 2)
   where
    rec = go (vectorPromote v')

mapZV :: (Core term) => ZipVector x nx y ny -> term x y -> term nx ny
mapZV SingleZV t = t
mapZV (DoubleZV zv) t = take rec &&& drop rec
 where
  rec = mapZV zv t

-- Polymorphic helper type isomorphic to @term a b@ via Yoneda embedding.
data Yoneda term a b = Yoneda (forall d. TyC d => term b d -> term a d)
runYoneda :: (Core term, TyC b) => Yoneda term a b -> term a b
runYoneda (Yoneda k) = k iden

yId :: Yoneda term a a
yId = Yoneda id

yoh :: (Core term, TyC a, TyC b, TyC c) => Yoneda term c (a, b) -> Yoneda term c a
yoh (Yoneda k) = Yoneda (\t -> k (take t))

yih :: (Core term, TyC a, TyC b, TyC c) => Yoneda term c (a, b) -> Yoneda term c b
yih (Yoneda k) = Yoneda (\t -> k (drop t))

transpose :: (Core term, TyC mx, TyC nmx) => ZipVector x mx nx mnx -> ZipVector mx nmx x nx -> term nmx mnx
transpose mzv nzv = go mzv nzv yId
 where
  go :: (Core term, TyC nm, TyC m) => ZipVector x kx nx knx -> ZipVector m nm x nx -> Yoneda term m kx -> term nm knx
  go SingleZV nzv t = mapZV nzv (runYoneda t)
  go (DoubleZV zv) nzv t = go zv nzv (yoh t) &&& go zv nzv (yih t)
