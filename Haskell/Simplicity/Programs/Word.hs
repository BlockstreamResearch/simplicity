{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.Word
  ( module Simplicity.Ty.Word
  -- * Arithmetic
  , zero
  , adder, fullAdder, multiplier, fullMultiplier
  -- * Bit-wise operations
  , shift, rotate
  , bitwise, bitwiseTri
  ) where

import Prelude hiding (Word, drop, take, not, or)

import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Bit
import Simplicity.Term.Core
import Simplicity.Ty.Word

-- | Simplicity expression for the constant function that returns the representation of 0.
--
-- @
-- 'fromWord' w ('zero' w _) = 0
-- @
zero :: (Core term, TyC a) => Word b -> term a b
zero BitW = false
zero (DoubleW w) = rec &&& rec
 where
  rec = zero w

-- | Simplicity expression for computing the sum of two words, including the carry bit.
--
-- @
-- 'fromWord' 'BitW' c * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y
--  where
--   (c, z) = 'adder' w (x, y)
-- @  
adder :: Core term => Word a -> term (a, a) (Bit, a)
adder BitW = cond (iden &&& not iden) (false &&& iden)
adder (DoubleW w) = (ooh &&& ioh) &&& (oih &&& iih >>> rec)
                >>> iih &&& (oh &&& ioh >>> fa)
                >>> ioh &&& (iih &&& oh)
 where
  rec = adder w
  fa = fullAdder w

-- | Simplicity expression for computing the sum of two words and a carry input bit, including the carry output bit.
--
-- @
-- 'fromWord' 'BitW' cout * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y + 'fromWord' 'BitW' cin
--  where
--   (cout, z) = 'fullAdder' w ((x, y), cin)
-- @  
fullAdder :: Core term => Word a -> term ((a, a), Bit) (Bit, a)
fullAdder BitW = take add &&& ih
             >>> ooh &&& (oih &&& ih >>> add)
             >>> cond true oh &&& iih
 where
  add = adder BitW
fullAdder (DoubleW w) = take (ooh &&& ioh) &&& (take (oih &&& iih) &&& ih >>> rec)
                    >>> iih &&& (oh &&& ioh >>> rec)
                    >>> ioh &&& (iih &&& oh)
 where
  rec = fullAdder w

-- | 'fullMultiplier' is a Simplicity expression that helps compute products of larger word sizes from smaller word sizes.
--
-- @
-- 'fromWord' ('DoubleW' w) ('fullMultiplier' w ((a, b), (c, d))) = 'fromWord' w a * 'fromWord' w b  + 'fromWord' w c + 'fromWord' w d
-- @  
fullMultiplier :: Core term => Word a -> term ((a, a), (a, a)) (a, a)
fullMultiplier BitW = ih &&& take (cond iden false)
                  >>> fullAdder BitW
fullMultiplier (DoubleW w) = take (ooh &&& (ioh &&& oih))
                         &&& ((take (ooh &&& iih) &&& drop (ooh &&& ioh) >>> rec)
                         &&& (take (oih &&& iih) &&& drop (oih &&& iih) >>> rec))
                         >>> take (oh &&& ioh)
                         &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> rec))
                         >>> (oh &&& drop (ioh &&& ooh) >>> rec) &&& drop (iih &&& oih)
 where
  rec = fullMultiplier w

-- | Simplicity expression for computing the product of two words, returning a doubled size word.
--
-- @
-- 'fromWord' ('DoubleW' w) ('multiplier' w (x, y)) = 'fromWord' w x * 'fromWord' w y
-- @  
multiplier :: Core term => Word a -> term (a, a) (a, a)
multiplier BitW = false &&& cond iden false
multiplier (DoubleW w) = (ooh &&& (ioh &&& oih))
                     &&& ((ooh &&& iih >>> rec) &&& (oih &&& iih >>> rec))
                     >>> take (oh &&& ioh)
                     &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> fm))
                     >>> (oh &&& drop (ioh &&& ooh) >>> fm) &&& drop (iih &&& oih)
 where
  rec = multiplier w
  fm = fullMultiplier w

-- | A Simplicity combinator for lifting a binary bit operation to a binary word operation that applies the bit operation bit-wise to each bit of the word.
bitwise :: forall term a. Core term => term (Bit, Bit) Bit -> Word a -> term (a, a) a
bitwise op = go
 where
  go :: forall a. Word a -> term (a, a) a
  go BitW = op
  go (DoubleW w) = (ooh &&& ioh >>> rec) &&& (oih &&& iih >>> rec)
   where
    rec = go w

-- | A Simplicity combinator for lifting a trinary bit operation to a trinary word operation that applies the bit operation bit-wise to each bit of the word.
-- This is similar to 'bitwise' except works with trinary bit operations instead of binary operations.
bitwiseTri :: forall term a. Core term => term (Bit, (Bit, Bit)) Bit -> Word a -> term (a, (a, a)) a
bitwiseTri op = go
 where
  go :: forall a. Word a -> term (a, (a, a)) a
  go BitW = op
  go (DoubleW w) = (ooh &&& (iooh &&& iioh) >>> rec)
               &&& (oih &&& (ioih &&& iiih) >>> rec)
   where
    rec = go w

-- @'BiggerWord' a b@ is a GADT where @a@ and @b@ are Simplicity word types and @a@ has fewer bits than @b@
-- This is a helper type that is used in the definitions of 'shift' and 'rotate'.
data BiggerWord a b where
  JustBigger :: TyC a => Word a -> BiggerWord a (a,a)
  MuchBigger :: (TyC a, TyC b) => BiggerWord a b -> BiggerWord a (b,b)

biggerWord :: BiggerWord a b -> Word b
biggerWord (JustBigger w) = DoubleW w
biggerWord (MuchBigger bw) = DoubleW (biggerWord bw)

doubleBigger :: BiggerWord a b -> BiggerWord (a,a) (b,b)
doubleBigger (JustBigger w) = JustBigger (DoubleW w)
doubleBigger (MuchBigger bw) = MuchBigger (doubleBigger bw)

compareWordSize :: Word a -> Word b -> Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b)
compareWordSize BitW BitW = Right Refl
compareWordSize (DoubleW n) BitW =
  case compareWordSize n BitW of
    Right Refl -> Left (Right (JustBigger BitW))
    Left (Right bw) -> Left (Right (MuchBigger bw))
compareWordSize BitW (DoubleW m) =
  case compareWordSize BitW m of
    Right Refl -> Left (Left (JustBigger BitW))
    Left (Left bw) -> Left (Left (MuchBigger bw))
compareWordSize (DoubleW n) (DoubleW m) =
  case compareWordSize n m of
    Right Refl -> Right Refl
    Left (Left bw) -> Left (Left (doubleBigger bw))
    Left (Right bw) -> Left (Right (doubleBigger bw))

-- | Simplicity expression for a bit shift by a constant amount.
-- 
-- @'shift' w n x@ is a left shift of @n@ bits of the word @x@.
-- The value @n@ can be negative in which case a right shift is performed.
shift :: (Core term, TyC a) => Word a -> Int -> term a a
shift w = subseq w w
 where
  subseq :: (Core term, TyC a, TyC b) => Word a -> Word b -> Int -> term a b
  subseq n m z | z == 0 = subseq0 (compareWordSize n m)
  subseq n m z | wordSize n <= z = zero m
               | z + wordSize m <= 0 = zero m
  subseq (DoubleW n) m           z | wordSize n <= z              = drop (subseq n m (z - wordSize n))
  subseq (DoubleW n) m           z | z + wordSize m <= wordSize n = take (subseq n m z)
  subseq n           (DoubleW m) z = subseq n m z &&& subseq n m (z + wordSize m)

  subseq0 :: (Core term, TyC a) => Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b) -> term a b
  subseq0 (Right Refl) = iden
  subseq0 (Left (Right (JustBigger w))) = take iden
  subseq0 (Left (Right (MuchBigger bw))) = take (subseq0 (Left (Right bw)))
  subseq0 (Left (Left (JustBigger w))) = iden &&& zero w
  subseq0 (Left (Left (MuchBigger bw))) = subseq0 (Left (Left bw)) &&& zero (biggerWord bw)

-- | Simplicity expression for a left bit rotation by a constant amount.
-- 
-- @'rotate' w n x@ is a left rotation of @n@ bits of the word @x@.
-- The value @n@ can be negative in which case a right rotation is performed.
rotate :: (Core term, TyC a) => Word a -> Int -> term a a
rotate w z = subseqWrap w w (z `mod` wordSize w)
 where
   -- Precondition: 0 <= z < wordSize n
   subseqWrap :: (Core term, TyC a, TyC b) => Word a -> Word b -> Int -> term a b
   subseqWrap n m z | z == 0 = subseqWrap0 (compareWordSize n m)
   subseqWrap (DoubleW n) m           z | wordSize n <= z && z + wordSize m <= 2 * wordSize n = drop (subseqWrap n m (z - wordSize n))
   subseqWrap (DoubleW n) m           z | z + wordSize m <= wordSize n                        = take (subseqWrap n m z)
   subseqWrap n           (DoubleW m) z = subseqWrap n m z &&& subseqWrap n m ((z + wordSize m) `mod` wordSize n)

   subseqWrap0 :: (Core term, TyC a) => Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b) -> term a b
   subseqWrap0 (Right Refl) = iden
   subseqWrap0 (Left (Right (JustBigger w))) = take iden
   subseqWrap0 (Left (Right (MuchBigger bw))) = take (subseqWrap0 (Left (Right bw)))
   subseqWrap0 (Left (Left (JustBigger w))) = iden &&& iden
   subseqWrap0 (Left (Left (MuchBigger bw))) = rec &&& rec
    where
     rec = subseqWrap0 (Left (Left bw))
