{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines 2^/n/ bit word Simplicity types and some associated Simplicity expressions and combinators that operate on them.
module Simplicity.Programs.Word
  ( Word(..), wordSize, fromWord, toWord
  -- * Arithmetic
  , zero
  , adder, fullAdder, multiplier, fullMultiplier
  -- * Bit-wise operations
  , shift, rotate
  , bitwise, bitwiseTri
  -- * Type aliases
  -- | Below are type aliases for Simplicity 'Word' types upto 256-bit words.
  -- Note: This does not limit word sizes; arbitrarily large word sizes are allowed by making further pairs.
  , Word2, Word4, Word8, Word16, Word32, Word64, Word128, Word256
  -- * Specializations
  -- | The following are useful instances of 'Word' and specializations of 'fromWord' and 'toWord' for commonly used word sizes.
  -- Other word sizes can still be constructed using other 'Word' values.
  -- ** Word8
  , word8, fromWord8, toWord8
  -- ** Word16
  , word16, fromWord16, toWord16
  -- ** Word32
  , word32, fromWord32, toWord32
  -- ** Word64
  , word64, fromWord64, toWord64
  -- ** Word256
  , word256, fromWord256, toWord256
  ) where

import Prelude hiding (Word, drop, take, not, or)

import Control.Monad.Trans.State (State, evalState, get, put)
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Term
import Simplicity.Programs.Bit

-- | The 'Word' GADT specifies which types correspond to Simplicity word types.
--
-- These are the types of 2^/n/ bit words and are made up of nested pairs of identically sized words down to the single-'Bit' word type.
data Word a where
  -- | A single bit 'Word'.
  BitW :: Word Bit 
  -- | A pair of identically sized 'Word's is the next larger 'Word'.
  DoubleW :: TyC a => Word a -> Word (a,a)

word8 :: Word Word8
word8 = DoubleW . DoubleW . DoubleW $ BitW

word16 :: Word Word16
word16 = DoubleW word8

word32 :: Word Word32
word32 = DoubleW word16

word64 :: Word Word64
word64 = DoubleW word32

word128 :: Word Word128
word128 = DoubleW word64

word256 :: Word Word256
word256 = DoubleW word128

-- | Computes the number of bits of the 'Word' 'a'.
--
-- @'wordSize' w = 'Simplicity.BitMachine.Ty.bitSizeR' ('reifyProxy' w)@
wordSize :: Word a -> Int
wordSize BitW = 1
wordSize (DoubleW w) = 2*(wordSize w)

-- | Covert a value of a Simplicity word type into a standard Haskell integer.
--
-- @'toWord' w ('fromWord' w n) = n@
fromWord :: Word a -> a -> Integer
fromWord = go 0
 where
  go :: Integer -> Word a -> a -> Integer
  go i BitW (Left ()) = 2 * i
  go i BitW (Right ()) = 2 * i + 1
  go i (DoubleW w) (hi, lo) = go (go i w hi) w lo

-- | Covert a standard Haskell integer into a Simplicity word type.
-- The value is take modulo 2^@('wordSize' w)@ where @w :: 'Word' a@ is the first argument.
--
-- @'fromWord' w ('toWord' w n) = n \`mod\` 'wordSize' w@
toWord :: Word a -> Integer -> a
toWord w i = evalState (go w) i
 where
  go :: Word a -> State Integer a
  go BitW = do
   i <- get
   put (i `div` 2)
   return $ toBit (odd i)
  go (DoubleW w) = do
   b <- go w
   a <- go w
   return (a, b)

type Word2 = (Bit, Bit)
type Word4 = (Word2, Word2)
type Word8 = (Word4, Word4)
type Word16 = (Word8, Word8)
type Word32 = (Word16, Word16)
type Word64 = (Word32, Word32)
type Word128 = (Word64, Word64)
type Word256 = (Word128, Word128)

fromWord8 :: Word8 -> Integer
fromWord8 = fromWord word8

fromWord16 :: Word16 -> Integer
fromWord16 = fromWord word16

fromWord32 :: Word32 -> Integer
fromWord32 = fromWord word32

fromWord64 :: Word64 -> Integer
fromWord64 = fromWord word64

fromWord256 :: Word256 -> Integer
fromWord256 = fromWord word256

toWord8 :: Integer -> Word8
toWord8 = toWord word8

toWord16 :: Integer -> Word16
toWord16 = toWord word16

toWord32 :: Integer -> Word32
toWord32 = toWord word32

toWord64 :: Integer -> Word64
toWord64 = toWord word64

toWord256 :: Integer -> Word256
toWord256 = toWord word256

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
