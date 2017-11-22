{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
module Simplicity.Programs.Word
  ( Word(..), wordTy, fromWord, toWord
  , Word8, word8, fromWord8, toWord8
  , Word16, word16, fromWord16, toWord16
  , Word32, word32, fromWord32, toWord32
  , Word64, word64, fromWord64, toWord64
  , Word256, word256, fromWord256, toWord256
  , zero
  , adder, fullAdder
  , multiplier, fullMultiplier
  , shift, rotate
  , bitwise, bitwiseTri
  ) where

import Prelude hiding (Word, drop, take, not, or)

import Control.Monad.Trans.State (State, evalState, get, put)
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Term
import Simplicity.Programs.Bit

data Word a where
  BitW :: Word Bit
  DoubleW :: TyC a => Word a -> Word (a,a)

word8 = DoubleW . DoubleW . DoubleW $ BitW
word16 = DoubleW word8
word32 = DoubleW word16
word64 = DoubleW word32
word128 = DoubleW word64
word256 = DoubleW word128

wordTy :: Word a -> TyReflect a
wordTy BitW = SumR OneR OneR
wordTy (DoubleW w) = ProdR rec rec
 where
  rec = wordTy w

-- wordSize w = bitSizeR (wordTy w)
wordSize :: Word a -> Int
wordSize BitW = 1
wordSize (DoubleW w) = 2*(wordSize w)

fromWord :: Word a -> a -> Integer
fromWord = go 0
 where
  go :: Integer -> Word a -> a -> Integer
  go i BitW (Left ()) = 2 * i
  go i BitW (Right ()) = 2 * i + 1
  go i (DoubleW w) (hi, lo) = go (go i w hi) w lo

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

zero :: (Core term, TyC a) => Word b -> term a b
zero BitW = false
zero (DoubleW w) = rec &&& rec
 where
  rec = zero w

adder :: Core term => Word a -> term (a, a) (Bit, a)
adder BitW = cond (iden &&& not iden) (false &&& iden)
adder (DoubleW w) = (ooh &&& ioh) &&& (oih &&& iih >>> rec)
                >>> iih &&& (oh &&& ioh >>> fa)
                >>> ioh &&& (iih &&& oh)
 where
  rec = adder w
  fa = fullAdder w

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

bitwise :: forall term a. Core term => term (Bit, Bit) Bit -> Word a -> term (a, a) a
bitwise op = go
 where
  go :: forall a. Word a -> term (a, a) a
  go BitW = op
  go (DoubleW w) = (ooh &&& ioh >>> rec) &&& (oih &&& iih >>> rec)
   where
    rec = go w

bitwiseTri :: forall term a. Core term => term (Bit, (Bit, Bit)) Bit -> Word a -> term (a, (a, a)) a
bitwiseTri op = go
 where
  go :: forall a. Word a -> term (a, (a, a)) a
  go BitW = op
  go (DoubleW w) = (ooh &&& (iooh &&& iioh) >>> rec)
               &&& (oih &&& (ioih &&& iiih) >>> rec)
   where
    rec = go w

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

-- shifts left on a positive amount and shifts right on a negative amount.
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

-- rotates left on a positive amount and rotates right on a negative amount.
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
