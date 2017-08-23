{-# LANGUAGE GADTs #-}
module Simplicity.Arith
  ( Word(..), wordTy, fromWord
  , Word8, Word16, Word32, word8, word16, word32, fromWord8, fromWord16, fromWord32
  , adder, fullAdder
  , multiplier, fullMultiplier
  ) where

import Simplicity.Bit
import Simplicity.Term

import Prelude hiding (Word, drop, take, not, or)

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

fromWord :: Word a -> a -> Integer
fromWord = go 0
 where
  go :: Integer -> Word a -> a -> Integer
  go i BitW (Left ()) = 2 * i
  go i BitW (Right ()) = 2 * i + 1
  go i (DoubleW w) (hi, lo) = go (go i w hi) w lo

type Word2 = (Bit, Bit)
type Word4 = (Word2, Word2)
type Word8 = (Word4, Word4)
type Word16 = (Word8, Word8)
type Word32 = (Word16, Word16)

fromWord8 :: Word8 -> Integer
fromWord16 :: Word16 -> Integer
fromWord32 :: Word32 -> Integer
fromWord8 = fromWord word8
fromWord16 = fromWord word16
fromWord32 = fromWord word32

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
