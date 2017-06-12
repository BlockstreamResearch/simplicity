{-# LANGUAGE GADTs #-}
module Simplicity.Arith
  ( Word(..), wordTy, fromWord
  , Word8, Word16, Word32, word8, word16, word32, fromWord8, fromWord16, fromWord32
  , adder, fullAdder
  , multiplier, fullMultiplier
  ) where

import Simplicity.Bit
import Simplicity.Ty
import Simplicity.Term

import Prelude hiding (Word, drop, take, not, or)

data Word a where
  BitW :: Word Bit
  DoubleW :: Word a -> Word (a,a)

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
adder (DoubleW w) = (take (take iden) &&& drop (take iden))
                &&& (take (drop iden) &&& drop (drop iden) >>> rec)
                >>> (take iden &&& drop (take iden) >>> fa) &&& drop (drop iden)
                >>> take (take iden) &&& (take (drop iden) &&& drop iden)
 where
  rec = adder w
  fa = fullAdder w

fullAdder :: Core term => Word a -> term ((a, a), Bit) (Bit, a)
fullAdder BitW = take add &&& drop iden
             >>> take (take iden) &&& (take (drop iden) &&& drop iden >>> add)
             >>> cond true (take iden) &&& drop (drop iden)
 where
  add = adder BitW
fullAdder (DoubleW w) = take (take (take iden) &&& drop (take iden))
                    &&& (take (take (drop iden) &&& drop (drop iden)) &&& drop iden >>> rec)
                    >>> (take iden &&& drop (take iden) >>> rec) &&& drop (drop iden)
                    >>> take (take iden) &&& (take (drop iden) &&& drop iden)
 where
  rec = fullAdder w

fullMultiplier :: Core term => Word a -> term ((a, a), (a, a)) (a, a)
fullMultiplier BitW = drop iden &&& take (cond iden false)
                  >>> fullAdder BitW
fullMultiplier (DoubleW w) = take ((take (take iden) &&& drop (take iden)) &&& take (drop iden))
                         &&& ((take (take (take iden) &&& drop (drop iden)) &&& drop (take (take iden) &&& drop (take iden)) >>> rec)
                         &&& (take (take (drop iden) &&& drop (drop iden)) &&& drop (take (drop iden) &&& drop (drop iden)) >>> rec))
                         >>> (take (take iden) &&& (take (take (drop iden) &&& drop iden) &&& drop (take (drop iden) &&& drop (take iden)) >>> rec))
                         &&& (drop (take (take iden) &&& drop (drop iden)))
                         >>> (take (take iden) &&& (take (drop (take iden)) &&& drop (take iden)) >>> rec) &&& (take (drop (drop iden)) &&& drop (drop iden))
 where
  rec = fullMultiplier w

multiplier :: Core term => Word a -> term (a, a) (a, a)
multiplier BitW = false &&& cond iden false
multiplier (DoubleW w) = ((take (take iden) &&& drop (take iden)) &&& take (drop iden))
                     &&& ((take (take iden) &&& drop (drop iden) >>> rec)
                     &&& (take (drop iden) &&& drop (drop iden) >>> rec))
                     >>> (take (take iden) &&& (take (take (drop iden) &&& drop iden) &&& drop (take (drop iden) &&& drop (take iden)) >>> fmul))
                     &&& (drop (take (take iden) &&& drop (drop iden)))
                     >>> (take (take iden) &&& (take (drop (take iden)) &&& drop (take iden)) >>> fmul) &&& (take (drop (drop iden)) &&& drop (drop iden))
 where
  rec = multiplier w
  fmul = fullMultiplier w
