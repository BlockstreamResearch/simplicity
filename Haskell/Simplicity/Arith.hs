{-# LANGUAGE GADTs #-}
module Simplicity.Arith
  ( Word(..), wordTy
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

wordTy :: Word a -> TyReflect a
wordTy BitW = SumR OneR OneR
wordTy (DoubleW w) = ProdR rec rec
 where
  rec = wordTy w

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
