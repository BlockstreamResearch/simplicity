module Simplicity.Bitcoin.Programs.LockTime
 ( getAbsoluteHeightLockIx, getAbsoluteTimeLockIx
 , getRelativeHeightLockIx, getRelativeTimeLockIx
 , module Simplicity.Programs.LockTime
 ) where

import Prelude hiding (Word, drop, not, take)

import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.Term
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.LockTime
import Simplicity.Programs.Word

type Index = Word32

getAbsoluteHeightLockIx :: (Core term, Primitive term) => term Index (Either () Height)
getAbsoluteHeightLockIx = primitive InputSequence
                      >>> bindR (not (iden &&& scribe (toWord32 0xFFFFFFFF) >>> eq))
                      >>> bindR (primitive LockTime >>> parseLock >>> injr iden ||| injl unit)

getAbsoluteTimeLockIx :: (Core term, Primitive term) => term Index (Either () Time)
getAbsoluteTimeLockIx = primitive InputSequence
                      >>> bindR (not (iden &&& scribe (toWord32 0xFFFFFFFF) >>> eq))
                      >>> bindR (primitive LockTime >>> parseLock >>> injl unit ||| injr iden)

getRelativeHeightLockIx :: (Core term, Primitive term) => term Index (Either () RelHeight)
getRelativeHeightLockIx = (unit >>> primitive Version &&& scribe (toWord32 2) >>> subtractor word32 >>> oh) &&& primitive InputSequence
                      >>> cond (injl unit)
                               (bindR parseSequence
                            >>> bindR (injr iden ||| injl unit))

getRelativeTimeLockIx :: (Core term, Primitive term) => term Index (Either () Duration)
getRelativeTimeLockIx = (unit >>> primitive Version &&& scribe (toWord32 2) >>> subtractor word32 >>> oh) &&& primitive InputSequence
                    >>> cond (injl unit)
                             (bindR parseSequence
                          >>> bindR (injl unit ||| injr iden))
