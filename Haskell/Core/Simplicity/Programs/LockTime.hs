module Simplicity.Programs.LockTime
 ( parseLock, parseSequence
 , Height, Time
 , RelHeight, Duration
 ) where

import Prelude hiding (Word, drop, not, take)

import Simplicity.Functor
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import Simplicity.Term.Core

type Height = Word32
type Time = Word32
type RelHeight = Word16
type Duration = Word32

parseLock :: Core term => term Word32 (Either Height Time)
parseLock = (iden &&& scribe (toWord32  500000000) >>> subtractor word32 >>> oh) &&& iden
        >>> cond (injl iden) (injr iden)

parseSequence :: Core term => term Word32 (Either () (Either RelHeight Duration))
parseSequence = bit31 &&& (bit22 &&& ih)
            >>> cond (injl unit)
                     (injr (cond (injl iden) (injr (zero word16 &&& iden >>> shift word32 (-9)))))
 where
  bit31  = take (take oooh)
  bit22 = take (drop ooih)
