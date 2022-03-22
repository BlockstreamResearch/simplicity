-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Bitcoin".
module Simplicity.Programs.TimeLock
 ( parseLock, parseSequence
 , Height, Time, Distance, Duration
 ) where

import Prelude hiding (Word, drop, not, subtract, take)

import Simplicity.Functor
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Arith
import Simplicity.Programs.Word
import Simplicity.Term.Core

type Height = Word32
type Time = Word32
type Distance = Word16
type Duration = Word16

-- | Implements 'Simplicity.Bitcoin.parseLock'.
parseLock :: Core term => term Word32 (Either Height Time)
parseLock = (iden &&& scribe (toWord32  500000000) >>> subtract word32 >>> oh) &&& iden
        >>> cond (injl iden) (injr iden)

-- | Implements 'Simplicity.Bitcoin.parseSequence'.
parseSequence :: Core term => term Word32 (Either () (Either Distance Duration))
parseSequence = bit31 &&& (bit22 &&& ih)
            >>> cond (injl unit)
                     (injr (cond (injr iden) (injl iden)))
 where
  bit31  = take (take oooh)
  bit22 = take (drop ooih)
