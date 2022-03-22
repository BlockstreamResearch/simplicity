-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.TimeLock
 ( txIsFinal
 , txLockHeight, txLockTime
 , txLockDistance, txLockDuration
 , checkLockHeight, checkLockTime
 , checkLockDistance, checkLockDuration
 , module Simplicity.Programs.TimeLock
 , Bit
 ) where

import Prelude hiding (Word, all, drop, max, not, take)

import Simplicity.Elements.Primitive
import Simplicity.Elements.Term
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.TimeLock
import Simplicity.Programs.Word

-- | Implements 'Simplicity.Elements.DataTypes.txIsFinal'.
txIsFinal :: (Core term, Primitive term) => term () Bit
txIsFinal = (unit &&& unit) >>> forWhile word32 body >>> copair iden true
 where
  body = take (drop (primitive InputSequence)) >>> copair (injl true) (all word32 >>> copair (injl false) (injr unit))

-- | Returns the transaction's LockTime if it is a Height value, otherwise it returns 0.
txLockHeight :: (Core term, Primitive term) => term () Height
txLockHeight = txIsFinal &&& primitive LockTime
           >>> cond z (parseLock >>> (copair iden z))
 where
  z = unit >>> zero word32

-- | Returns the transaction's LockTime if it is a Time value, otherwise it returns 0.
txLockTime :: (Core term, Primitive term) => term () Time
txLockTime = txIsFinal &&& primitive LockTime
         >>> cond z (parseLock >>> (copair z iden))
 where
  z = unit >>> zero word32

bip68VersionCheck :: (Core term, Primitive term) => term () Bit
bip68VersionCheck = scribe (toWord32 2) &&& primitive Version >>> le word32

-- | Implements 'Simplicity.Elements.DataTypes.txLockDistance'.
txLockDistance :: (Core term, Primitive term) => term () Distance
txLockDistance = bip68VersionCheck &&& zero word16
             >>> match ih (forWhile word32 body >>> copair iden iden)
 where
  body = take (drop (primitive InputSequence)) &&& ih
     >>> match (injl ih) (injr (take parseSequence &&& ih >>> match ih (match (max word16) ih)))

-- | Implements 'Simplicity.Elements.DataTypes.txLockDuration'.
txLockDuration :: (Core term, Primitive term) => term () Duration
txLockDuration = bip68VersionCheck &&& zero word16
             >>> match ih (forWhile word32 body >>> copair iden iden)
 where
  body = take (drop (primitive InputSequence)) &&& ih
     >>> match (injl ih) (injr (take parseSequence &&& ih >>> match ih (match ih (max word16))))

-- | Asserts that the input is less than or equal to the value returned by 'txLockHeight'.
checkLockHeight :: (Assert term, Primitive term) => term Height ()
checkLockHeight = assert (iden &&& (unit >>> txLockHeight) >>> le word32)

-- | Asserts that the input is less than or equal to the value returned by 'txLockTime'.
checkLockTime :: (Assert term, Primitive term) => term Time ()
checkLockTime = assert (iden &&& (unit >>> txLockTime) >>> le word32)

-- | Asserts that the input is less than or equal to the value returned by 'txLockDistance'.
checkLockDistance :: (Assert term, Primitive term) => term Distance ()
checkLockDistance = assert (iden &&& (unit >>> txLockDistance) >>> le word16)

-- | Asserts that the input is less than or equal to the value returned by 'txLockDuration'.
checkLockDuration :: (Assert term, Primitive term) => term Duration ()
checkLockDuration = assert (iden &&& (unit >>> txLockDuration) >>> le word16)
