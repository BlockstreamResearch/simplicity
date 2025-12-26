-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Bitcoin.DataTypes".
module Simplicity.Bitcoin.Programs.TimeLock
 ( txIsFinal
 , txLockHeight, txLockTime
 , txLockDistance, txLockDuration
 , checkLockHeight, checkLockTime
 , checkLockDistance, checkLockDuration
 , module Simplicity.Programs.TimeLock
 , Bit
 ) where

import Prelude hiding (Word, all, drop, max, not, take)

import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.Term
import Simplicity.Bitcoin.Programs.Transaction.Lib
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.TimeLock
import Simplicity.Programs.Word

-- | Implements 'Simplicity.Bitcoin.DataTypes.txIsFinal'.
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

-- | Computes the relative height timelock or 0 if there is no such timelock.
txLockDistance :: (Assert term, Primitive term) => term () Distance
txLockDistance = bip68VersionCheck &&& (currentSequence >>> parseSequence)
             >>> cond (copair (unit >>> z) (copair iden (unit >>> z))) (unit >>> z)
 where
  z = zero word16

-- | Computes the relative time timelock or 0 if there is no such timelock.
txLockDuration :: (Assert term, Primitive term) => term () Distance
txLockDuration = bip68VersionCheck &&& (currentSequence >>> parseSequence)
             >>> cond (copair (unit >>> z) (copair (unit >>> z) iden)) (unit >>> z)
 where
  z = zero word16

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
