{-# LANGUAGE GADTs #-}
-- | This module defines 2^/n/ bit word Simplicity types.
module Simplicity.Ty.Word
  ( Word(..), wordSize, fromWord, toWord
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

import Prelude hiding (Word)

import Control.Monad.Trans.State (State, evalState, get, put)

import Simplicity.Ty
import Simplicity.Ty.Bit

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
