{-# LANGUAGE GADTs, RankNTypes, TypeOperators #-}

-- | This module defines 2^/n/ bit word Simplicity types.
module Simplicity.Ty.Word
  ( Vector(..), vectorComp, vectorPromote, compareVectorSize
  , vectorSize, vector_
  , Buffer(..), bufferFill, bufferVector, buffer_
  , Word, wordSize, fromWord, toWord
  -- * Type aliases
  -- | Below are type aliases for Simplicity 'Word' types up to 4096-bit words.
  -- Note: This does not limit word sizes; arbitrarily large word sizes are allowed by making further pairs.
  , Word1, Word2, Word4, Word8, Word16, Word32, Word64, Word128, Word256, Word512, Word1024, Word2048, Word4096
  , Vector1, Vector2, Vector4, Vector8, Vector16, Vector32, Vector64, Vector128, Vector256, Vector512, Vector1024, Vector2048, Vector4096
  , vector1, vector2, vector4, vector8, vector16, vector32, vector64, vector128, vector256, vector512, vector1024, vector2048, vector4096
  , Buffer1, Buffer3, Buffer7, Buffer15, Buffer31, Buffer63, Buffer127, Buffer255, Buffer511
  , buffer1, buffer3, buffer7, buffer15, buffer31, buffer63, buffer127, buffer255, buffer511
  -- * Specializations
  -- | The following are useful instances of 'Word' and specializations of 'fromWord' and 'toWord' for commonly used word sizes.
  -- Other word sizes can still be constructed using other 'Word' values.

  -- ** Word1
  , word1, fromWord1, fromInt1, toWord1
  -- ** Word2
  , word2, fromWord2, fromInt2, toWord2
  -- ** Word4
  , word4, fromWord4, fromInt4, toWord4
  -- ** Word8
  , word8, fromWord8, fromInt8, toWord8
  -- ** Word16
  , word16, fromWord16, fromInt16, toWord16
  -- ** Word32
  , word32, fromWord32, fromInt32, toWord32
  -- ** Word64
  , word64, fromWord64, fromInt64, toWord64
  -- ** Word128
  , word128, fromWord128, fromInt128, toWord128
  -- ** Word256
  , word256, fromWord256, fromInt256, toWord256
  -- ** Word512
  , word512, fromWord512, fromInt512, toWord512
  -- ** Word1024
  , word1024, fromWord1024, fromInt1024, toWord1024
  -- ** Word2048
  , word2048, fromWord2048, fromInt2048, toWord2048
  -- ** Word4096
  , word4096, fromWord4096, fromInt4096, toWord4096
  -- * Zip Vector
  , ZipVector(..)
  -- ** Bit
  , module Simplicity.Ty.Bit
  ) where

import Prelude hiding (Word)

import Control.Monad.Trans.State (State, evalState, get, put)
import Data.Type.Equality ((:~:)(Refl))
import Lens.Family2.Stock (Traversal', rgt_)

import Simplicity.Ty
import Simplicity.Ty.Bit

right_ f = rgt_ f

type Vector1 x = x
type Vector2 x = (x,x)
type Vector4 x = Vector2 (Vector2 x)
type Vector8 x = Vector2 (Vector4 x)
type Vector16 x = Vector2 (Vector8 x)
type Vector32 x = Vector2 (Vector16 x)
type Vector64 x = Vector2 (Vector32 x)
type Vector128 x = Vector2 (Vector64 x)
type Vector256 x = Vector2 (Vector128 x)
type Vector512 x = Vector2 (Vector256 x)
type Vector1024 x = Vector2 (Vector512 x)
type Vector2048 x = Vector2 (Vector1024 x)
type Vector4096 x = Vector2 (Vector2048 x)

vector1 :: TyC x => Vector x (Vector1 x)
vector1 = SingleV

vector2 :: TyC x => Vector x (Vector2 x)
vector2 = DoubleV vector1

vector4 :: TyC x => Vector x (Vector4 x)
vector4 = DoubleV vector2

vector8 :: TyC x => Vector x (Vector8 x)
vector8 = DoubleV vector4

vector16 :: TyC x => Vector x (Vector16 x)
vector16 = DoubleV vector8

vector32 :: TyC x => Vector x (Vector32 x)
vector32 = DoubleV vector16

vector64 :: TyC x => Vector x (Vector64 x)
vector64 = DoubleV vector32

vector128 :: TyC x => Vector x (Vector128 x)
vector128 = DoubleV vector64

vector256 :: TyC x => Vector x (Vector256 x)
vector256 = DoubleV vector128

vector512 :: TyC x => Vector x (Vector512 x)
vector512 = DoubleV vector256

vector1024 :: TyC x => Vector x (Vector1024 x)
vector1024 = DoubleV vector512

vector2048 :: TyC x => Vector x (Vector2048 x)
vector2048 = DoubleV vector1024

vector4096 :: TyC x => Vector x (Vector4096 x)
vector4096 = DoubleV vector2048

-- | @'Vector' x a@ specifies types, @a@, which are nested pairs of ... pairs of @x@'s.
--
-- The type @a@ contain 2^/n/ @x@ values for some /n/.
data Vector x a where
  SingleV :: TyC x => Vector x x
  DoubleV :: (TyC x, TyC a) => Vector x a -> Vector x (Vector2 a)

-- | A proof that a 'Vector' of 'Vector's is itself a 'Vector'.
vectorComp :: TyC a => Vector a b -> Vector b c -> Vector a c
vectorComp v SingleV = v
vectorComp v (DoubleV w) = DoubleV (vectorComp v w)

-- | A proof that if @y@ is a 'Vector' of @x@'s then @(y, y)@ is a vector of @(x, x)@'s
vectorPromote :: Vector x y -> Vector (x, x) (y, y)
vectorPromote SingleV = SingleV
vectorPromote (DoubleV v) = DoubleV (vectorPromote v)

-- | Given @a@ and @b@ which are both 'Vector's of @z@'s, then decide which of the two 'Vector's is longer or prove that they are equal.
compareVectorSize :: Vector z a -> Vector z b -> Either (Vector (b, b) a) (Either (a :~: b) (Vector (a, a) b))
compareVectorSize SingleV SingleV = Right (Left Refl)
compareVectorSize (DoubleV n) SingleV =
  case compareVectorSize n SingleV of
    Left v -> Left (DoubleV v)
    Right (Left Refl) -> Left SingleV
compareVectorSize SingleV (DoubleV m) =
  case compareVectorSize SingleV m of
    Right (Left Refl) -> Right (Right SingleV)
    Right (Right v) -> Right (Right (DoubleV v))
compareVectorSize (DoubleV n) (DoubleV m) =
  case compareVectorSize n m of
    Left v -> Left (vectorPromote v)
    Right (Left Refl) -> Right (Left Refl)
    Right (Right v) -> Right (Right (vectorPromote v))

-- | Given a 'Vector', @a@, fill it with values from a list, returning any unused elements.
--
-- Fails if not enough elements are available.
vectorFill :: Vector x a -> [x] -> Maybe (a, [x])
vectorFill SingleV [] = Nothing
vectorFill SingleV (x:xs) = Just (x, xs)
vectorFill (DoubleV vec) l = do
  (v1, l') <- vectorFill vec l
  (v2, l'') <- vectorFill vec l'
  return ((v1,v2),l'')

-- | Computes the number of entries in a 'Vector'.
vectorSize :: Vector x a -> Int
vectorSize SingleV = 1
vectorSize (DoubleV w) = 2*(vectorSize w)

-- | A (monomorphic) traversal of a 'Vector'.
vector_ :: Vector x a -> Traversal' a x
vector_ SingleV = ($)
vector_ (DoubleV v) = \f (x,y) -> (,) <$> rec f x <*> rec f y
 where
  rec = vector_ v

type Buffer1 x = S x
type Buffer3 x = (S (Vector2 x), Buffer1 x)
type Buffer7 x = (S (Vector4 x), Buffer3 x)
type Buffer15 x = (S (Vector8 x), Buffer7 x)
type Buffer31 x = (S (Vector16 x), Buffer15 x)
type Buffer63 x = (S (Vector32 x), Buffer31 x)
type Buffer127 x = (S (Vector64 x), Buffer63 x)
type Buffer255 x = (S (Vector128 x), Buffer127 x)
type Buffer511 x = (S (Vector256 x), Buffer255 x)

-- | @'Buffer' x v b@ specifies a type @b@ which is of the form @('S' (x^(2^/n/)), ..., ('S' x^2, 'S' x)...)@
-- where @x^(2^/n/)@ is a 'Vector' of @x@.
--
-- The type @b@ contains up to, but excluding, 2^/n/ @x@ values for some /n/.
--
-- The type @b@ is isomorphic to @1 + x + x^2 + ... + x^(2^/n/-1)@.
--
-- The type @v@ is a `Vector' of @x@'s which is used as a helper type (see 'bufferVector').
data Buffer x v b where
 SingleB :: TyC x => Buffer x (Vector2 x) (S x)
 DoubleB :: (TyC x, TyC v, TyC b) => Buffer x v b -> Buffer x (Vector2 v) (S v, b)

buffer1 :: TyC x => Buffer x (Vector2 x) (Buffer1 x)
buffer1 = SingleB

buffer3 :: TyC x => Buffer x (Vector4 x) (Buffer3 x)
buffer3 = DoubleB buffer1

buffer7 :: TyC x => Buffer x (Vector8 x) (Buffer7 x)
buffer7 = DoubleB buffer3

buffer15 :: TyC x => Buffer x (Vector16 x) (Buffer15 x)
buffer15 = DoubleB buffer7

buffer31 :: TyC x => Buffer x (Vector32 x) (Buffer31 x)
buffer31 = DoubleB buffer15

buffer63 :: TyC x => Buffer x (Vector64 x) (Buffer63 x)
buffer63 = DoubleB buffer31

buffer127 :: TyC x => Buffer x (Vector128 x) (Buffer127 x)
buffer127 = DoubleB buffer63

buffer255 :: TyC x => Buffer x (Vector256 x) (Buffer255 x)
buffer255 = DoubleB buffer127

buffer511 :: TyC x => Buffer x (Vector512 x) (Buffer511 x)
buffer511 = DoubleB buffer255

-- | Given a 'Buffer', @b@, of up to 2^/n/ @x@'s, return a 'Vector' of 2^/n/ @x@'s.
bufferVector  :: Buffer x v b -> Vector x v
bufferVector SingleB = vector2
bufferVector (DoubleB buf) = DoubleV (bufferVector buf)

-- | Given a 'Buffer', @b@, return the empty buffer for it.
bufferEmpty :: Buffer x v b -> b
bufferEmpty SingleB = Left ()
bufferEmpty (DoubleB buf) = (Left (), bufferEmpty buf)

-- | Given a 'Buffer', @b@, fill it with values from a list, returning any unused elements.
bufferFill :: Buffer x v b -> [x] -> (b,[x])
bufferFill buf [] = (bufferEmpty buf, [])
bufferFill SingleB (x:xs) = (Right x, xs)
bufferFill (DoubleB buf) l = case vectorFill (bufferVector buf) l of
  Nothing -> let (rec,l'') = bufferFill buf l in ((Left (), rec), l'')
  Just (v, l') -> let (rec, l'') = bufferFill buf l' in ((Right v, rec), l'')

-- | A (monomorphic) traversal of a 'Buffer'.
buffer_ :: Buffer x v b -> Traversal' b x
buffer_ SingleB = right_
buffer_ (DoubleB v) = \f (x,y) -> (,) <$> (right_.vector_ (bufferVector v)) f x  <*> buffer_ v f y

type Word1 = Vector1 Bit
type Word2 = Vector2 Bit
type Word4 = Vector4 Bit
type Word8 = Vector8 Bit
type Word16 = Vector16 Bit
type Word32 = Vector32 Bit
type Word64 = Vector64 Bit
type Word128 = Vector128 Bit
type Word256 = Vector256 Bit
type Word512 = Vector512 Bit
type Word1024 = Vector1024 Bit
type Word2048 = Vector2048 Bit
type Word4096 = Vector4096 Bit

-- | @'Word' a@ specifies the types, @a@, which correspond to Simplicity word types.
--
-- These are the types of 2^/n/ bit words and are made up of nested pairs of identically sized words down to the single-'Bit' type.
type Word = Vector Bit

word1 :: Word Word1
word1 = vector1

word2 :: Word Word2
word2 = vector2

word4 :: Word Word4
word4 = vector4

word8 :: Word Word8
word8 = vector8

word16 :: Word Word16
word16 = vector16

word32 :: Word Word32
word32 = vector32

word64 :: Word Word64
word64 = vector64

word128 :: Word Word128
word128 = vector128

word256 :: Word Word256
word256 = vector256

word512 :: Word Word512
word512 = vector512

word1024 :: Word Word1024
word1024 = vector1024

word2048 :: Word Word2048
word2048 = vector2048

word4096 :: Word Word4096
word4096 = vector4096

-- | Computes the number of entries in a 'Word'.
--
-- @'wordSize' w = 'Simplicity.BitMachine.Ty.bitSizeR' ('reifyProxy' w)@
wordSize :: Word a -> Int
wordSize = vectorSize

-- | Covert a value of a Simplicity word type as a unsigned Haskell integer.
--
-- @'toWord' w ('fromWord' w n) = n@
fromWord :: Word a -> a -> Integer
fromWord = fromWordRec 0

fromWordRec :: Integer -> Word a -> a -> Integer
fromWordRec i SingleV (Left ()) = 2 * i
fromWordRec i SingleV (Right ()) = 2 * i + 1
fromWordRec i (DoubleV w) (hi, lo) = fromWordRec (fromWordRec i w hi) w lo

-- | Covert a value of a Simplicity word type as a signed Haskell integer.
--
-- @'toWord' w ('fromInt' w n) = n@
fromInt :: Word a -> a -> Integer
fromInt SingleV (Left ()) = 0
fromInt SingleV (Right ()) = -1
fromInt (DoubleV w) (hi, lo) = fromWordRec (fromInt w hi) w lo

-- | Covert a standard Haskell integer into a Simplicity word type.
-- The value is take modulo 2^@('wordSize' w)@ where @w :: 'Word' a@ is the first argument.
--
-- @'fromWord' w ('toWord' w n) = n \`mod\` 'wordSize' w@
toWord :: Word a -> Integer -> a
toWord w i = evalState (go w) i
 where
  go :: Word a -> State Integer a
  go SingleV = do
   i <- get
   put (i `div` 2)
   return $ toBit (odd i)
  go (DoubleV w) = do
   b <- go w
   a <- go w
   return (a, b)

fromWord1 :: Word1 -> Integer
fromWord1 = fromWord word1

fromWord2 :: Word2 -> Integer
fromWord2 = fromWord word2

fromWord4 :: Word4 -> Integer
fromWord4 = fromWord word4

fromWord8 :: Word8 -> Integer
fromWord8 = fromWord word8

fromWord16 :: Word16 -> Integer
fromWord16 = fromWord word16

fromWord32 :: Word32 -> Integer
fromWord32 = fromWord word32

fromWord64 :: Word64 -> Integer
fromWord64 = fromWord word64

fromWord128 :: Word128 -> Integer
fromWord128 = fromWord word128

fromWord256 :: Word256 -> Integer
fromWord256 = fromWord word256

fromWord512 :: Word512 -> Integer
fromWord512 = fromWord word512

fromWord1024 :: Word1024 -> Integer
fromWord1024 = fromWord word1024

fromWord2048 :: Word2048 -> Integer
fromWord2048 = fromWord word2048

fromWord4096 :: Word4096 -> Integer
fromWord4096 = fromWord word4096

fromInt1 :: Word1 -> Integer
fromInt1 = fromInt word1

fromInt2 :: Word2 -> Integer
fromInt2 = fromInt word2

fromInt4 :: Word4 -> Integer
fromInt4 = fromInt word4

fromInt8 :: Word8 -> Integer
fromInt8 = fromInt word8

fromInt16 :: Word16 -> Integer
fromInt16 = fromInt word16

fromInt32 :: Word32 -> Integer
fromInt32 = fromInt word32

fromInt64 :: Word64 -> Integer
fromInt64 = fromInt word64

fromInt128 :: Word128 -> Integer
fromInt128 = fromInt word128

fromInt256 :: Word256 -> Integer
fromInt256 = fromInt word256

fromInt512 :: Word512 -> Integer
fromInt512 = fromInt word512

fromInt1024 :: Word1024 -> Integer
fromInt1024 = fromInt word1024

fromInt2048 :: Word2048 -> Integer
fromInt2048 = fromInt word2048

fromInt4096 :: Word4096 -> Integer
fromInt4096 = fromInt word4096

toWord1 :: Integer -> Word1
toWord1 = toWord word1

toWord2 :: Integer -> Word2
toWord2 = toWord word2

toWord4 :: Integer -> Word4
toWord4 = toWord word4

toWord8 :: Integer -> Word8
toWord8 = toWord word8

toWord16 :: Integer -> Word16
toWord16 = toWord word16

toWord32 :: Integer -> Word32
toWord32 = toWord word32

toWord64 :: Integer -> Word64
toWord64 = toWord word64

toWord128 :: Integer -> Word128
toWord128 = toWord word128

toWord256 :: Integer -> Word256
toWord256 = toWord word256

toWord512 :: Integer -> Word512
toWord512 = toWord word512

toWord1024 :: Integer -> Word1024
toWord1024 = toWord word1024

toWord2048 :: Integer -> Word2048
toWord2048 = toWord word2048

toWord4096 :: Integer -> Word4096
toWord4096 = toWord word4096

-- | A pair of 'Vector's of the same length that have different contents.
data ZipVector x a y b where
  SingleZV :: (TyC x, TyC y) => ZipVector x x y y
  DoubleZV :: (TyC x, TyC a, TyC y, TyC b) => ZipVector x a y b -> ZipVector x (Vector2 a) y (Vector2 b)
