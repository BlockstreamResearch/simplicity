-- | This modules provides functionality to aid serializiang and deserializing to and from bit streams using difference lists and Van Laarhoven free monad representations.
module Simplicity.Serialization
  ( DList, putBitString, putPositive
  , getBitString, getPositive, getPositiveUpTo
  , getItem
  , getCatalogue
  , evalStream, evalExactVector
  , evalStreamWithError
  , Error(..)
  , getEvalBitStream, treeEvalBitStream
  , putBitStream
  ) where

import Prelude hiding (length)

import Control.Monad (forM_, guard)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (Cont, cont, runCont)
import Control.Monad.Trans.State (StateT(..), evalStateT, get, put)
import Data.Bits (setBit, testBit)
import Data.List (foldl', genericLength, unfoldr)
import Data.List.Split (chunksOf)
import Data.Serialize.Get (Get, getWord8)
import Data.Serialize.Put (Putter, putWord8)
import Data.Vector.Unboxed (Vector, Unbox, indexM, length)
import Data.Void (Void, vacuous)
import Data.Word (Word8)

import Simplicity.Tree

-- | A type for difference lists: an efficent type for appending to lists.
--
-- To convert a difference list, @l :: DList a@, to a list, apply it to the empty list, @l [] :: [a]@.
-- To convert a list, @l :: [a]@, to a difference list, partially apply it to the append funciton, @(l++) :: DList a@.
type DList a = [a] -> [a]

-- | A self-delimiting encoding of variable length list of bits returned as a difference list.
--
-- The empty list, @[]@, is encoded as the difference list representing @[False]@.
-- A non-empty list, @l@, is encoded as the difference list representing @[True] ++ n ++ l@,
-- where @n@ is the length of @l@ encoded by 'putPositive'.
putBitString :: [Bool] -> DList Bool
putBitString [] = (False :)
putBitString l = (True :) . putPositive (genericLength l) . (l ++)

-- | A self-delimiting encoding of arbitrary sized positive integers.
--
-- A positive number is encoded by writing it base-2, choping off the leading '1',
-- and encoding the remaining digits as a list of Booleans in big-endian using 'putBitString'.
-- e.g.
--
-- @putPositive 1 = putBitString []@
--
-- @putPositive 2 = putBitString [False]@
--
-- @putPositive 3 = putBitString [True]@
--
-- @putPositive 4 = putBitString [False,False]@
--
-- @putPositive 5 = putBitString [False,True]@
putPositive :: Integer -> DList Bool
putPositive = putBitString . reverse . unfoldr f
 where
  f i | i <= 1 = Nothing
      | otherwise = Just (odd i, i `div` 2)

-- | Decodes the self-delimiting encoding of a variable length list of bits.
--
-- Note that the type @forall m. Monad m => m Bool -> m a@ is isomorphic to the free monad over the @X²@ functor.
-- In other words, 'getBitString' has the type of a binary branching tree with leaves containing '[Bool]' values.
--
-- @evalStream getBitString (putBitString l) == Just l@
getBitString :: Monad m => m Bool -> m [Bool]
getBitString next = next >>= f
 where
  f False = return []
  f True = getPositive next >>= loop
  loop i | i <= 0 = return []
         | otherwise = (:) <$> next <*> loop (i-1)

-- | Decodes the self-delimiting encoding of a positive integer.
--
-- Note that the type @forall m. Monad m => m Bool -> m a@ is isomorphic to the free monad over the @X²@ functor.
-- In other words, 'getPositive' has the type of a binary branching tree with leaves containing 'Integer' values.
--
-- @evalStream getPositive (putPositive n) == Just n@
getPositive :: Monad m => m Bool -> m Integer
getPositive = fmap (foldl' f 1) . getBitString
 where
  f i False = 2*i
  f i True  = 2*i + 1

-- | Decodes the self-delimiting encoding of a positive integer that is less than or equal to a given bound.
--
-- If the encoded value exceeds the bound, then nothing is returned.
--
-- Note that the type @forall m. Monad m => m void -> m b -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@.
-- In other words, 'getPositiveUpTo' returns the type of a binary branching tree with leaves containing 'Integer' values or nothing.
getPositiveUpTo :: Monad m => Integer -> m Void -> m Bool -> m Integer
getPositiveUpTo bound abort | 0 < bound = getUpTo (putPositive bound []) (\abort_ -> getPositive) abort
                            | otherwise = \next_ -> vacuous abort
 where
  getUpTo :: Monad m => [Bool] -> (StateT [Bool] m Void -> StateT [Bool] m Bool -> StateT [Bool] m a) -> m Void -> m Bool -> m a
  getUpTo bound prog abort next = evalStateT (prog (lift abort) (StateT boundNext)) bound
   where
    boundNext [] = vacuous abort
    boundNext (hd:tl) = next >>= k
     where
      k b | b <= hd = return (b, if b == hd then tl else repeat True)
          | otherwise = vacuous abort

-- | Decodes the self-delimiting encoding of a positive integer that repesents an item in a list.
--
-- If the encoded value exceeds the length of the list, then nothing is returned.
--
-- Note: Because only positive integers have an encoding, the indexing into the list is 1-based rather than the usual 0-based.
--
-- Note that the type @forall m. Monad m => m void -> m b -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@.
-- In other words, 'getItem' returns the type of a binary branching tree with leaves containing 'a' values or nothing.
getItem :: Monad m => [a] -> m Void -> m Bool -> m a
getItem items abort next = select <$> getPositiveUpTo (genericLength items) abort next
 where
  select n = items !! fromInteger (n - 1)

-- | Decodes the self-delimiting encoding of a sequence of positive integers that repesents an item in a 'Catalogue'.
-- Guided by the 'Catalogue' the 'getItem' decods a positive integer to select an item from a 'Shelf'.
-- If that item is another 'Catalogue', then it recursively decodes another positive integer, otherwise it returns the 'Item' from the 'Shelf'.
--
-- If an encoded value exceeds the length of any shelf list, then nothing is returned.
--
-- If an encoded value references a 'Missing' item, then nothing is returned.
--
-- Note: Because only positive integers have an encoding, the indexing into a 'Shelf' is 1-based rather than the usual 0-based.
--
-- Note that the type @forall m. Monad m => m void -> m b -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@.
-- In other words, 'getCatalogue' returns the type of a binary branching tree with leaves containing 'a' values or nothing.
getCatalogue :: Monad m => Catalogue a -> m Void -> m Bool -> m a
getCatalogue Missing abort next = vacuous abort
getCatalogue (Item a) abort next = return a
getCatalogue (Shelf shelf) abort next = do
  item <- getItem shelf abort next
  getCatalogue item abort next

-- | @evalStream :: (forall m. Monad m => m b -> m a) -> [b] -> Maybe a@
--
-- Interprets the free monad representation of a stream transformer as a function consuming lists.
-- 'evalStream' returns 'Nothing' if the stream transforms consumes the entire input before returning a value.
--
-- Note that the type @forall m. Monad m => m b -> m a@ is isomorphic to the free monad over the @X^b@ functor at @a@.
-- In other words, 'evalStream' transforms a type of @b@-branching trees with leaves containing @a@ values
-- into a function consuming a list of @b@s and returning a @Maybe a@.
evalStream :: (StateT [b] Maybe b -> StateT [b] Maybe a) -> [b] -> Maybe a
evalStream prog = evalStateT (prog (get >>= f))
 where
  f [] = fail "Simplicity.Serialization.evalStream: End of Stream"
  f (hd:tl) = put tl >> return hd

-- | @evalExactVector :: Unboxed b => (forall m. Monad m => m b -> m a) -> 'Vector' b -> Maybe a@
--
-- Interprets the free monad representation of a stream transformer as a function consuming unboxed 'Vector's.
-- 'evalExactVector' returns 'Nothing' unless the input vector is entirely and exactly consumed.
--
-- Note that the type @forall m. Monad m => m b -> m a@ is isomorphic to the free monad over the @X^b@ functor at @a@.
-- In other words, 'evalExactVector' transforms a type of @b@-branching trees with leaves containing @a@ values
-- into a function consuming a 'Vector' of @b@s and returning a @Maybe a@.
evalExactVector :: Unbox b => (StateT Int Maybe b -> StateT Int Maybe a) -> Vector b -> Maybe a
evalExactVector prog bs = evalStateT (prog next >>= assertEnd) 0
 where
  n = length bs
  next = do
   i <- get
   guard (i < n)
   put (i + 1)
   indexM bs i
  assertEnd result = do
    i <- get
    guard (i == n)
    return result

-- | The type of errors that can be produced by 'evalStreamWithError'.
data Error = EndOfInput
           | ParseError
           deriving (Eq, Show)

-- | @evalStreamWithError :: (forall m. Monad m => m void -> m b -> m a) -> [b] -> 'Either' 'Error' a@
--
-- Interprets the free monad representation of a partial stream transformer as a function consuming lists.
-- 'evalStreamWithError' returns @'Left' 'EndOfInput'@ if the stream transforms consumes the entire input before returning a value and
-- @'Left' 'ParseError'@ if the stream transforms aborts.
--
-- Note that the type @forall m. Monad m => m void -> m b -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@.
-- In other words, 'evalStreamWithError' transforms a type of @b@-branching trees with leaves either containing @a@ values or no values
-- into a function consuming a list of @b@s and returning an @'Either' 'Error' a@.
evalStreamWithError :: (StateT [b] (Either Error) void ->
                        StateT [b] (Either Error) b ->
                        StateT [b] (Either Error) a)
                    -> [b] -> Either Error a
evalStreamWithError prog = evalStateT (prog abort (get >>= f))
 where
  abort = lift (Left ParseError)
  f [] = lift (Left EndOfInput)
  f (hd:tl) = put tl >> return hd

-- | @getEvalBitStream :: (forall m. Monad m => m void -> m Bool -> m a) -> Get a@
--
-- Interprets the free monad representaiton of a bit-stream transformer with failure in the 'Get' monad.
-- This consumes bits from a 'ByteString' in big-endian order.
-- Any unconsumed bits from the last byte processed are discarded.
-- If the provided bit-stream transformer fails, then 'Control.Monad.fail' is called for the 'Get' monad.
--
-- Note that the type @forall m. Monad m => m void -> m b -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@.
getEvalBitStream :: (StateT (Maybe (Word8, Int)) Get void -> StateT (Maybe (Word8, Int)) Get Bool -> StateT (Maybe (Word8, Int)) Get a) -> Get a
getEvalBitStream prog = evalStateT (prog (fail "Simplicity.Serialization.getEvalBitStream: aborted") (StateT next)) Nothing
 where
  next Nothing = do
   w <- getWord8
   return (testBit w 7, Just (w, 6))
  next (Just (w, i)) | i < 0     = next Nothing
                     | otherwise = return (testBit w i, Just (w, i-1))

-- Cont is a poor-man's Codensity Monad.
-- | @treeEvalBitStream :: (forall m. Monad m => m void -> m Bool -> m a) -> BinTree a@
--
-- Reifies the free monad represenation of a bit-stream transformer with failure as a 'BinTree'.
--
-- Note that the type @forall m. Monad m => m void -> m Bool -> m a@ is isomorphic to the free monad over the @X^b + 1@ functor at @a@,
-- which is the 'BinTree a' type.
treeEvalBitStream :: (Cont (BinTree a) void -> Cont (BinTree a) Bool -> Cont (BinTree a) a) -> BinTree a
treeEvalBitStream prog = runCont (prog abort next) Leaf
 where
   abort = cont $ const Dead
   next = cont $ \k -> branch (k False) (k True)

-- | Packs and writes out a list of 'Bool's via the 'Data.Serialize.Put.Put' monad.
-- It writes starting from MSB (most sigificant bit) to LSB (least sigificant bit) within a byte.
putBitStream :: Putter [Bool]
putBitStream l = forM_ (chunksOf 8 l) putChunk
 where
  putChunk bs = putWord8 $ foldr (flip setBit) 0 [i|(b, i) <- zip bs [7,6..0], b]
