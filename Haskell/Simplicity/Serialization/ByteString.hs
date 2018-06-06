-- | This modules provides a byte-stream serialization and deserialization functions for 'UntypedSimplicityDag's.
module Simplicity.Serialization.ByteString
  ( getDag
  ) where

import Control.Monad (unless)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State (StateT, runStateT)
import qualified Control.Monad.Trans.State as MS
import Data.Bits ((.&.), testBit)
import Data.ByteString.Short (ShortByteString)
import Data.Serialize (Get, get)
import Data.Serialize.Get (getWord8, getWord16be, getShortByteString)
import Data.Vector (Vector, unfoldrM, foldM)
import qualified Data.Vector.Unboxed as UV
import qualified Data.Word as W
import Lens.Family2.Stock (_1)

import Simplicity.Digest
import Simplicity.Elaboration
import Simplicity.Primitive
import Simplicity.Serialization

-- Decodes a bit-string of given length from a byte-stream.
getBoolVector :: Int -> Get (UV.Vector Bool)
getBoolVector i = getEvalBitStream prog
 where
  prog _abort next = UV.replicateM i next

-- Decodes a single node for a 'UntypedSimplicityDag'.
-- The first byte is given as an argument, but if needed, more bytes may be consumed from the stream.
decodeNode :: W.Word8 -> Get (UntypedTermF Bool)
decodeNode 0x20 = return uIden
decodeNode 0x21 = return uUnit
decodeNode 0x23 = uHidden <$> get
decodeNode 0xff = do
  len <- fromIntegral <$> getWord16be
  unless (127 <= len) (fail "Simplicity.Serialization.ByteString.decodeNode: Badly coded long witness length.")
  uWitness <$> getBoolVector len
decodeNode w | w .&. 0xf7 == 0x10 = return (uInjl (testBit w 3))
             | w .&. 0xf7 == 0x11 = return (uInjr (testBit w 3))
             | w .&. 0xf7 == 0x12 = return (uTake (testBit w 3))
             | w .&. 0xf7 == 0x13 = return (uDrop (testBit w 3))
             | w .&. 0xf3 == 0x00 = return (uComp (testBit w 3) (testBit w 2))
             | w .&. 0xf3 == 0x01 = return (uCase (testBit w 3) (testBit w 2))
             | w .&. 0xf3 == 0x02 = return (uPair (testBit w 3) (testBit w 2))
             | w .&. 0xf3 == 0x03 = return (uDisconnect (testBit w 3) (testBit w 2))
             | w .&. 0x80 == 0x80 = do
  let len = fromIntegral (w .&. 0x7f)
  uWitness <$> getBoolVector len
             | w .&. 0x20 == 0x20 = getPrimByte w >>= go
   where
    go (Just p) = return (uPrim p)
    go Nothing = fail $ "Simplicity.Serialization.ByteString.decodeNode: Unknown primtiive #"++show w++"."

-- The 'DeserializeM' monad adds a counter to the 'Get' monad to count the number of nodes deserialized.
-- This is used to compute the offsets of references.
type DeserializeM a = StateT Integer Get a

-- Decodes a node references (a.k.a. indices) for a 'UntypedSimplicityDag'.
-- The input flag set to 'False' means to return the last index, which is offset 0.
-- The input flag set to 'True' means to parse the reference from the stream.
-- In this case we add 1 to the decoded value to get the relative offset since a relative offset of 0 is handled by the input flag set to 'False'.
getIx :: Bool -> DeserializeM Integer
getIx False = return 0
getIx True = do
  cnt <- MS.get
  ix <- lift (getSizedInteger (cnt - 1))
  unless (ix < cnt) (fail "getIx: index out of range")
  return (ix + 1)
 where
  getSizedInteger bound | bound <= 0 = return 0
                        | otherwise = do
    hi <- getSizedInteger (bound `div` 256)
    lo <- getWord8
    return (hi * 256 + fromIntegral lo)

-- Decodes a single node and references for a 'UntypedSimplicityDag'.
-- 'Nothing' is returned when then end-of-stream code is encountered.
getNode :: DeserializeM (Maybe (UntypedTermF Integer))
getNode = do
  w <- lift getWord8
  case w of
   0x1f -> return Nothing
   _    -> do
     bNode <- lift (decodeNode w)
     Just <$> traverse getIx bNode

-- | Decodes a self-delimiting byte-stream encoding of 'UntypedSimplicityDag'.
getDag :: Get UntypedSimplicityDag
getDag = unfoldrM (fmap strength . runStateT getNode) 0
 where
  strength = _1 id
