-- | This modules provides serialization and deserialization functions for 'UntypedSimplicityDag's via ceral's "Data.Serialize" library.
module Simplicity.Serialization.ByteString
  ( getDag, putDag
  ) where

import Control.Monad (unless)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State (StateT, runStateT)
import qualified Control.Monad.Trans.State as MS
import Data.Bits ((.|.), (.&.), testBit, setBit)
import Data.ByteString.Short (ShortByteString)
import Data.Serialize (Get, get, Putter, put)
import Data.Serialize.Get (getWord8, getWord16be, getShortByteString)
import Data.Serialize.Put (putWord8, putWord16be, putShortByteString)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Word as W
import Lens.Family2.Stock (_1)

import Simplicity.Digest
import Simplicity.Inference
import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Ty

-- Decodes a bit-string of given length from a byte-stream.
getBoolVector :: Int -> Get (UV.Vector Bool)
getBoolVector i = getEvalBitStream prog
 where
  prog _abort next = UV.replicateM i next

putBoolVector :: Putter (UV.Vector Bool)
putBoolVector = putBitStream . UV.toList

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
             | w .&. 0x80 == 0x80 = uWitness <$> getBoolVector (fromIntegral (w .&. 0x7f))
             | w .&. 0x20 == 0x20 = getPrimByte w >>= go
   where
    go (Just p) = return (uPrim p)
    go Nothing = fail $ "Simplicity.Serialization.ByteString.decodeNode: Unknown primtiive #"++show w++"."

-- The 'DeserializeM' monad adds a counter to the 'Get' monad to count the number of nodes deserialized.
-- This is used to compute the offsets of references.
type DeserializeM a = StateT Integer Get a

-- Decodes a node references (a.k.a. indices) for a 'UntypedSimplicityDag'.
-- The input flag set to 'False' means to return the last index, which is offset 1.
-- The input flag set to 'True' means to parse the reference from the stream.
-- In this case we add 2 to the decoded value to get the relative offset since a relative offset of 1 is handled by the input flag set to 'False'.
getIx :: Bool -> DeserializeM Integer
getIx False = return 1
getIx True = do
  cnt <- MS.get
  ix <- lift (getSizedInteger (cnt - 2))
  unless (ix <= cnt) (fail "getIx: index out of range")
  return (ix + 2)
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
getDag = V.toList <$> V.unfoldrM (fmap f . runStateT getNode) 0
 where
  f (mnode, i) = do
    node <- mnode
    return (node, succ i)

putIx bound i | bound <= 0 = return ()
              | otherwise = putIx (bound `div` 256) (i `div` 256) >> putWord8 (fromIntegral i)

putNode :: Int -> Putter (UntypedTermF Integer)
putNode bnd node | Just (x,y) <- isUComp node = putBinary x y 0x00
                 | Just (x,y) <- isUCase node = putBinary x y 0x01
                 | Just (x,y) <- isUPair node = putBinary x y 0x02
                 | Just (x,y) <- isUDisconnect node = putBinary x y 0x03
                 | Just x <- isUInjl node = putUnary x 0x10
                 | Just x <- isUInjr node = putUnary x 0x11
                 | Just x <- isUTake node = putUnary x 0x12
                 | Just x <- isUDrop node = putUnary x 0x13
                 | Just _ <- isUIden node = putWord8 0x20
                 | Just _ <- isUUnit node = putWord8 0x21
                 | Just h <- isUHidden node = putWord8 0x23 >> put h
                 | Just w <- isUWitness node = putWitness w
                 | Just (SomeArrow p _ _) <- isUPrim node = putPrimByte p
 where
  putUnary 1 z = putWord8 z
  putUnary i z | 2 <= i = putWord8 (setBit z 3) >> putIx (bnd - 2) (i - 2)
  putBinary x 1 z = putUnary x z
  putBinary x i z | 2 <= i = putUnary x (setBit z 2) >> putIx (bnd - 2) (i - 2)
  putWitness w | len < 127 = putWord8 (0x80 .|. fromIntegral len) >> putBoolVector w
               | len <= fromIntegral (maxBound :: W.Word16) = putWord8 0xff
                                                           >> putWord16be (fromIntegral len)
                                                           >> putBoolVector w
   where
    len = UV.length w

-- | Encodes an 'UntypedSimplicityDag' as a self-delimiting byte-stream code.
putDag :: Putter UntypedSimplicityDag
putDag v = sequence (zipWith putNode [0..] v) >> putWord8 0x1f
