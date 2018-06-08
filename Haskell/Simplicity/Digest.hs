-- | This modules wraps Data.Digest.Pure.SHA in order to simulate direct access to the SHA-256 compression function by providing access to SHA-256 midstates.
{-# LANGUAGE BangPatterns #-}
module Simplicity.Digest
  ( Hash256, get256Bits, integerHash256
  , IV, bsIv, ivHash, bslHash, bsHash, bitStringHash
  , Block512, compress, compressHalf
  ) where

import Control.Monad (replicateM)
import Control.Monad.Trans.State (evalState, state)
import Data.Binary.Get (Decoder(..), pushChunk, pushChunks, pushEndOfInput)
import Data.Binary (encode)
import Data.Bits ((.|.), bit, shiftL, testBit, zeroBits)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Short as BSS
import qualified Data.ByteString.Lazy as BSL
import Data.Digest.Pure.SHA (SHA256State, sha256Incremental, padSHA1)
import Data.List (foldl')
import Data.Serialize (Serialize, get, getShortByteString, put, putShortByteString)
import Data.Word (Word64)

-- | Represents a 256-bit hash value or midstate from SHA-256.
newtype Hash256 = Hash256 { hash256 :: BSS.ShortByteString } deriving Show

instance Serialize Hash256 where
  get = Hash256 <$> getShortByteString 32
  put (Hash256 bs) = putShortByteString bs

-- | Deserializes a 256-bit hash value from a stream of 'Bool's.
--
-- Note that the type @forall m. Monad m => m Bool -> m a@ is isomorphic to the free monad over the @X²@ functor.
-- In other words, 'get256Bits' has the type of a binary branching tree with leaves containing 'Hash256' values.
get256Bits :: Monad m => m Bool -> m Hash256
get256Bits next = Hash256 . BSS.pack <$> replicateM 32 (packBits <$> replicateM 8 next)
 where
  packBits = foldr (.|.) zeroBits . concat . zipWith f [7,6..0]
   where
    f i True = [bit i]
    f i False = []

-- | Extracts the 256 hash value as an integer.
integerHash256 :: Hash256 -> Integer
integerHash256 h = foldl' go 0 . BSS.unpack $ hash256 h
 where
  go n w = (n `shiftL` 8) .|. fromIntegral w

-- | Represents a SHA-256 midstate.  This is either the SHA-256 initial value,
-- or some SHA-256 midstate created from applying the SHA-256 'compress'ion
-- function.
newtype IV = IV (Decoder SHA256State)

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString' representing an initial value.
bsIv :: BSL.ByteString -> IV
bsIv = IV . pushChunks sha256Incremental . padSHA1

-- | Realize a initial value as a concrete Hash.
ivHash :: IV -> Hash256
ivHash (IV state) =  case pushEndOfInput state of
  Done _ _ x -> Hash256 . BSS.toShort . BSL.toStrict . encode $ x
  _          -> error "getHash256 unexpected decoder state"

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString'.
bslHash :: BSL.ByteString -> Hash256
bslHash = ivHash . bsIv

-- | Computes a SHA-256 hash from a 'BS.ByteString'.
bsHash :: BS.ByteString -> Hash256
bsHash = bslHash . BSL.fromStrict

-- Perpare a bit string for SHA-256 hashing by adding the padding and grouping bits into blocks.
padSha256 :: [Bool] -> [Block512]
padSha256 l = go 0 (l ++ [True])
 where
  go :: Word64 -> [Bool] -> [Block512]
  go !i l | 512 < lenPre + 64 = blockify pre : go (i + fromIntegral lenPre) post
          | otherwise = [blockify (pre ++ replicate (512 - 64 - lenPre) False ++ map (testBit (i + fromIntegral lenPre - 1)) [63, 62 .. 0])]
   where
    (pre, post) = splitAt 512 l
    lenPre = length pre
    blockify = evalState (twice (get256Bits (state prog)))
     where
      prog [] = (False, [])
      prog (b:bs) = (b, bs)
      twice m = (,) <$> m <*> m

-- | Compues a SHA-256 hash from a bit-string.
bitStringHash :: [Bool] -> Hash256
bitStringHash = ivHash . foldl' compress (IV sha256Incremental) . padSha256

-- | A SHA-256 block is 512 bits.  For Simplicity's Merkle tree application, we
-- will be building blocks containting hashes.
type Block512 = (Hash256, Hash256)

-- | Given an initial value and a block of data consisting of a pair of hashes, apply the SHA-256 compression function.
compress :: IV -> Block512 -> IV
compress (IV state) (h1, h2) = IV $ state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)

-- | Given an initial value and a block of data consisting of a one hash followed by 256-bits of zeros, apply the SHA-256 compression function.
compressHalf :: IV -> Hash256 -> IV
compressHalf iv h = compress iv (zero, h)
 where
  zero = Hash256 . BSS.pack $ replicate 32 0
