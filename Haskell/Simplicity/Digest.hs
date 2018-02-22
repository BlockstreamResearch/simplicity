-- | This modules wraps Data.Digest.Pure.SHA in order to simulate direct access to the SHA-256 compression function by providing access to SHA-256 midstates.
module Simplicity.Digest
  (Hash256, hash256, integerHash256, bsHash
  ,Block
  ,compress, compressHalf
  ) where

import Data.Binary.Get (Decoder(..), pushChunk, pushChunks, pushEndOfInput)
import Data.Binary (encode)
import Data.Bits ((.|.), shiftL)
import Data.Digest.Pure.SHA (SHA256State, sha256Incremental, padSHA1)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL

-- | Represents a 256-bit hash value or midstate from SHA-256.
newtype Hash256 = Hash256 (Decoder SHA256State)

-- | Extracts the 256 hash value as an 'BS.ByteString'.
hash256 :: Hash256 -> BS.ByteString
hash256 (Hash256 state) = case pushEndOfInput state of
  Done _ _ x -> BSL.toStrict (encode x)
  _          -> error "getHash256 unexpected decoder state"

-- | Extracts the 256 hash value as an integer.
integerHash256 :: Hash256 -> Integer
integerHash256 h = BS.foldl' go 0 $ hash256 h
 where
  go n w = (n `shiftL` 8) .|. fromIntegral w

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString'.
bsHash :: BSL.ByteString -> Hash256
bsHash = Hash256 . pushChunks sha256Incremental . padSHA1

type Block = (Hash256, Hash256)

-- | Given an initial value and a block of data consisting of a pair of hashes, apply the SHA-256 compression function.
compress :: Hash256 -> Block -> Hash256
compress (Hash256 iv) (h1, h2) = Hash256 $ iv `pushChunk` hash256 h1 `pushChunk` hash256 h2

-- | Given an initial value and a block of data consisting of a one hash followed by 256-bits of zeros, apply the SHA-256 compression function.
compressHalf :: Hash256 -> Hash256 -> Hash256
compressHalf (Hash256 iv) h = Hash256 $ iv `pushChunk` hash256 h `pushChunk` zero
 where
  zero = BS.replicate 32 0
