-- | This modules wraps Data.Digest.Pure.SHA in order to simulate direct access to the SHA-256 compression function by providing access to SHA-256 midstates.
module Simplicity.Digest
  (Hash256, integerHash256
  ,IV, bsIv, ivHash, bslHash, bsHash
  ,Block ,compress, compressHalf
  ) where

import Data.Binary.Get (Decoder(..), pushChunk, pushChunks, pushEndOfInput)
import Data.Binary (encode)
import Data.Bits ((.|.), shiftL)
import Data.Digest.Pure.SHA (SHA256State, sha256Incremental, padSHA1)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL

-- | Represents a 256-bit hash value or midstate from SHA-256.
newtype Hash256 = Hash256 { hash256 :: BS.ByteString } deriving Show

-- | Extracts the 256 hash value as an integer.
integerHash256 :: Hash256 -> Integer
integerHash256 h = BS.foldl' go 0 $ hash256 h
 where
  go n w = (n `shiftL` 8) .|. fromIntegral w

newtype IV = IV (Decoder SHA256State)

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString' representing an initial value.
bsIv :: BSL.ByteString -> IV
bsIv = IV . pushChunks sha256Incremental . padSHA1

-- | Realize a initial value as a concrete Hash.
ivHash :: IV -> Hash256
ivHash (IV state) =  case pushEndOfInput state of
  Done _ _ x -> Hash256 . BSL.toStrict . encode $ x
  _          -> error "getHash256 unexpected decoder state"

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString'.
bslHash :: BSL.ByteString -> Hash256
bslHash = ivHash . bsIv

-- | Computes a SHA-256 hash from a 'BS.ByteString'.
bsHash :: BS.ByteString -> Hash256
bsHash = bslHash . BSL.fromStrict

type Block = (Hash256, Hash256)

-- | Given an initial value and a block of data consisting of a pair of hashes, apply the SHA-256 compression function.
compress :: IV -> Block -> IV
compress (IV state) (h1, h2) = IV $ state `pushChunk` hash256 h1 `pushChunk` hash256 h2

-- | Given an initial value and a block of data consisting of a one hash followed by 256-bits of zeros, apply the SHA-256 compression function.
compressHalf :: IV -> Hash256 -> IV
compressHalf iv h = compress iv (h, zero)
 where
  zero = Hash256 (BS.replicate 32 0)
