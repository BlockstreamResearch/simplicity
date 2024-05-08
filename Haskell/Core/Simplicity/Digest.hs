-- | This modules wraps Data.Digest.Pure.SHA in order to simulate direct access to the SHA-256 compression function by providing access to SHA-256 midstates.
{-# LANGUAGE BangPatterns #-}
module Simplicity.Digest
  ( Hash256, be256, be256_, le256, le256_
  , get256Bits, put256Bits
  , integerHash256, hash0
  , IV, noTagIv, tagIv, ivHash, bslHash, bsHash, bslDoubleHash, taggedHash, bitStringHash
  , Block512, compress, compressHalf
  , freeStart
  , Ctx(..), ctxInit, ctxBuild, ctxAdd, ctxFinalize
  ) where

import Control.Monad (replicateM)
import Control.Monad.Trans.State (evalState, state)
import Data.Binary.Get (Decoder(..), pushChunk, pushChunks, pushEndOfInput)
import qualified Data.Binary as Binary
import Data.Bits ((.|.), bit, shiftL, testBit, zeroBits)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Short as BSS
import qualified Data.ByteString.Lazy as BSL
import Data.List (foldl')
import Data.Serialize (Serialize, encode, get, getShortByteString, put, putShortByteString)
import Lens.Family2 (Adapter', Lens', (^.), (^..), over, review, under)
import Lens.Family2.Stock (bend, bend_)
import Lens.Family2.Unchecked (adapter)
import Numeric (showHex)
import Simplicity.Digest.Pure.SHA
import Simplicity.Word
import Simplicity.Serialization

-- | Represents a 256-bit hash value or midstate from SHA-256.
newtype Hash256 = Hash256 { hash256 :: BSS.ShortByteString } deriving (Eq, Ord)

instance Show Hash256 where
  show h = "0x" ++ showHex256 (h^.be256_)

instance Serialize Hash256 where
  get = Hash256 <$> getShortByteString 32
  put (Hash256 bs) = putShortByteString bs

-- | A 'Lens' accessing a 'Word256' from a 'Hash256' using a big endian interpretation.
be256_ :: Lens' Hash256 Word256
be256_ = under be256

-- | An adaptor converting a 'Hash256' to a 'Word256' using a big endian interpretation.
be256 :: Adapter' Hash256 Word256
be256 = adapter to fro
 where
  fro w = Hash256 $ BSS.toShort (encode w)
  to h = foldl' go 0 . BSS.unpack $ hash256 h
   where
    go n w = (n `shiftL` 8) .|. fromIntegral w

-- | A 'Lens' accessing a 'Word256' from a 'Hash256' using a little endian interpretation.
le256_ :: Lens' Hash256 Word256
le256_ = under le256

-- | An adaptor converting a 'Hash256' to a 'Word256' using a little endian interpretation.
le256 :: Adapter' Hash256 Word256
le256 = adapter rev rev . be256
 where
  rev = Hash256 . BSS.toShort . BS.reverse . BSS.fromShort . hash256

-- | Deserializes a 256-bit hash value from a stream of 'Bool's.
--
-- Note that the type @forall m. Monad m => m Bool -> m a@ is isomorphic to the free monad over the @X²@ functor.
-- In other words, 'get256Bits' has the type of a binary branching tree with leaves containing 'Hash256' values.
--
-- Due to the flat nature of 'Hash256' only the 'Applicative' interface happens to be used by 'get256Bits'.
-- This is why the constraint is 'Applicative' instead of 'Monad'.
get256Bits :: Applicative m => m Bool -> m Hash256
get256Bits = review (be256.bend)

-- | Serializes a 256-bit hash value to a stream of 'Bool's.
put256Bits :: Hash256 -> DList Bool
put256Bits h k = (h^..be256_.bend_) ++ k

-- | Extracts the 256 hash value as an integer.
integerHash256 :: Hash256 -> Integer
integerHash256 h = toInteger $ h^.be256_

-- | A hash value with all bits set to 0.
--
-- @ integerHash256 hash0 = 0 @
hash0 :: Hash256
hash0 = review (over be256) 0

-- | Represents a SHA-256 midstate.  This is either the SHA-256 initial value,
-- or some SHA-256 midstate created from applying the SHA-256 'compress'ion
-- function.
newtype IV = IV (Decoder SHA256State)

-- | The SHA-256 inital value.
noTagIv :: IV
noTagIv = IV sha256Incremental

-- | Return the SHA-256 midstate after compression of a block of the SHA256 digest of the given tag name twice.
-- This twice repeated SHA256 digest is the tagged hash format used by BIP-340 and BIP-341.
tagIv :: String -> IV
tagIv tag = compress noTagIv (tagDigest, tagDigest)
 where
  tagDigest = bsHash . BSC.pack $ tag

-- | Realize a initial value as a concrete Hash.
ivHash :: IV -> Hash256
ivHash (IV state) =  case pushEndOfInput state of
  Done _ _ x -> Hash256 . BSS.toShort . BSL.toStrict . Binary.encode $ x
  _          -> error "getHash256 unexpected decoder state"

-- | Restore an IV from an given midstate.
--
-- WARNING: Use of 'freeStart' may violate the security assumptions about SHA-256.
freeStart :: Hash256 -> IV
freeStart midstate = IV $ runSHAIncremental midstateSHA256State processSHA256Block
 where
  midstateSHA256State = Binary.decode . BSL.fromStrict . encode $ midstate

-- | Computes a SHA-256 hash from a lazy 'BSL.ByteString'.
bslHash :: BSL.ByteString -> Hash256
bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1

-- | Computes a SHA-256 hash from a 'BS.ByteString'.
bsHash :: BS.ByteString -> Hash256
bsHash = bslHash . BSL.fromStrict

-- | Computes a Bitcoin-style double SHA-256 hash from a lazy 'BSL.ByteString'.
bslDoubleHash :: BSL.ByteString -> Hash256
bslDoubleHash = bsHash . encode . bslHash

-- | Computes a SHA-256 tagged hash.
taggedHash :: String -- ^ tag
           -> BS.ByteString -- ^ message
           -> Hash256
taggedHash tag str = ivHash . IV . pushChunks state $ BSL.fromStrict str <> BSL.fromChunks (padSHA1Chunks (len + 64))
 where
  IV state = tagIv tag
  len = BS.length str

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

-- | Given an initial value and a block of data consisting of a one hash preceeded by 256-bits of zeros, apply the SHA-256 compression function.
compressHalf :: IV -> Hash256 -> IV
compressHalf iv h = compress iv (hash0, h)

-- | A SHA-256 context for bytes.
data Ctx = Ctx { ctxBuffer :: BS.ByteString
               , ctxCounter :: Integer
               , ctxIV :: IV
               }

-- | Initialize an empty 'Ctx'.
ctxInit :: Ctx
ctxInit = Ctx { ctxBuffer = mempty, ctxCounter = 0, ctxIV = noTagIv }

-- | Normalize the context's buffer to less than 64 bytes.
--
-- This may fail if the SHA-256 counter overflows.
ctxNormalize :: Ctx -> Maybe Ctx
ctxNormalize ctx | 2^55 <= ctxCounter ctx = Nothing
                 | BS.length (ctxBuffer ctx) < 64 = Just ctx
                 | otherwise = ctxNormalize
                             $ Ctx { ctxBuffer = BS.drop 64 (ctxBuffer ctx)
                                   , ctxCounter = 1 + ctxCounter ctx
                                   , ctxIV = let IV state = ctxIV ctx in IV (state `pushChunk` BS.take 64 (ctxBuffer ctx))
                                   }

-- | Append a bytestring to a context.
--
-- This may fail if the SHA-256 counter overflows.
ctxAdd :: Ctx -> BS.ByteString -> Maybe Ctx
ctxAdd ctx bs = ctxNormalize $ ctx { ctxBuffer = ctxBuffer ctx <> bs }

-- | Freely construct a SHA-256 'Ctx' from its components.
--
-- This may fail if the SHA-256 counter overflows.
--
-- WARNING: Use of 'ctxBuild' may violate the secuirty assumptions about SHA-256.
ctxBuild :: [Word8] -- ^ Buffer
         -> Integer -- ^ Compression count
         -> Hash256 -- ^ Midstate
         -> Maybe Ctx
ctxBuild buffer counter midstate = ctxNormalize $ Ctx { ctxBuffer = BS.pack buffer
                                                      , ctxCounter = counter
                                                      , ctxIV = freeStart midstate
                                                      }

-- | Add the SHA-256 padding an produce the final hash output.
ctxFinalize :: Ctx -> Hash256
ctxFinalize ctx | 8*size < 2^64 = Hash256 . BSS.toShort . BSL.toStrict . Binary.encode
                              $ completeSha256Incremental (state `pushChunk` ctxBuffer ctx) (fromInteger size)
 where
  size = ctxCounter ctx * 64 + toInteger (BS.length (ctxBuffer ctx))
  IV state = ctxIV ctx
