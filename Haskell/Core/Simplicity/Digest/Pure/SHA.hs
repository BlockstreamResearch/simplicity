{- This is a copy of Galoi's Data.Digets.Pure.SHA module.
   We copy it here in order to export some internal functions.
   This is needed to allow for "free-start" SHA-256, which violates normal SHA-256 encapsulation rules.
   This file is subject to their licence below.
-}
{-
Copyright (c) 2008, Galois, Inc.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in 
    the documentation and/or other materials provided with the 
    distribution.
  * Neither the name of the Galois, Inc. nor the names of its
    contributors may be used to endorse or promote products derived 
    from this software without specific prior written permission.  

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
-}
{-# LANGUAGE BangPatterns, CPP, FlexibleInstances #-}
-- |Pure implementations of the SHA suite of hash functions. The implementation
-- is basically an unoptimized translation of FIPS 180-2 into Haskell. If you're
-- looking for performance, you probably won't find it here.
module Simplicity.Digest.Pure.SHA
       ( -- * 'Digest' and related functions
         Digest
       , SHA1State, SHA256State, SHA512State
       , showDigest
       , integerDigest
       , bytestringDigest
         -- * Calculating hashes
       , sha1
       , sha224
       , sha256
       , sha384
       , sha512
       , sha1Incremental
       , completeSha1Incremental
       , sha224Incremental
       , completeSha224Incremental
       , sha256Incremental
       , completeSha256Incremental
       , sha384Incremental
       , completeSha384Incremental
       , sha512Incremental
       , completeSha512Incremental
         -- * Calculating message authentication codes (MACs)
       , hmacSha1
       , hmacSha224
       , hmacSha256
       , hmacSha384
       , hmacSha512
         -- * Internal routines included for testing
       , toBigEndianSBS, fromBigEndianSBS
       , calc_k
       , padSHA1, padSHA512
       , padSHA1Chunks, padSHA512Chunks
         -- * Internal routines included for freestart
       , runSHAIncremental, processSHA256Block
       )
 where
 
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.Bits
import Data.ByteString.Lazy(ByteString)
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString as SBS
import Data.Char (intToDigit)
import Data.List (foldl')

-- | An abstract datatype for digests.
newtype Digest t = Digest ByteString deriving (Eq,Ord)

instance Show (Digest t) where
  show = showDigest

instance Binary (Digest SHA1State) where
  get = Digest `fmap` getLazyByteString 20
  put (Digest bs) = putLazyByteString bs

instance Binary (Digest SHA256State) where
  get = Digest `fmap` getLazyByteString 32
  put (Digest bs) = putLazyByteString bs

instance Binary (Digest SHA512State) where
  get = Digest `fmap` getLazyByteString 64
  put (Digest bs) = putLazyByteString bs

-- --------------------------------------------------------------------------
--
-- State Definitions and Initial States
--
-- --------------------------------------------------------------------------

data SHA1State = SHA1S !Word32 !Word32 !Word32 !Word32 !Word32

initialSHA1State :: SHA1State
initialSHA1State = SHA1S 0x67452301 0xefcdab89 0x98badcfe 0x10325476 0xc3d2e1f0

data SHA256State = SHA256S !Word32 !Word32 !Word32 !Word32
                           !Word32 !Word32 !Word32 !Word32

initialSHA224State :: SHA256State
initialSHA224State = SHA256S 0xc1059ed8 0x367cd507 0x3070dd17 0xf70e5939
                             0xffc00b31 0x68581511 0x64f98fa7 0xbefa4fa4

initialSHA256State :: SHA256State
initialSHA256State = SHA256S 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
                             0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19

data SHA512State = SHA512S !Word64 !Word64 !Word64 !Word64
                           !Word64 !Word64 !Word64 !Word64

initialSHA384State :: SHA512State
initialSHA384State = SHA512S 0xcbbb9d5dc1059ed8 0x629a292a367cd507
                             0x9159015a3070dd17 0x152fecd8f70e5939
                             0x67332667ffc00b31 0x8eb44a8768581511
                             0xdb0c2e0d64f98fa7 0x47b5481dbefa4fa4

initialSHA512State :: SHA512State
initialSHA512State = SHA512S 0x6a09e667f3bcc908 0xbb67ae8584caa73b
                             0x3c6ef372fe94f82b 0xa54ff53a5f1d36f1
                             0x510e527fade682d1 0x9b05688c2b3e6c1f
                             0x1f83d9abfb41bd6b 0x5be0cd19137e2179

-- --------------------------------------------------------------------------
--
-- Synthesize of states to and from ByteStrings
--
-- --------------------------------------------------------------------------


synthesizeSHA1 :: SHA1State -> Put
synthesizeSHA1 (SHA1S a b c d e) = do
  putWord32be a
  putWord32be b
  putWord32be c
  putWord32be d
  putWord32be e

getSHA1 :: Get SHA1State
getSHA1 = do
  a <- getWord32be
  b <- getWord32be
  c <- getWord32be
  d <- getWord32be
  e <- getWord32be
  return $! SHA1S a b c d e

synthesizeSHA224 :: SHA256State -> Put
synthesizeSHA224 (SHA256S a b c d e f g _) = do
  putWord32be a
  putWord32be b
  putWord32be c
  putWord32be d
  putWord32be e
  putWord32be f
  putWord32be g

synthesizeSHA256 :: SHA256State -> Put
synthesizeSHA256 (SHA256S a b c d e f g h) = do
  putWord32be a
  putWord32be b
  putWord32be c
  putWord32be d
  putWord32be e
  putWord32be f
  putWord32be g
  putWord32be h

getSHA256 :: Get SHA256State
getSHA256 = do
  a <- getWord32be
  b <- getWord32be
  c <- getWord32be
  d <- getWord32be
  e <- getWord32be
  f <- getWord32be
  g <- getWord32be
  h <- getWord32be
  return $! SHA256S a b c d e f g h

synthesizeSHA384 :: SHA512State -> Put
synthesizeSHA384 (SHA512S a b c d e f _ _) = do
  putWord64be a
  putWord64be b
  putWord64be c
  putWord64be d
  putWord64be e
  putWord64be f

synthesizeSHA512 :: SHA512State -> Put
synthesizeSHA512 (SHA512S a b c d e f g h) = do
  putWord64be a
  putWord64be b
  putWord64be c
  putWord64be d
  putWord64be e
  putWord64be f
  putWord64be g
  putWord64be h

getSHA512 :: Get SHA512State
getSHA512 = do
  a <- getWord64be
  b <- getWord64be
  c <- getWord64be
  d <- getWord64be
  e <- getWord64be
  f <- getWord64be
  g <- getWord64be
  h <- getWord64be
  return $! SHA512S a b c d e f g h

instance Binary SHA1State where
  put = synthesizeSHA1
  get = getSHA1

instance Binary SHA256State where
  put = synthesizeSHA256
  get = getSHA256

instance Binary SHA512State where
  put = synthesizeSHA512
  get = getSHA512


-- --------------------------------------------------------------------------
--
-- Padding
--
-- --------------------------------------------------------------------------

padSHA1 :: ByteString -> ByteString
padSHA1 = generic_pad 448 512 64

padSHA1Chunks :: Int -> [SBS.ByteString]
padSHA1Chunks = generic_pad_chunks 448 512 64

padSHA512 :: ByteString -> ByteString
padSHA512 = generic_pad 896 1024 128

padSHA512Chunks :: Int -> [SBS.ByteString]
padSHA512Chunks = generic_pad_chunks 896 1024 128

generic_pad :: Word64 -> Word64 -> Int -> ByteString -> ByteString
generic_pad a b lSize bs =
  BS.fromChunks $! go 0 chunks
 where
  chunks = BS.toChunks bs

  -- Generates the padded ByteString at the same time it computes the length
  -- of input. If the length is computed before the computation of the hash, it
  -- will break the lazy evaluation of the input and no longer run in constant
  -- memory space.
  go !len [] = generic_pad_chunks a b lSize len
  go !len (c:cs) = c : go (len + SBS.length c) cs

generic_pad_chunks :: Word64 -> Word64 -> Int -> Int -> [SBS.ByteString]
generic_pad_chunks a b lSize len =
  let lenBits = fromIntegral $ len * 8
      k = calc_k a b lenBits
      -- INVARIANT: k is necessarily > 0, and (k + 1) is a multiple of 8.
      kBytes = (k + 1) `div` 8
      nZeroBytes = fromIntegral $! kBytes - 1
      padLength = toBigEndianSBS lSize lenBits
  in [SBS.singleton 0x80, SBS.replicate nZeroBytes 0, padLength]

-- Given a, b, and l, calculate the smallest k such that (l + 1 + k) mod b = a.
calc_k :: Word64 -> Word64 -> Word64 -> Word64
calc_k a b l =
  if r <= -1
    then fromIntegral r + b
    else fromIntegral r
 where
  r = toInteger a - toInteger l `mod` toInteger b - 1

toBigEndianSBS :: (Integral a, Bits a) => Int -> a -> SBS.ByteString
toBigEndianSBS s val = SBS.pack $ map getBits [s - 8, s - 16 .. 0]
 where
   getBits x = fromIntegral $ (val `shiftR` x) .&. 0xFF

fromBigEndianSBS :: (Integral a, Bits a) => SBS.ByteString -> a
fromBigEndianSBS =
  SBS.foldl (\ acc x -> (acc `shiftL` 8) + fromIntegral x) 0

-- --------------------------------------------------------------------------
--
-- SHA Functions
--
-- --------------------------------------------------------------------------

{-# SPECIALIZE ch :: Word32 -> Word32 -> Word32 -> Word32 #-}
{-# SPECIALIZE ch :: Word64 -> Word64 -> Word64 -> Word64 #-}
ch :: Bits a => a -> a -> a -> a
ch x y z = (x .&. y) `xor` (complement x .&. z)

{-# SPECIALIZE maj :: Word32 -> Word32 -> Word32 -> Word32 #-}
{-# SPECIALIZE maj :: Word64 -> Word64 -> Word64 -> Word64 #-}
maj :: Bits a => a -> a -> a -> a
maj x y z = (x .&. (y .|. z)) .|. (y .&. z)
-- note:
--   the original functions is (x & y) ^ (x & z) ^ (y & z)
--   if you fire off truth tables, this is equivalent to 
--     (x & y) | (x & z) | (y & z)
--   which you can the use distribution on:
--     (x & (y | z)) | (y & z)
--   which saves us one operation.

bsig256_0 :: Word32 -> Word32
bsig256_0 x = rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22

bsig256_1 :: Word32 -> Word32
bsig256_1 x = rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25

lsig256_0 :: Word32 -> Word32
lsig256_0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3

lsig256_1 :: Word32 -> Word32
lsig256_1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10

bsig512_0 :: Word64 -> Word64
bsig512_0 x = rotateR x 28 `xor` rotateR x 34 `xor` rotateR x 39

bsig512_1 :: Word64 -> Word64
bsig512_1 x = rotateR x 14 `xor` rotateR x 18 `xor` rotateR x 41

lsig512_0 :: Word64 -> Word64
lsig512_0 x = rotateR x 1 `xor` rotateR x 8 `xor` shiftR x 7

lsig512_1 :: Word64 -> Word64
lsig512_1 x = rotateR x 19 `xor` rotateR x 61 `xor` shiftR x 6

-- --------------------------------------------------------------------------
--
-- Message Schedules
--
-- --------------------------------------------------------------------------

data SHA1Sched = SHA1Sched !Word32 !Word32 !Word32 !Word32 !Word32 --  0 -  4
                           !Word32 !Word32 !Word32 !Word32 !Word32 --  5 -  9
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 10 - 14
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 15 - 19
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 20 - 24
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 25 - 29
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 30 - 34
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 35 - 39
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 40 - 44
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 45 - 49
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 50 - 54
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 55 - 59
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 60 - 64
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 65 - 69
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 70 - 74
                           !Word32 !Word32 !Word32 !Word32 !Word32 -- 75 - 79

getSHA1Sched :: Get SHA1Sched
getSHA1Sched = do
  w00 <- getWord32be
  w01 <- getWord32be
  w02 <- getWord32be
  w03 <- getWord32be
  w04 <- getWord32be
  w05 <- getWord32be
  w06 <- getWord32be
  w07 <- getWord32be
  w08 <- getWord32be
  w09 <- getWord32be
  w10 <- getWord32be
  w11 <- getWord32be
  w12 <- getWord32be
  w13 <- getWord32be
  w14 <- getWord32be
  w15 <- getWord32be
  let w16 = rotateL (w13 `xor` w08 `xor` w02 `xor` w00) 1
      w17 = rotateL (w14 `xor` w09 `xor` w03 `xor` w01) 1
      w18 = rotateL (w15 `xor` w10 `xor` w04 `xor` w02) 1
      w19 = rotateL (w16 `xor` w11 `xor` w05 `xor` w03) 1
      w20 = rotateL (w17 `xor` w12 `xor` w06 `xor` w04) 1
      w21 = rotateL (w18 `xor` w13 `xor` w07 `xor` w05) 1
      w22 = rotateL (w19 `xor` w14 `xor` w08 `xor` w06) 1
      w23 = rotateL (w20 `xor` w15 `xor` w09 `xor` w07) 1
      w24 = rotateL (w21 `xor` w16 `xor` w10 `xor` w08) 1
      w25 = rotateL (w22 `xor` w17 `xor` w11 `xor` w09) 1
      w26 = rotateL (w23 `xor` w18 `xor` w12 `xor` w10) 1
      w27 = rotateL (w24 `xor` w19 `xor` w13 `xor` w11) 1
      w28 = rotateL (w25 `xor` w20 `xor` w14 `xor` w12) 1
      w29 = rotateL (w26 `xor` w21 `xor` w15 `xor` w13) 1
      w30 = rotateL (w27 `xor` w22 `xor` w16 `xor` w14) 1
      w31 = rotateL (w28 `xor` w23 `xor` w17 `xor` w15) 1
      w32 = rotateL (w29 `xor` w24 `xor` w18 `xor` w16) 1
      w33 = rotateL (w30 `xor` w25 `xor` w19 `xor` w17) 1
      w34 = rotateL (w31 `xor` w26 `xor` w20 `xor` w18) 1
      w35 = rotateL (w32 `xor` w27 `xor` w21 `xor` w19) 1
      w36 = rotateL (w33 `xor` w28 `xor` w22 `xor` w20) 1
      w37 = rotateL (w34 `xor` w29 `xor` w23 `xor` w21) 1
      w38 = rotateL (w35 `xor` w30 `xor` w24 `xor` w22) 1
      w39 = rotateL (w36 `xor` w31 `xor` w25 `xor` w23) 1
      w40 = rotateL (w37 `xor` w32 `xor` w26 `xor` w24) 1
      w41 = rotateL (w38 `xor` w33 `xor` w27 `xor` w25) 1
      w42 = rotateL (w39 `xor` w34 `xor` w28 `xor` w26) 1
      w43 = rotateL (w40 `xor` w35 `xor` w29 `xor` w27) 1
      w44 = rotateL (w41 `xor` w36 `xor` w30 `xor` w28) 1
      w45 = rotateL (w42 `xor` w37 `xor` w31 `xor` w29) 1
      w46 = rotateL (w43 `xor` w38 `xor` w32 `xor` w30) 1
      w47 = rotateL (w44 `xor` w39 `xor` w33 `xor` w31) 1
      w48 = rotateL (w45 `xor` w40 `xor` w34 `xor` w32) 1
      w49 = rotateL (w46 `xor` w41 `xor` w35 `xor` w33) 1
      w50 = rotateL (w47 `xor` w42 `xor` w36 `xor` w34) 1
      w51 = rotateL (w48 `xor` w43 `xor` w37 `xor` w35) 1
      w52 = rotateL (w49 `xor` w44 `xor` w38 `xor` w36) 1
      w53 = rotateL (w50 `xor` w45 `xor` w39 `xor` w37) 1
      w54 = rotateL (w51 `xor` w46 `xor` w40 `xor` w38) 1
      w55 = rotateL (w52 `xor` w47 `xor` w41 `xor` w39) 1
      w56 = rotateL (w53 `xor` w48 `xor` w42 `xor` w40) 1
      w57 = rotateL (w54 `xor` w49 `xor` w43 `xor` w41) 1
      w58 = rotateL (w55 `xor` w50 `xor` w44 `xor` w42) 1
      w59 = rotateL (w56 `xor` w51 `xor` w45 `xor` w43) 1
      w60 = rotateL (w57 `xor` w52 `xor` w46 `xor` w44) 1
      w61 = rotateL (w58 `xor` w53 `xor` w47 `xor` w45) 1
      w62 = rotateL (w59 `xor` w54 `xor` w48 `xor` w46) 1
      w63 = rotateL (w60 `xor` w55 `xor` w49 `xor` w47) 1
      w64 = rotateL (w61 `xor` w56 `xor` w50 `xor` w48) 1
      w65 = rotateL (w62 `xor` w57 `xor` w51 `xor` w49) 1
      w66 = rotateL (w63 `xor` w58 `xor` w52 `xor` w50) 1
      w67 = rotateL (w64 `xor` w59 `xor` w53 `xor` w51) 1
      w68 = rotateL (w65 `xor` w60 `xor` w54 `xor` w52) 1
      w69 = rotateL (w66 `xor` w61 `xor` w55 `xor` w53) 1
      w70 = rotateL (w67 `xor` w62 `xor` w56 `xor` w54) 1
      w71 = rotateL (w68 `xor` w63 `xor` w57 `xor` w55) 1
      w72 = rotateL (w69 `xor` w64 `xor` w58 `xor` w56) 1
      w73 = rotateL (w70 `xor` w65 `xor` w59 `xor` w57) 1
      w74 = rotateL (w71 `xor` w66 `xor` w60 `xor` w58) 1
      w75 = rotateL (w72 `xor` w67 `xor` w61 `xor` w59) 1
      w76 = rotateL (w73 `xor` w68 `xor` w62 `xor` w60) 1
      w77 = rotateL (w74 `xor` w69 `xor` w63 `xor` w61) 1
      w78 = rotateL (w75 `xor` w70 `xor` w64 `xor` w62) 1
      w79 = rotateL (w76 `xor` w71 `xor` w65 `xor` w63) 1
  return $! SHA1Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
                      w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
                      w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
                      w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
                      w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
                      w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
                      w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
                      w70 w71 w72 w73 w74 w75 w76 w77 w78 w79

data SHA256Sched = SHA256Sched !Word32 !Word32 !Word32 !Word32 !Word32 -- 00-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 05-09
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 10-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 15-09
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 20-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 25-09
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 30-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 35-09
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 40-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 45-09
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 50-04
                               !Word32 !Word32 !Word32 !Word32 !Word32 -- 55-09
                               !Word32 !Word32 !Word32 !Word32         -- 60-63

getSHA256Sched :: Get SHA256Sched
getSHA256Sched = do
  w00 <- getWord32be
  w01 <- getWord32be
  w02 <- getWord32be
  w03 <- getWord32be
  w04 <- getWord32be
  w05 <- getWord32be
  w06 <- getWord32be
  w07 <- getWord32be
  w08 <- getWord32be
  w09 <- getWord32be
  w10 <- getWord32be
  w11 <- getWord32be
  w12 <- getWord32be
  w13 <- getWord32be
  w14 <- getWord32be
  w15 <- getWord32be
  let w16 = lsig256_1 w14 + w09 + lsig256_0 w01 + w00
      w17 = lsig256_1 w15 + w10 + lsig256_0 w02 + w01
      w18 = lsig256_1 w16 + w11 + lsig256_0 w03 + w02
      w19 = lsig256_1 w17 + w12 + lsig256_0 w04 + w03
      w20 = lsig256_1 w18 + w13 + lsig256_0 w05 + w04
      w21 = lsig256_1 w19 + w14 + lsig256_0 w06 + w05
      w22 = lsig256_1 w20 + w15 + lsig256_0 w07 + w06
      w23 = lsig256_1 w21 + w16 + lsig256_0 w08 + w07
      w24 = lsig256_1 w22 + w17 + lsig256_0 w09 + w08
      w25 = lsig256_1 w23 + w18 + lsig256_0 w10 + w09
      w26 = lsig256_1 w24 + w19 + lsig256_0 w11 + w10
      w27 = lsig256_1 w25 + w20 + lsig256_0 w12 + w11
      w28 = lsig256_1 w26 + w21 + lsig256_0 w13 + w12
      w29 = lsig256_1 w27 + w22 + lsig256_0 w14 + w13
      w30 = lsig256_1 w28 + w23 + lsig256_0 w15 + w14
      w31 = lsig256_1 w29 + w24 + lsig256_0 w16 + w15
      w32 = lsig256_1 w30 + w25 + lsig256_0 w17 + w16
      w33 = lsig256_1 w31 + w26 + lsig256_0 w18 + w17
      w34 = lsig256_1 w32 + w27 + lsig256_0 w19 + w18
      w35 = lsig256_1 w33 + w28 + lsig256_0 w20 + w19
      w36 = lsig256_1 w34 + w29 + lsig256_0 w21 + w20
      w37 = lsig256_1 w35 + w30 + lsig256_0 w22 + w21
      w38 = lsig256_1 w36 + w31 + lsig256_0 w23 + w22
      w39 = lsig256_1 w37 + w32 + lsig256_0 w24 + w23
      w40 = lsig256_1 w38 + w33 + lsig256_0 w25 + w24
      w41 = lsig256_1 w39 + w34 + lsig256_0 w26 + w25
      w42 = lsig256_1 w40 + w35 + lsig256_0 w27 + w26
      w43 = lsig256_1 w41 + w36 + lsig256_0 w28 + w27
      w44 = lsig256_1 w42 + w37 + lsig256_0 w29 + w28
      w45 = lsig256_1 w43 + w38 + lsig256_0 w30 + w29
      w46 = lsig256_1 w44 + w39 + lsig256_0 w31 + w30
      w47 = lsig256_1 w45 + w40 + lsig256_0 w32 + w31
      w48 = lsig256_1 w46 + w41 + lsig256_0 w33 + w32
      w49 = lsig256_1 w47 + w42 + lsig256_0 w34 + w33
      w50 = lsig256_1 w48 + w43 + lsig256_0 w35 + w34
      w51 = lsig256_1 w49 + w44 + lsig256_0 w36 + w35
      w52 = lsig256_1 w50 + w45 + lsig256_0 w37 + w36
      w53 = lsig256_1 w51 + w46 + lsig256_0 w38 + w37
      w54 = lsig256_1 w52 + w47 + lsig256_0 w39 + w38
      w55 = lsig256_1 w53 + w48 + lsig256_0 w40 + w39
      w56 = lsig256_1 w54 + w49 + lsig256_0 w41 + w40
      w57 = lsig256_1 w55 + w50 + lsig256_0 w42 + w41
      w58 = lsig256_1 w56 + w51 + lsig256_0 w43 + w42
      w59 = lsig256_1 w57 + w52 + lsig256_0 w44 + w43
      w60 = lsig256_1 w58 + w53 + lsig256_0 w45 + w44
      w61 = lsig256_1 w59 + w54 + lsig256_0 w46 + w45
      w62 = lsig256_1 w60 + w55 + lsig256_0 w47 + w46
      w63 = lsig256_1 w61 + w56 + lsig256_0 w48 + w47
  return $! SHA256Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
                        w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
                        w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
                        w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
                        w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
                        w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
                        w60 w61 w62 w63

data SHA512Sched = SHA512Sched !Word64 !Word64 !Word64 !Word64 !Word64 --  0- 4
                               !Word64 !Word64 !Word64 !Word64 !Word64 --  5- 9
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 10-14
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 15-19
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 20-24
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 25-29
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 30-34
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 35-39
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 40-44
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 45-49
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 50-54
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 55-59
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 60-64
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 65-69
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 70-74
                               !Word64 !Word64 !Word64 !Word64 !Word64 -- 75-79

getSHA512Sched :: Get SHA512Sched
getSHA512Sched = do
  w00 <- getWord64be
  w01 <- getWord64be
  w02 <- getWord64be
  w03 <- getWord64be
  w04 <- getWord64be
  w05 <- getWord64be
  w06 <- getWord64be
  w07 <- getWord64be
  w08 <- getWord64be
  w09 <- getWord64be
  w10 <- getWord64be
  w11 <- getWord64be
  w12 <- getWord64be
  w13 <- getWord64be
  w14 <- getWord64be
  w15 <- getWord64be
  let w16 = lsig512_1 w14 + w09 + lsig512_0 w01 + w00
      w17 = lsig512_1 w15 + w10 + lsig512_0 w02 + w01
      w18 = lsig512_1 w16 + w11 + lsig512_0 w03 + w02
      w19 = lsig512_1 w17 + w12 + lsig512_0 w04 + w03
      w20 = lsig512_1 w18 + w13 + lsig512_0 w05 + w04
      w21 = lsig512_1 w19 + w14 + lsig512_0 w06 + w05
      w22 = lsig512_1 w20 + w15 + lsig512_0 w07 + w06
      w23 = lsig512_1 w21 + w16 + lsig512_0 w08 + w07
      w24 = lsig512_1 w22 + w17 + lsig512_0 w09 + w08
      w25 = lsig512_1 w23 + w18 + lsig512_0 w10 + w09
      w26 = lsig512_1 w24 + w19 + lsig512_0 w11 + w10
      w27 = lsig512_1 w25 + w20 + lsig512_0 w12 + w11
      w28 = lsig512_1 w26 + w21 + lsig512_0 w13 + w12
      w29 = lsig512_1 w27 + w22 + lsig512_0 w14 + w13
      w30 = lsig512_1 w28 + w23 + lsig512_0 w15 + w14
      w31 = lsig512_1 w29 + w24 + lsig512_0 w16 + w15
      w32 = lsig512_1 w30 + w25 + lsig512_0 w17 + w16
      w33 = lsig512_1 w31 + w26 + lsig512_0 w18 + w17
      w34 = lsig512_1 w32 + w27 + lsig512_0 w19 + w18
      w35 = lsig512_1 w33 + w28 + lsig512_0 w20 + w19
      w36 = lsig512_1 w34 + w29 + lsig512_0 w21 + w20
      w37 = lsig512_1 w35 + w30 + lsig512_0 w22 + w21
      w38 = lsig512_1 w36 + w31 + lsig512_0 w23 + w22
      w39 = lsig512_1 w37 + w32 + lsig512_0 w24 + w23
      w40 = lsig512_1 w38 + w33 + lsig512_0 w25 + w24
      w41 = lsig512_1 w39 + w34 + lsig512_0 w26 + w25
      w42 = lsig512_1 w40 + w35 + lsig512_0 w27 + w26
      w43 = lsig512_1 w41 + w36 + lsig512_0 w28 + w27
      w44 = lsig512_1 w42 + w37 + lsig512_0 w29 + w28
      w45 = lsig512_1 w43 + w38 + lsig512_0 w30 + w29
      w46 = lsig512_1 w44 + w39 + lsig512_0 w31 + w30
      w47 = lsig512_1 w45 + w40 + lsig512_0 w32 + w31
      w48 = lsig512_1 w46 + w41 + lsig512_0 w33 + w32
      w49 = lsig512_1 w47 + w42 + lsig512_0 w34 + w33
      w50 = lsig512_1 w48 + w43 + lsig512_0 w35 + w34
      w51 = lsig512_1 w49 + w44 + lsig512_0 w36 + w35
      w52 = lsig512_1 w50 + w45 + lsig512_0 w37 + w36
      w53 = lsig512_1 w51 + w46 + lsig512_0 w38 + w37
      w54 = lsig512_1 w52 + w47 + lsig512_0 w39 + w38
      w55 = lsig512_1 w53 + w48 + lsig512_0 w40 + w39
      w56 = lsig512_1 w54 + w49 + lsig512_0 w41 + w40
      w57 = lsig512_1 w55 + w50 + lsig512_0 w42 + w41
      w58 = lsig512_1 w56 + w51 + lsig512_0 w43 + w42
      w59 = lsig512_1 w57 + w52 + lsig512_0 w44 + w43
      w60 = lsig512_1 w58 + w53 + lsig512_0 w45 + w44
      w61 = lsig512_1 w59 + w54 + lsig512_0 w46 + w45
      w62 = lsig512_1 w60 + w55 + lsig512_0 w47 + w46
      w63 = lsig512_1 w61 + w56 + lsig512_0 w48 + w47
      w64 = lsig512_1 w62 + w57 + lsig512_0 w49 + w48
      w65 = lsig512_1 w63 + w58 + lsig512_0 w50 + w49
      w66 = lsig512_1 w64 + w59 + lsig512_0 w51 + w50
      w67 = lsig512_1 w65 + w60 + lsig512_0 w52 + w51
      w68 = lsig512_1 w66 + w61 + lsig512_0 w53 + w52
      w69 = lsig512_1 w67 + w62 + lsig512_0 w54 + w53
      w70 = lsig512_1 w68 + w63 + lsig512_0 w55 + w54
      w71 = lsig512_1 w69 + w64 + lsig512_0 w56 + w55
      w72 = lsig512_1 w70 + w65 + lsig512_0 w57 + w56
      w73 = lsig512_1 w71 + w66 + lsig512_0 w58 + w57
      w74 = lsig512_1 w72 + w67 + lsig512_0 w59 + w58
      w75 = lsig512_1 w73 + w68 + lsig512_0 w60 + w59
      w76 = lsig512_1 w74 + w69 + lsig512_0 w61 + w60
      w77 = lsig512_1 w75 + w70 + lsig512_0 w62 + w61
      w78 = lsig512_1 w76 + w71 + lsig512_0 w63 + w62
      w79 = lsig512_1 w77 + w72 + lsig512_0 w64 + w63
  return $! SHA512Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
                        w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
                        w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
                        w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
                        w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
                        w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
                        w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
                        w70 w71 w72 w73 w74 w75 w76 w77 w78 w79

-- --------------------------------------------------------------------------
--
-- SHA Block Processors
--
-- --------------------------------------------------------------------------

processSHA1Block :: SHA1State -> Get SHA1State
processSHA1Block s00@(SHA1S a00 b00 c00 d00 e00) = do
  (SHA1Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
             w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
             w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
             w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
             w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
             w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
             w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
             w70 w71 w72 w73 w74 w75 w76 w77 w78 w79) <- getSHA1Sched
  let s01 = step1_ch  s00 0x5a827999 w00
      s02 = step1_ch  s01 0x5a827999 w01
      s03 = step1_ch  s02 0x5a827999 w02
      s04 = step1_ch  s03 0x5a827999 w03
      s05 = step1_ch  s04 0x5a827999 w04
      s06 = step1_ch  s05 0x5a827999 w05
      s07 = step1_ch  s06 0x5a827999 w06
      s08 = step1_ch  s07 0x5a827999 w07
      s09 = step1_ch  s08 0x5a827999 w08
      s10 = step1_ch  s09 0x5a827999 w09
      s11 = step1_ch  s10 0x5a827999 w10
      s12 = step1_ch  s11 0x5a827999 w11
      s13 = step1_ch  s12 0x5a827999 w12
      s14 = step1_ch  s13 0x5a827999 w13
      s15 = step1_ch  s14 0x5a827999 w14
      s16 = step1_ch  s15 0x5a827999 w15
      s17 = step1_ch  s16 0x5a827999 w16
      s18 = step1_ch  s17 0x5a827999 w17
      s19 = step1_ch  s18 0x5a827999 w18
      s20 = step1_ch  s19 0x5a827999 w19
      s21 = step1_par s20 0x6ed9eba1 w20
      s22 = step1_par s21 0x6ed9eba1 w21
      s23 = step1_par s22 0x6ed9eba1 w22
      s24 = step1_par s23 0x6ed9eba1 w23
      s25 = step1_par s24 0x6ed9eba1 w24
      s26 = step1_par s25 0x6ed9eba1 w25
      s27 = step1_par s26 0x6ed9eba1 w26
      s28 = step1_par s27 0x6ed9eba1 w27
      s29 = step1_par s28 0x6ed9eba1 w28
      s30 = step1_par s29 0x6ed9eba1 w29
      s31 = step1_par s30 0x6ed9eba1 w30
      s32 = step1_par s31 0x6ed9eba1 w31
      s33 = step1_par s32 0x6ed9eba1 w32
      s34 = step1_par s33 0x6ed9eba1 w33
      s35 = step1_par s34 0x6ed9eba1 w34
      s36 = step1_par s35 0x6ed9eba1 w35
      s37 = step1_par s36 0x6ed9eba1 w36
      s38 = step1_par s37 0x6ed9eba1 w37
      s39 = step1_par s38 0x6ed9eba1 w38
      s40 = step1_par s39 0x6ed9eba1 w39
      s41 = step1_maj s40 0x8f1bbcdc w40
      s42 = step1_maj s41 0x8f1bbcdc w41
      s43 = step1_maj s42 0x8f1bbcdc w42
      s44 = step1_maj s43 0x8f1bbcdc w43
      s45 = step1_maj s44 0x8f1bbcdc w44
      s46 = step1_maj s45 0x8f1bbcdc w45
      s47 = step1_maj s46 0x8f1bbcdc w46
      s48 = step1_maj s47 0x8f1bbcdc w47
      s49 = step1_maj s48 0x8f1bbcdc w48
      s50 = step1_maj s49 0x8f1bbcdc w49
      s51 = step1_maj s50 0x8f1bbcdc w50
      s52 = step1_maj s51 0x8f1bbcdc w51
      s53 = step1_maj s52 0x8f1bbcdc w52
      s54 = step1_maj s53 0x8f1bbcdc w53
      s55 = step1_maj s54 0x8f1bbcdc w54
      s56 = step1_maj s55 0x8f1bbcdc w55
      s57 = step1_maj s56 0x8f1bbcdc w56
      s58 = step1_maj s57 0x8f1bbcdc w57
      s59 = step1_maj s58 0x8f1bbcdc w58
      s60 = step1_maj s59 0x8f1bbcdc w59
      s61 = step1_par s60 0xca62c1d6 w60
      s62 = step1_par s61 0xca62c1d6 w61
      s63 = step1_par s62 0xca62c1d6 w62
      s64 = step1_par s63 0xca62c1d6 w63
      s65 = step1_par s64 0xca62c1d6 w64
      s66 = step1_par s65 0xca62c1d6 w65
      s67 = step1_par s66 0xca62c1d6 w66
      s68 = step1_par s67 0xca62c1d6 w67
      s69 = step1_par s68 0xca62c1d6 w68
      s70 = step1_par s69 0xca62c1d6 w69
      s71 = step1_par s70 0xca62c1d6 w70
      s72 = step1_par s71 0xca62c1d6 w71
      s73 = step1_par s72 0xca62c1d6 w72
      s74 = step1_par s73 0xca62c1d6 w73
      s75 = step1_par s74 0xca62c1d6 w74
      s76 = step1_par s75 0xca62c1d6 w75
      s77 = step1_par s76 0xca62c1d6 w76
      s78 = step1_par s77 0xca62c1d6 w77
      s79 = step1_par s78 0xca62c1d6 w78
      s80 = step1_par s79 0xca62c1d6 w79
      SHA1S a80 b80 c80 d80 e80 = s80
  return $! SHA1S (a00 + a80) (b00 + b80) (c00 + c80) (d00 + d80) (e00 + e80)

{-# INLINE step1_ch #-}
step1_ch :: SHA1State -> Word32 -> Word32 -> SHA1State
step1_ch !(SHA1S a b c d e) k w = SHA1S a' b' c' d' e'
 where a' = rotateL a 5 + ((b .&. c) `xor` (complement b .&. d)) + e + k + w
       b' = a
       c' = rotateL b 30
       d' = c
       e' = d

{-# INLINE step1_par #-}
step1_par :: SHA1State -> Word32 -> Word32 -> SHA1State
step1_par !(SHA1S a b c d e) k w = SHA1S a' b' c' d' e'
 where a' = rotateL a 5 + (b `xor` c `xor` d) + e + k + w
       b' = a
       c' = rotateL b 30
       d' = c
       e' = d

{-# INLINE step1_maj #-}
step1_maj :: SHA1State -> Word32 -> Word32 -> SHA1State
step1_maj !(SHA1S a b c d e) k w = SHA1S a' b' c' d' e'
 where a' = rotateL a 5 + ((b .&. (c .|. d)) .|. (c .&. d)) + e + k + w
       b' = a
       c' = rotateL b 30
       d' = c
       e' = d
-- See the note on maj, above

processSHA256Block :: SHA256State -> Get SHA256State
processSHA256Block !s00@(SHA256S a00 b00 c00 d00 e00 f00 g00 h00) = do
  (SHA256Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
               w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
               w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
               w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
               w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
               w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
               w60 w61 w62 w63) <- getSHA256Sched
  let s01 = step256 s00 0x428a2f98 w00
      s02 = step256 s01 0x71374491 w01
      s03 = step256 s02 0xb5c0fbcf w02
      s04 = step256 s03 0xe9b5dba5 w03
      s05 = step256 s04 0x3956c25b w04
      s06 = step256 s05 0x59f111f1 w05
      s07 = step256 s06 0x923f82a4 w06
      s08 = step256 s07 0xab1c5ed5 w07
      s09 = step256 s08 0xd807aa98 w08
      s10 = step256 s09 0x12835b01 w09
      s11 = step256 s10 0x243185be w10
      s12 = step256 s11 0x550c7dc3 w11
      s13 = step256 s12 0x72be5d74 w12
      s14 = step256 s13 0x80deb1fe w13
      s15 = step256 s14 0x9bdc06a7 w14
      s16 = step256 s15 0xc19bf174 w15
      s17 = step256 s16 0xe49b69c1 w16
      s18 = step256 s17 0xefbe4786 w17
      s19 = step256 s18 0x0fc19dc6 w18
      s20 = step256 s19 0x240ca1cc w19
      s21 = step256 s20 0x2de92c6f w20
      s22 = step256 s21 0x4a7484aa w21
      s23 = step256 s22 0x5cb0a9dc w22
      s24 = step256 s23 0x76f988da w23
      s25 = step256 s24 0x983e5152 w24
      s26 = step256 s25 0xa831c66d w25
      s27 = step256 s26 0xb00327c8 w26
      s28 = step256 s27 0xbf597fc7 w27
      s29 = step256 s28 0xc6e00bf3 w28
      s30 = step256 s29 0xd5a79147 w29
      s31 = step256 s30 0x06ca6351 w30
      s32 = step256 s31 0x14292967 w31
      s33 = step256 s32 0x27b70a85 w32
      s34 = step256 s33 0x2e1b2138 w33
      s35 = step256 s34 0x4d2c6dfc w34
      s36 = step256 s35 0x53380d13 w35
      s37 = step256 s36 0x650a7354 w36
      s38 = step256 s37 0x766a0abb w37
      s39 = step256 s38 0x81c2c92e w38
      s40 = step256 s39 0x92722c85 w39
      s41 = step256 s40 0xa2bfe8a1 w40
      s42 = step256 s41 0xa81a664b w41
      s43 = step256 s42 0xc24b8b70 w42
      s44 = step256 s43 0xc76c51a3 w43
      s45 = step256 s44 0xd192e819 w44
      s46 = step256 s45 0xd6990624 w45
      s47 = step256 s46 0xf40e3585 w46
      s48 = step256 s47 0x106aa070 w47
      s49 = step256 s48 0x19a4c116 w48
      s50 = step256 s49 0x1e376c08 w49
      s51 = step256 s50 0x2748774c w50
      s52 = step256 s51 0x34b0bcb5 w51
      s53 = step256 s52 0x391c0cb3 w52
      s54 = step256 s53 0x4ed8aa4a w53
      s55 = step256 s54 0x5b9cca4f w54
      s56 = step256 s55 0x682e6ff3 w55
      s57 = step256 s56 0x748f82ee w56
      s58 = step256 s57 0x78a5636f w57
      s59 = step256 s58 0x84c87814 w58
      s60 = step256 s59 0x8cc70208 w59
      s61 = step256 s60 0x90befffa w60
      s62 = step256 s61 0xa4506ceb w61
      s63 = step256 s62 0xbef9a3f7 w62
      s64 = step256 s63 0xc67178f2 w63
      SHA256S a64 b64 c64 d64 e64 f64 g64 h64 = s64
  return $! SHA256S (a00 + a64) (b00 + b64) (c00 + c64) (d00 + d64)
                    (e00 + e64) (f00 + f64) (g00 + g64) (h00 + h64)

{-# INLINE step256 #-}
step256 :: SHA256State -> Word32 -> Word32 -> SHA256State
step256 !(SHA256S a b c d e f g h) k w = SHA256S a' b' c' d' e' f' g' h'
 where
  t1 = h + bsig256_1 e + ch e f g + k + w
  t2 = bsig256_0 a + maj a b c
  h' = g
  g' = f
  f' = e
  e' = d + t1
  d' = c
  c' = b
  b' = a
  a' = t1 + t2

processSHA512Block :: SHA512State -> Get SHA512State
processSHA512Block !s00@(SHA512S a00 b00 c00 d00 e00 f00 g00 h00) = do
  (SHA512Sched w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
               w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
               w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
               w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
               w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
               w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
               w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
               w70 w71 w72 w73 w74 w75 w76 w77 w78 w79) <- getSHA512Sched
  let s01 = step512 s00 0x428a2f98d728ae22 w00
      s02 = step512 s01 0x7137449123ef65cd w01
      s03 = step512 s02 0xb5c0fbcfec4d3b2f w02
      s04 = step512 s03 0xe9b5dba58189dbbc w03
      s05 = step512 s04 0x3956c25bf348b538 w04
      s06 = step512 s05 0x59f111f1b605d019 w05
      s07 = step512 s06 0x923f82a4af194f9b w06
      s08 = step512 s07 0xab1c5ed5da6d8118 w07
      s09 = step512 s08 0xd807aa98a3030242 w08
      s10 = step512 s09 0x12835b0145706fbe w09
      s11 = step512 s10 0x243185be4ee4b28c w10
      s12 = step512 s11 0x550c7dc3d5ffb4e2 w11
      s13 = step512 s12 0x72be5d74f27b896f w12
      s14 = step512 s13 0x80deb1fe3b1696b1 w13
      s15 = step512 s14 0x9bdc06a725c71235 w14
      s16 = step512 s15 0xc19bf174cf692694 w15
      s17 = step512 s16 0xe49b69c19ef14ad2 w16
      s18 = step512 s17 0xefbe4786384f25e3 w17
      s19 = step512 s18 0x0fc19dc68b8cd5b5 w18
      s20 = step512 s19 0x240ca1cc77ac9c65 w19
      s21 = step512 s20 0x2de92c6f592b0275 w20
      s22 = step512 s21 0x4a7484aa6ea6e483 w21
      s23 = step512 s22 0x5cb0a9dcbd41fbd4 w22
      s24 = step512 s23 0x76f988da831153b5 w23
      s25 = step512 s24 0x983e5152ee66dfab w24
      s26 = step512 s25 0xa831c66d2db43210 w25
      s27 = step512 s26 0xb00327c898fb213f w26
      s28 = step512 s27 0xbf597fc7beef0ee4 w27
      s29 = step512 s28 0xc6e00bf33da88fc2 w28
      s30 = step512 s29 0xd5a79147930aa725 w29
      s31 = step512 s30 0x06ca6351e003826f w30
      s32 = step512 s31 0x142929670a0e6e70 w31
      s33 = step512 s32 0x27b70a8546d22ffc w32
      s34 = step512 s33 0x2e1b21385c26c926 w33
      s35 = step512 s34 0x4d2c6dfc5ac42aed w34
      s36 = step512 s35 0x53380d139d95b3df w35
      s37 = step512 s36 0x650a73548baf63de w36
      s38 = step512 s37 0x766a0abb3c77b2a8 w37
      s39 = step512 s38 0x81c2c92e47edaee6 w38
      s40 = step512 s39 0x92722c851482353b w39
      s41 = step512 s40 0xa2bfe8a14cf10364 w40
      s42 = step512 s41 0xa81a664bbc423001 w41
      s43 = step512 s42 0xc24b8b70d0f89791 w42
      s44 = step512 s43 0xc76c51a30654be30 w43
      s45 = step512 s44 0xd192e819d6ef5218 w44
      s46 = step512 s45 0xd69906245565a910 w45
      s47 = step512 s46 0xf40e35855771202a w46
      s48 = step512 s47 0x106aa07032bbd1b8 w47
      s49 = step512 s48 0x19a4c116b8d2d0c8 w48
      s50 = step512 s49 0x1e376c085141ab53 w49
      s51 = step512 s50 0x2748774cdf8eeb99 w50
      s52 = step512 s51 0x34b0bcb5e19b48a8 w51
      s53 = step512 s52 0x391c0cb3c5c95a63 w52
      s54 = step512 s53 0x4ed8aa4ae3418acb w53
      s55 = step512 s54 0x5b9cca4f7763e373 w54
      s56 = step512 s55 0x682e6ff3d6b2b8a3 w55
      s57 = step512 s56 0x748f82ee5defb2fc w56
      s58 = step512 s57 0x78a5636f43172f60 w57
      s59 = step512 s58 0x84c87814a1f0ab72 w58
      s60 = step512 s59 0x8cc702081a6439ec w59
      s61 = step512 s60 0x90befffa23631e28 w60
      s62 = step512 s61 0xa4506cebde82bde9 w61
      s63 = step512 s62 0xbef9a3f7b2c67915 w62
      s64 = step512 s63 0xc67178f2e372532b w63
      s65 = step512 s64 0xca273eceea26619c w64
      s66 = step512 s65 0xd186b8c721c0c207 w65
      s67 = step512 s66 0xeada7dd6cde0eb1e w66
      s68 = step512 s67 0xf57d4f7fee6ed178 w67
      s69 = step512 s68 0x06f067aa72176fba w68
      s70 = step512 s69 0x0a637dc5a2c898a6 w69
      s71 = step512 s70 0x113f9804bef90dae w70
      s72 = step512 s71 0x1b710b35131c471b w71
      s73 = step512 s72 0x28db77f523047d84 w72
      s74 = step512 s73 0x32caab7b40c72493 w73
      s75 = step512 s74 0x3c9ebe0a15c9bebc w74
      s76 = step512 s75 0x431d67c49c100d4c w75
      s77 = step512 s76 0x4cc5d4becb3e42b6 w76
      s78 = step512 s77 0x597f299cfc657e2a w77
      s79 = step512 s78 0x5fcb6fab3ad6faec w78
      s80 = step512 s79 0x6c44198c4a475817 w79
      SHA512S a80 b80 c80 d80 e80 f80 g80 h80 = s80
  return $! SHA512S (a00 + a80) (b00 + b80) (c00 + c80) (d00 + d80)
                    (e00 + e80) (f00 + f80) (g00 + g80) (h00 + h80)

{-# INLINE step512 #-}
step512 :: SHA512State -> Word64 -> Word64 -> SHA512State
step512 !(SHA512S a b c d e f g h) k w = SHA512S a' b' c' d' e' f' g' h'
 where
  t1 = h + bsig512_1 e + ch e f g + k + w
  t2 = bsig512_0 a + maj a b c
  h' = g
  g' = f
  f' = e
  e' = d + t1
  d' = c
  c' = b
  b' = a
  a' = t1 + t2

-- --------------------------------------------------------------------------
--
-- Run the routines
--
-- --------------------------------------------------------------------------

runSHA :: a -> (a -> Get a) -> ByteString -> a
runSHA s nextChunk input = runGet (getAll s) input
 where
  getAll s_in = do
    done <- isEmpty
    if done
      then return s_in
      else nextChunk s_in >>= getAll

runSHAIncremental :: a -> (a -> Get a) -> Decoder a
runSHAIncremental s nextChunk = runGetIncremental (getAll s)
 where
  getAll s_in = do
    done <- isEmpty
    if done
      then return s_in
      else nextChunk s_in >>= getAll

generic_complete :: (t -> [SBS.ByteString]) -> (a -> Put) -> Decoder a -> t
  -> Digest a
generic_complete pad synthesize decoder len =
  let decoder' = pushEndOfInput $ foldl' pushChunk decoder $ pad len
  in case decoder' of
       Fail _ _ _ -> error "Decoder is in Fail state."
       Partial _ -> error "Decoder is in Partial state."
       Done _ _ x -> Digest $ runPut $! synthesize x

-- |Compute the SHA-1 hash of the given ByteString. The output is guaranteed
-- to be exactly 160 bits, or 20 bytes, long. This is a good default for
-- programs that need a good, but not necessarily hyper-secure, hash function.
sha1 :: ByteString -> Digest SHA1State
sha1 bs_in = Digest bs_out
 where
  bs_pad = padSHA1 bs_in
  fstate = runSHA initialSHA1State processSHA1Block bs_pad
  bs_out = runPut $! synthesizeSHA1 fstate

-- |Similar to `sha1` but use an incremental interface. When the decoder has
-- been completely fed, `completeSha1Incremental` must be used so it can
-- finish successfully.
sha1Incremental :: Decoder SHA1State
sha1Incremental = runSHAIncremental initialSHA1State processSHA1Block

completeSha1Incremental :: Decoder SHA1State -> Int -> Digest SHA1State
completeSha1Incremental = generic_complete padSHA1Chunks synthesizeSHA1

-- |Compute the SHA-224 hash of the given ByteString. Note that SHA-224 and
-- SHA-384 differ only slightly from SHA-256 and SHA-512, and use truncated
-- versions of the resulting hashes. So using 224/384 may not, in fact, save
-- you very much ...
sha224 :: ByteString -> Digest SHA256State
sha224 bs_in = Digest bs_out
 where
  bs_pad = padSHA1 bs_in
  fstate = runSHA initialSHA224State processSHA256Block bs_pad
  bs_out = runPut $! synthesizeSHA224 fstate

-- |Similar to `sha224` but use an incremental interface. When the decoder has
-- been completely fed, `completeSha224Incremental` must be used so it can
-- finish successfully.
sha224Incremental :: Decoder SHA256State
sha224Incremental = runSHAIncremental initialSHA224State processSHA256Block

completeSha224Incremental :: Decoder SHA256State -> Int -> Digest SHA256State
completeSha224Incremental = generic_complete padSHA1Chunks synthesizeSHA224

-- |Compute the SHA-256 hash of the given ByteString. The output is guaranteed
-- to be exactly 256 bits, or 32 bytes, long. If your security requirements
-- are pretty serious, this is a good choice. For truly significant security
-- concerns, however, you might try one of the bigger options.
sha256 :: ByteString -> Digest SHA256State
sha256 bs_in = Digest bs_out
 where
  bs_pad = padSHA1 bs_in
  fstate = runSHA initialSHA256State processSHA256Block bs_pad
  bs_out = runPut $! synthesizeSHA256 fstate

-- |Similar to `sha256` but use an incremental interface. When the decoder has
-- been completely fed, `completeSha256Incremental` must be used so it can
-- finish successfully.
sha256Incremental :: Decoder SHA256State
sha256Incremental = runSHAIncremental initialSHA256State processSHA256Block

completeSha256Incremental :: Decoder SHA256State -> Int -> Digest SHA256State
completeSha256Incremental = generic_complete padSHA1Chunks synthesizeSHA256

-- |Compute the SHA-384 hash of the given ByteString. Yup, you guessed it,
-- the output will be exactly 384 bits, or 48 bytes, long.
sha384 :: ByteString -> Digest SHA512State
sha384 bs_in = Digest bs_out
 where
  bs_pad = padSHA512 bs_in
  fstate = runSHA initialSHA384State processSHA512Block bs_pad
  bs_out = runPut $! synthesizeSHA384 fstate

-- |Similar to `sha384` but use an incremental interface. When the decoder has
-- been completely fed, `completeSha384Incremental` must be used so it can
-- finish successfully.
sha384Incremental :: Decoder SHA512State
sha384Incremental = runSHAIncremental initialSHA384State processSHA512Block

completeSha384Incremental :: Decoder SHA512State -> Int -> Digest SHA512State
completeSha384Incremental = generic_complete padSHA512Chunks synthesizeSHA384

-- |For those for whom only the biggest hashes will do, this computes the
-- SHA-512 hash of the given ByteString. The output will be 64 bytes, or
-- 512 bits, long.
sha512 :: ByteString -> Digest SHA512State
sha512 bs_in = Digest bs_out
 where
  bs_pad = padSHA512 bs_in
  fstate = runSHA initialSHA512State processSHA512Block bs_pad
  bs_out = runPut $! synthesizeSHA512 fstate

-- |Similar to `sha512` but use an incremental interface. When the decoder has
-- been completely fed, `completeSha512Incremental` must be used so it can
-- finish successfully.
sha512Incremental :: Decoder SHA512State
sha512Incremental = runSHAIncremental initialSHA512State processSHA512Block

completeSha512Incremental :: Decoder SHA512State -> Int -> Digest SHA512State
completeSha512Incremental = generic_complete padSHA512Chunks synthesizeSHA512

-- --------------------------------------------------------------------------

-- | Compute an HMAC using SHA-1.
hmacSha1
  :: ByteString  -- ^ secret key
  -> ByteString  -- ^ message
  -> Digest SHA1State     -- ^ SHA-1 MAC
hmacSha1 = hmac sha1 64

-- | Compute an HMAC using SHA-224.
hmacSha224
  :: ByteString  -- ^ secret key
  -> ByteString  -- ^ message
  -> Digest SHA256State     -- ^ SHA-224 MAC
hmacSha224 = hmac sha224 64

-- | Compute an HMAC using SHA-256.
hmacSha256
  :: ByteString  -- ^ secret key
  -> ByteString  -- ^ message
  -> Digest SHA256State  -- ^ SHA-256 MAC
hmacSha256 = hmac sha256 64

-- | Compute an HMAC using SHA-384.
hmacSha384
  :: ByteString  -- ^ secret key
  -> ByteString  -- ^ message
  -> Digest SHA512State     -- ^ SHA-384 MAC
hmacSha384 = hmac sha384 128

-- | Compute an HMAC using SHA-512.
hmacSha512
  :: ByteString  -- ^ secret key
  -> ByteString  -- ^ message
  -> Digest SHA512State     -- ^ SHA-512 MAC
hmacSha512 = hmac sha512 128

-- --------------------------------------------------------------------------

hmac :: (ByteString -> Digest t) -> Int -> ByteString -> ByteString -> Digest t
hmac f bl k m = f (BS.append opad (bytestringDigest (f (BS.append ipad m))))
 where
  opad = BS.map (xor ov) k'
  ipad = BS.map (xor iv) k'
  ov = 0x5c :: Word8
  iv = 0x36 :: Word8

  k' = BS.append kt pad
   where
    kt  = if kn > bn then bytestringDigest (f k) else k
    pad = BS.replicate (bn - ktn) 0
    kn  = fromIntegral (BS.length k)
    ktn = fromIntegral (BS.length kt)
    bn  = fromIntegral bl

-- --------------------------------------------------------------------------
--
--                                OTHER
--
-- --------------------------------------------------------------------------


-- | Convert a digest to a string.
-- The digest is rendered as fixed with hexadecimal number.
showDigest :: Digest t -> String
showDigest (Digest bs) = showDigestBS bs

-- |Prints out a bytestring in hexadecimal. Just for convenience.
showDigestBS :: ByteString -> String
showDigestBS bs = foldr paddedShowHex [] (BS.unpack bs)
 where
   paddedShowHex x xs = intToDigit (fromIntegral (x `shiftR` 4))
                      : intToDigit (fromIntegral (x .&. 0xf))
                      : xs

-- | Convert a digest to an Integer.
integerDigest :: Digest t -> Integer
integerDigest (Digest bs) = BS.foldl' addShift 0 bs
 where addShift n y = (n `shiftL` 8) .|. fromIntegral y

-- | Convert a digest to a ByteString.
bytestringDigest :: Digest t -> ByteString
bytestringDigest (Digest bs) = bs
