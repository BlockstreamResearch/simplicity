{-# LANGUAGE GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expression and types that can be used for computing SHA-256 hashes.
-- Be aware that SHA-256 padding isn't provided and messages should be manually padded.
module Simplicity.Programs.Sha256
 ( Lib(Lib), lib
 , LibAssert(LibAssert), mkLibAssert
 -- * Operations
 , Block, Hash, Ctx8
 , iv, hashBlock
 , ctx8Init
 , ctx8Add1
 , ctx8Addn
 , ctx8AddBuffer
 , ctx8Finalize
 , hashLoop
 , ctx8InitTag
 , tapdataInit
 -- * Example instances
 , libAssert
 ) where

import Prelude hiding (Word, drop, not, take)
import Data.String (fromString)

import Simplicity.Digest
import Simplicity.Functor
import Simplicity.MerkleRoot
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import Simplicity.Term.Core hiding (one)

-- | In SHA-256, each block of data passed to the compression function is a 512-bit 'Word'.
type Block = Word512

-- | In SHA-256, the inital vector and hash value are 256-bit 'Word's.
type Hash = Word256

-- | A SHA-256 context (for bytes) consists of a buffer of less than 94 bytes, a counter for the number of compression functions invoked, and a midstate.
--
-- It is invalid for a context's counter to be greater than or equal to 2^55.
type Ctx8 = (Buffer63 Word8, (Word64, Word256))

-- | A collection of core Simplicity expressions for SHA-256.
-- Use 'lib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Simplicity expression for the constant function that returns the SHA-256 initial vector.
    iv :: term () Hash
    -- | Simplicity expression for the SHA-256 compression function which takes a midstate (or initial vector) and a message block and outputs a hash value (which is used as a midstate if there are further message blocks).
  , hashBlock :: term (Hash, Block) Hash
    -- | Initialize an empty 'Ctx8'.
  , ctx8Init :: term () Ctx8
    -- | Initialize a tapdata tagged sha256 context.
  , tapdataInit :: term () Ctx8
  }

data LibAssert term =
 LibAssert {
    -- | Append one byte to a 'Ctx8'.
    --
    -- This operation fails if the input or output 'Ctx8' is or would be invalid.
    ctx8Add1 :: term (Ctx8, Word8) Ctx8
    -- | Append a vector of bytes to a 'Ctx8'.
    --
    -- This operation fails if the input or output 'Ctx8' is or would be invalid.
  , ctx8Addn :: forall v. TyC v => Vector Word8 v -> term (Ctx8, v) Ctx8
    -- | Append a buffer of bytes to a 'Ctx8'.
    --
    -- This operation fails if the input or output 'Ctx8' is or would be invalid.
  , ctx8AddBuffer :: forall v b. TyC b => Buffer Word8 v b -> term (Ctx8, b) Ctx8
    -- | Append Sha-256 padding and finalize the hash
    --
    -- This operation fails if the input 'Ctx8' is invalid.
  , ctx8Finalize :: term Ctx8 Hash
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { iv = m iv
    , hashBlock = m hashBlock
    , ctx8Init = m ctx8Init
    , tapdataInit = m tapdataInit
    }

instance SimplicityFunctor LibAssert where
  sfmap m LibAssert{..} =
   LibAssert
    { ctx8Add1 = m ctx8Add1
    , ctx8Addn = m . ctx8Addn
    , ctx8AddBuffer = m . ctx8AddBuffer
    , ctx8Finalize = m ctx8Finalize
    }

-- | Build the Sha256 'Lib' library.
lib :: Core term => Lib term
lib = l
 where
  l@Lib{..} = Lib
   { iv = scribe . toWord256 $ 0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19
   , hashBlock = oh &&& compression
             >>> ((collate oooh &&& collate ooih)
             &&&  (collate oioh &&& collate oiih))
             &&& ((collate iooh &&& collate ioih)
             &&&  (collate iioh &&& collate iiih))
   , ctx8Init = buffer63Empty &&& (zero word64 &&& iv)
   , tapdataInit = buffer63Empty &&& (one word64 &&& tapdataPrefix)
   }
   where
    collate x = take x &&& drop x >>> add32
    compression = scribe32 k0 &&& iden >>> foldr (\k rec -> scribe32 k &&& step >>> rec) round ks
    k0:ks = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
            ,0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
            ,0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
            ,0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
            ,0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
            ,0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
            ,0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
            ,0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
    step = round &&& (drop (drop schedule))
    scribe32 x = scribe (toWord32 x)
    round = part1 >>> part2
     where
      part1 = ((t1 &&& io oooh) &&& io odiag)
          &&& io (bigDiag &&& idiag)
      part2 = ((t12 &&& ooih) &&& oih)
          &&& ((t1d &&& ioih) &&& iih)
      t1 = (oh &&& iio oooh >>> add32) &&& io (drop (iih &&& ((ooh >>> bigSigma1) &&& (ooh &&& diag >>> chWord32) >>> add32)) >>> add32) >>> add32
      t12 = take ((oih &&& ih >>> majWord32) &&& (take (oh &&& (ih >>> bigSigma0)) >>> add32)) >>> add32
      t1d = oooh &&& iooh >>> add32
      bigSigma0 = rotateW32 (-2) &&& rotateW32 (-13) &&& rotateW32 (-22) >>> xor_xorWord32
      bigSigma1 = rotateW32 (-6) &&& rotateW32 (-11) &&& rotateW32 (-25) >>> xor_xorWord32
      chWord32 = bitwise_ch word32
      majWord32 = bitwise_maj word32
    schedule = (take part1 &&& (take idiag &&& (take iiih &&& drop oooh)))
           &&& (drop part1 &&& (drop idiag &&& (drop iiih &&& smallSigma)))
     where
      part1 = odiag &&& bigDiag
      smallSigma = (take (oo (oh &&& (ih >>> smallSigma0))) >>> add32) &&& (drop (ooih &&& (iioh >>> smallSigma1)) >>> add32) >>> add32
      smallSigma0 = rotateW32 (-7)  &&& rotateW32 (-18) &&& shiftW32 (-3)  >>> xor_xorWord32
      smallSigma1 = rotateW32 (-17) &&& rotateW32 (-19) &&& shiftW32 (-10) >>> xor_xorWord32
    oo x = take (take x)
    io x = drop (take x)
    iio x = drop (io x)
    diag = oih &&& ioh
    odiag = take diag
    idiag = drop diag
    bigDiag = oiih &&& iooh
    add32 = add word32 >>> ih
    xor_xorWord32 = bitwise_xor_xor word32
    rotateW32 = rotate_const word32
    shiftW32 = shift_const_by false word32
    buffer63Empty = bufferEmpty buffer63
    tapdataPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "TapData"

-- | Given an "array", which is a term that maps an index @w@ to a vector of bytes @v@, returning nothing if the index is out of bounds,
-- hash all the bytes of the "array" in seqeuenced until the end of the array (i.e. upto the first index where the "array" term returns nothing).
--
-- A context value of type "c" is available to be pass into the "array" term.
hashLoop :: (Assert term, TyC c, TyC w, TyC v) => Vector Word8 v -> Word w -> term (c, w) (S v) -> term (c, Ctx8) Ctx8
hashLoop v = \w array ->
  let body = take array &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> ctx8Addv))
  in forWhile w body >>> copair iden iden
 where
  ctx8Addv = ctx8Addn libAssert v

ctx8InitTag :: Core term => String -> term () Ctx8
ctx8InitTag tag = buffer63Empty &&& (one word64 &&& prefix)
 where
  prefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ tag
  buffer63Empty = bufferEmpty buffer63

-- | Build the Sha256 'LibAssert' library.
mkLibAssert :: Assert term => Lib term -> LibAssert term
mkLibAssert Lib{..}  = l
 where
  l@LibAssert{..} = LibAssert
   { ctx8Add1 = (ooh &&& ih >>> buffer63Snoc) &&& oih
            >>> match ((unit >>> buffer63Empty) &&& ((drop (take (increment word64) >>> assertl ih cmrFail0)) &&& (iih &&& oh >>> hashBlock)))
                      iden
            >>> (verifyNumCompression &&& iden) >>> ih
   , ctx8Addn = \v -> case v of
                  SingleV -> ctx8Add1
                  (DoubleV v) -> let rec = ctx8Addn v in
                                 (oh &&& ioh >>> rec) &&& iih >>> rec
   , ctx8AddBuffer = \b -> case b of
                       SingleB -> ih &&& oh >>> match (drop (iden &&& verifyNumCompression >>> oh)) (ih &&& oh >>> ctx8Add1)
                       (DoubleB b) -> (ioh &&& oh >>> match ih (ih &&& oh >>> ctx8Addn (bufferVector b))) &&& iih >>> ctx8AddBuffer b
     -- We clear the context's counter (after verifying it) because the counter is allowed to "overflow" during padding.
   , ctx8Finalize = ((oh &&& ((verifyNumCompression >>> zero word64) &&& iih)) &&& (unit >>> scribe (toWord64 (2^63))) >>> ctx8Add8 >>> (take pad063 &&& iih))
                &&& ((take buffer63Size >>> left_pad_low word8 vector8) &&& drop (take (shift_const_by false word64 6)) >>> add64 >>> shift_const_by false word64 3)
                >>> oih &&& (oooh &&& (take oioh &&& (take (take iioh) &&& ih))) >>> hashBlock
   }
   where
    buffer63Empty = bufferEmpty buffer63
    ctx8Add8 = ctx8Addn vector8
    verifyNumCompression = assert (ioh &&& (unit >>> scribe (toWord64 (2^55))) >>> lt word64)
    add64 = add word64 >>> ih
    buffer63Snoc = bufferSnoc buffer63
    buffer63Size = ((false &&& false) &&& (take (copair false true) &&& drop (take (copair false true))))
               &&& drop (drop ((take (copair false true) &&& drop (take (copair false true))) &&& drop (drop (take (copair false true) &&& drop (copair false true)))))
    pad063 = oh &&& drop pad031 >>> match (ih &&& take (zero word256)) iden
    pad031 = oh &&& drop pad015 >>> match (ih &&& take (zero word128)) iden
    pad015 = oh &&& drop pad07 >>> match (ih &&& take (zero word64)) iden
    pad07 = oh &&& drop pad03 >>> match (ih &&& take (zero word32)) iden
    pad03 = oh &&& drop pad01 >>> match (ih &&& take (zero word16)) iden
    pad01 = copair (zero word16) (iden &&& (unit >>> zero word8))

-- | An instance of the Sha256 'LibAssert' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
libAssert :: Assert term => LibAssert term
libAssert = mkLibAssert lib
