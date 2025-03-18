{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement pure calculations used by Bitcoin.
module Simplicity.Programs.Bitcoin
  ( Lib(Lib), mkLib
  , buildTapleafSimplicity, buildTapbranch
  , LibAssert(LibAssert), mkLibAssert
  , outpointHash, annexHash
  , buildTaptweak
  -- * Example instances
  , lib, libAssert
  -- * Reexports
  , Hash, Ctx8
  ) where

import Prelude hiding (Word, drop, not, subtract, take)
import Data.String (fromString)
import Lens.Family2 (over, review)

import Simplicity.Digest
import Simplicity.Functor
import Simplicity.LibSecp256k1.Spec (fieldOrder, groupOrder)
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Arith
import Simplicity.Programs.Word
import Simplicity.Term.Core hiding (one)
import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1
import Simplicity.Programs.LibSecp256k1 hiding (Lib(Lib), mkLib, lib)
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 hiding ( Lib(Lib), lib
                                         , LibAssert(LibAssert), mkLibAssert, libAssert)

-- | A collection of core Simplicity expressions for Bitcoin calculations.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { buildTapleafSimplicity :: term Hash Hash

    -- | Compute a tapbranch hash from two branches.
  , buildTapbranch :: term (Hash, Hash) Hash
  }

-- | A collection of Simplicity with Assertions expressions for Bitcoin calculations.
-- Use 'mkLibAssert' to construct an instance of this library.
data LibAssert term =
 LibAssert
  { -- | A hash of an outpoint.
    outpointHash :: term (Ctx8, (Word256, Word32)) Ctx8
    -- | A hash of an optional hash.
  , annexHash :: term (Ctx8, S Word256) Ctx8
    -- | Compute a taptweak hash from a pubkey and a hash.
  , buildTaptweak :: term (PubKey, Hash) PubKey
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { buildTapleafSimplicity = m buildTapleafSimplicity
    , buildTapbranch = m buildTapbranch
    }

instance SimplicityFunctor LibAssert where
  sfmap m LibAssert{..} =
   LibAssert
    { outpointHash = m outpointHash
    , annexHash = m annexHash
    , buildTaptweak = m buildTaptweak
    }

-- | Build the Bitcoin 'Lib' library from its dependencies.
mkLib :: forall term. Core term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  lib@Lib{..} = Lib {
    buildTapleafSimplicity = (unit >>> tapleafPrefix)
                         &&& ((unit >>> (simplicityVersion &&& scribe (toWord8 32))) &&& iden >>> full_shift word16 word256 >>>
                              (oh &&& ((((ih &&& (unit >>> scribe (toWord16 0x8000))) &&& (unit >>> zero word32)) &&& (unit >>> zero word64)) &&& (unit >>> scribe (toWord128 (512+16+256))))))
                         >>> hashBlock
  , buildTapbranch = ((unit >>> tapbranchPrefix)
                 &&& (lt word256 &&& iden >>> cond iden (ih &&& oh))
                 >>> hashBlock)
                 &&& (unit >>> scribe (toWord512 $ 2^511 + 1024)) >>> hashBlock
  } where
    tapleafPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "TapLeaf"
    tapbranchPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "TapBranch"
    simplicityVersion = scribe . toWord8 $ 0xbe

-- | An instance of the Bitcoin 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: Core term => Lib term
lib = mkLib Sha256.lib

-- | Build the Bitcoin 'LibAssert' library.
mkLibAssert :: forall term. Assert term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                        -> Sha256.LibAssert term -- ^ "Simplicity.Programs.Sha256"
                                        -> LibSecp256k1.Lib term -- ^ "Simplicity.Programs.Libsecp256k1"
                                        -> LibAssert term
mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert
 where
  libAssert@LibAssert{..} = LibAssert {
    outpointHash = (oh &&& ioh >>> ctx8Add32) &&& iih >>> ctx8Add4
  , annexHash = ih &&& oh
            >>> match (ih &&& take (zero word8) >>> ctx8Add1)
                      ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32)
  , buildTaptweak = assert (
                  (((assert (oh &&& (unit >>> scribe (toWord256 fieldOrder)) >>> lt256) >>> taptweakPrefix) &&& iden >>> hashBlock)
                &&& (unit >>> scribe (toWord512 $ 2^511 + 1024)) >>> hashBlock >>>
                   (assert (iden &&& (unit >>> scribe (toWord256 groupOrder)) >>> lt256) &&& iden) >>> drop generate)
                &&& assert ((unit >>> false) &&& oh >>> decompress)
                >>> gej_ge_add >>> gej_normalize) >>> oh
  } where
    lt256 = lt word256
    ctx8Add32 = ctx8Addn vector32
    ctx8Add8 = ctx8Addn vector8
    ctx8Add4 = ctx8Addn vector4
    taptweakPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "TapTweak"

-- | An instance of the Bitcoin 'LibAssert' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLibAssert' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
libAssert :: Assert term => LibAssert term
libAssert = mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib
