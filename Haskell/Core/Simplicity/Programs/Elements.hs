{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement pure calculations used by Elements.
module Simplicity.Programs.Elements
  ( Lib(Lib), mkLib
  , Conf
  , calculateIssuanceEntropy, calculateAsset, calculateExplicitToken, calculateConfidentialToken
  , LibAssert(LibAssert), mkLibAssert
  , outpointHash, assetAmountHash, nonceHash, annexHash
  -- * Example instances
  , lib, libAssert
  -- * Reexports
  , Hash, Ctx8
  ) where

import Prelude hiding (Word, drop, not, subtract, take)

import Simplicity.Functor
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Arith
import Simplicity.Programs.Word
import Simplicity.Term.Core hiding (one)
import Simplicity.Programs.LibSecp256k1 hiding (Lib(Lib), mkLib, lib)
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 hiding ( Lib(Lib), lib
                                         , LibAssert(LibAssert), mkLibAssert, libAssert)

-- | A Simplicity type constructor for Elements confidential values.
type Conf a = Either Point a

-- | A collection of core Simplicity expressions for Elements calculations.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | An implementation of GenerateAssetEntropy from Element's @issuance.cpp@.
    calculateIssuanceEntropy :: term ((Hash, Word32), Hash) Hash

    -- | An implementation of CalculateAsset from Element's @issuance.cpp@.
  , calculateAsset :: term Hash Hash

    -- | An implementation of CalculateReissuanceToken for explicit values from Element's @issuance.cpp@.
  , calculateExplicitToken :: term Hash Hash

    -- | An implementation of CalculateReissuanceToken for confidential values from Element's @issuance.cpp@.
  , calculateConfidentialToken :: term Hash Hash
  }

-- | A collection of Simplicity with Assertions expressions for Elements calculations.
-- Use 'mkLibAssert' to construct an instance of this library.
data LibAssert term =
 LibAssert
  { -- | A hash of an optional parent genesis hash and an outpoint.
    outpointHash :: term (Ctx8, (S Word256, (Word256, Word32))) Ctx8
    -- | A hash of a confidential asset and amount.
  , assetAmountHash :: term (Ctx8, (Conf Word256, Conf Word64)) Ctx8
    -- | A hash of an optional nonce.
  , nonceHash :: term (Ctx8, S (Conf Word256)) Ctx8
    -- | A hash of an optional hash.
  , annexHash :: term (Ctx8, S Word256) Ctx8
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { calculateIssuanceEntropy = m calculateIssuanceEntropy
    , calculateAsset = m calculateAsset
    , calculateExplicitToken = m calculateExplicitToken
    , calculateConfidentialToken = m calculateConfidentialToken
    }

instance SimplicityFunctor LibAssert where
  sfmap m LibAssert{..} =
   LibAssert
    { outpointHash = m outpointHash
    , assetAmountHash = m assetAmountHash
    , nonceHash = m nonceHash
    , annexHash = m annexHash
    }

-- | Build the Elements 'Lib' library from its dependencies.
mkLib :: forall term. Core term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  lib@Lib{..} = Lib {
    calculateIssuanceEntropy = (unit >>> iv) &&& (take opHash &&& ih) >>> hashBlock

  , calculateAsset = (unit >>> iv) &&& (iden &&& (unit >>> zero word256)) >>> hashBlock

  , calculateExplicitToken = (unit >>> iv) &&& (iden &&& (unit >>> scribe (toWord256 (2^248)))) >>> hashBlock

  , calculateConfidentialToken = (unit >>> iv) &&& (iden &&& (unit >>> scribe (toWord256 (2*2^248)))) >>> hashBlock
  } where
    opHash :: term (Hash, Word32) Hash
    opHash = (unit >>> iv)
         &&& (((unit >>> iv) &&& (oh &&& (((drop (drop (ih &&& oh) &&& take (ih &&& oh)) &&& scribe (toWord32 (2^31))) &&& (unit >>> zero word64)) &&& (unit >>> scribe (toWord128 (256+32))))) >>> hashBlock)
          &&& (unit >>> scribe (toWord256 (2^255 + 256)))) >>> hashBlock

-- | An instance of the Elements 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: Core term => Lib term
lib = mkLib Sha256.lib

-- | Build the Elements 'LibAssert' library.
mkLibAssert :: forall term. Assert term => Sha256.LibAssert term -- ^ "Simplicity.Programs.Sha256"
                                        -> LibAssert term
mkLibAssert Sha256.LibAssert{..} = libAssert
 where
  libAssert@LibAssert{..} = LibAssert {
    outpointHash = ((ioh &&& oh >>> match (ih &&& take (zero word8) >>> ctx8Add1)
                                        ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32))
               &&& iioh >>> ctx8Add32) &&& iiih >>> ctx8Add4
  , assetAmountHash = (oh &&& ioh >>> assetHash) &&& iih >>> amountHash
  , nonceHash = ih &&& oh
            >>> match (ih &&& take (zero word8) >>> ctx8Add1)
                (ih &&& take (copair (take (copair (scribe (toWord8 0x02)) (scribe (toWord8 0x03))) &&& ih) ((unit >>> scribe (toWord8 0x01)) &&& iden))
                 >>> (oh &&& ioh >>> ctx8Add1) &&& iih >>> ctx8Add32)
  , annexHash = ih &&& oh
            >>> match (ih &&& take (zero word8) >>> ctx8Add1)
                      ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32)
  } where
    ctx8Add32 = ctx8Addn vector32
    ctx8Add8 = ctx8Addn vector8
    ctx8Add4 = ctx8Addn vector4
    assetHash = oh &&& drop (copair (take (copair (scribe (toWord8 0x0a)) (scribe (toWord8 0x0b))) &&& ih) ((unit >>> scribe (toWord8 0x01)) &&& iden))
            >>> (oh &&& ioh >>> ctx8Add1) &&& iih >>> ctx8Add32
    amountHash = ih &&& oh
             >>> match ((ih &&& take (take (copair (scribe (toWord8 0x08)) (scribe (toWord8 0x09)))) >>> ctx8Add1) &&& oih >>> ctx8Add32)
                       ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add8)

-- | An instance of the Elements 'LibAssert' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLibAssert' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
libAssert :: Assert term => LibAssert term
libAssert = mkLibAssert Sha256.libAssert
