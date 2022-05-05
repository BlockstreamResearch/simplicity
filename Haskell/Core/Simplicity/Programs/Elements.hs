{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement pure calculations used by Elements.
module Simplicity.Programs.Elements
  ( Lib(Lib), mkLib
  , Conf
  , calculateIssuanceEntropy, calculateAsset, calculateExplicitToken, calculateConfidentialToken
  -- * Example instances
  , lib
  -- * Reexports
  , Hash
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
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)

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

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { calculateIssuanceEntropy = m calculateIssuanceEntropy
    , calculateAsset = m calculateAsset
    , calculateExplicitToken = m calculateExplicitToken
    , calculateConfidentialToken = m calculateConfidentialToken
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
