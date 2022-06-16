{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement Issuance functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.Issuance
  ( Lib(Lib), mkLib
  , issuance, issuanceEntropy, issuanceAsset, issuanceToken
  -- * Example instances
  , lib
  -- * Reexports
  , Bit, Hash
  ) where

import Prelude hiding (Word, all, drop, max, not, take)

import Simplicity.Functor
import Simplicity.Elements.Primitive
import Simplicity.Elements.Term hiding (one)
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Elements as Elements
import Simplicity.Programs.Elements hiding (Lib(Lib), mkLib, lib)
import Simplicity.Programs.Generic
import Simplicity.Programs.Word

-- | A collection of Simplicity expressions for Issuances.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Returns a False value if the inputs issuance is a new issuance.
    -- Returns a True value if the input's issuance is a re-issuance.
    -- Returns a 'Just Nothing' value if the input has no issuance.
    -- Returns a Nothing value of the input index is out of range.
    issuance :: term Word32 (S (S Bit))
    -- | Computes the entropy of a new issuance or returns the entropy of a reissuance.
    -- Returns a 'Just Nothing' value if the input has no issuance.
    -- Returns a Nothing value of the input index is out of range.
  , issuanceEntropy :: term Word32 (S (S Hash))
    -- | Computes the asset ID of an issuance.
    -- Returns a 'Just Nothing' value if the input has no issuance.
    -- Returns a Nothing value of the input index is out of range.
  , issuanceAsset :: term Word32 (S (S Hash))
    -- | Computes the reissuance token ID of an issuance.
    -- Returns a 'Just Nothing' value if the input has no issuance.
    -- Returns a Nothing value of the input index is out of range.
  , issuanceToken :: term Word32 (S (S Hash))
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    {
      issuance = m issuance
    , issuanceEntropy = m issuanceEntropy
    , issuanceAsset = m issuanceAsset
    , issuanceToken = m issuanceToken
    }

-- | Build the Issuance 'Lib' library from its dependencies.
mkLib :: forall term. (Core term, Primitive term) => Elements.Lib term -- ^ "Simplicity.Programs.Elements"
                                                  -> Lib term
mkLib Elements.Lib{..} = lib
 where
  lib@Lib{..} = Lib {
    issuance = primitive ReissuanceEntropy &&& primitive NewIssuanceContract
           >>> match (injl unit)
                     (flip match (injr (injr true))
                     (drop (copair (injl unit) (copair (injr (injl unit)) (injr (injr false))))))

  , issuanceEntropy = primitive ReissuanceEntropy &&& (primitive NewIssuanceContract &&& primitive InputPrevOutpoint)
                  >>> match (injl unit)
                      (flip match (take (injr (injr iden)))
                       (drop (match (injl unit) (match (injr (injl unit)) (ih &&& oh
                      >>> match (injl unit) (injr (injr calculateIssuanceEntropy)))))))

  , issuanceAsset = issuanceEntropy >>> copair (injl unit) (injr (copair (injl unit) (injr calculateAsset)))

  , issuanceToken = issuanceEntropy &&& primitive IssuanceAssetAmt
                >>> match (injl unit) (match (injr (injl unit)) (ih &&& oh
                >>> match (injl unit) (match (injl unit) (injr (injr
                      (match (drop calculateConfidentialToken) (drop calculateExplicitToken)))))))
  }

-- | An instance of the Issuance 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: (Core term, Primitive term) => Lib term
lib = mkLib Elements.lib
