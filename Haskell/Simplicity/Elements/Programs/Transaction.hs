{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.Transaction
 ( Lib(Lib), lib
 , outputAssetAmount
 , inputAssetAmount
 , currentAssetAmount
 ) where

import Simplicity.Digest
import Simplicity.Elements.Primitive
import Simplicity.Elements.Term hiding (one)
import Simplicity.Functor
import Simplicity.Ty.Word

data Lib term =
 Lib
  { -- | Returns a pair of asset and amounts for the given output index.
    -- Returns Nothing of the index is out of range.
    outputAssetAmount :: term Word32 (S (Conf Word256, Conf Word64))
    -- | Returns a pair of asset and amounts for the given input index.
    -- Returns Nothing of the index is out of range.
  , inputAssetAmount :: term Word32 (S (Conf Word256, Conf Word64))
    -- | Returns a pair of asset and amounts of the current input.
  , currentAssetAmount :: term () (Conf Word256, Conf Word64)
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    {
      outputAssetAmount = m outputAssetAmount
    , inputAssetAmount = m inputAssetAmount
    , currentAssetAmount = m currentAssetAmount
    }

-- | Build the Transaction 'Lib' library.
lib :: forall term. (Assert term, Primitive term) => Lib term
lib = l
 where
  l@Lib{..} = Lib {
    outputAssetAmount = primitive OutputAmount &&& primitive OutputAsset
                    >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))

  , inputAssetAmount = primitive InputAmount &&& primitive InputAsset
                   >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))

  , currentAssetAmount = primitive CurrentAsset &&& primitive CurrentAmount
  }
