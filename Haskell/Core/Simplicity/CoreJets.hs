-- | This modules provides a GADT for a type of "core" Simplicity jets, i.e. those jets that don't use applicaiton specific primitives.
--
-- While the 'CoreJet' data type could be made an instance of 'Simplicity.JetType.JetType', we instead generally expect it to be used as a substructure of all jets used in each specific Simplicity application.
-- The other exports of this library aid in building an instance of 'Simplicity.JetType.JetType' for those that make use of 'CoreJet' as a substructure.
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.CoreJets
 ( CoreJet(..)
 , specification, coreJetMap
 , implementation
 , putJetBit, getJetBit
 ) where

import Prelude hiding (fail, drop, take)

import qualified Data.Map as Map
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.FFI.Jets as FFI
import Simplicity.MerkleRoot
import Simplicity.Serialization
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Programs.Word
import Simplicity.Term.Core

-- | A data type of (typed) tokens representing known "core" jets.
--
-- A core jet is a jet that doesn't use primitives.
data CoreJet a b where
  Adder32 :: CoreJet (Word32, Word32) (Bit, Word32)
  FullAdder32 :: CoreJet ((Word32, Word32), Bit) (Bit, Word32)
  Subtractor32 :: CoreJet (Word32, Word32) (Bit, Word32)
  FullSubtractor32 :: CoreJet ((Word32, Word32), Bit) (Bit, Word32)
  Multiplier32 :: CoreJet (Word32, Word32) Word64
  FullMultiplier32 :: CoreJet ((Word32, Word32), (Word32, Word32)) Word64
  Sha256HashBlock :: CoreJet (Sha256.Hash, Sha256.Block) Sha256.Hash

deriving instance Eq (CoreJet a b)
deriving instance Show (CoreJet a b)

-- | The specification of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.specification' method.
specification :: Assert term => CoreJet a b -> term a b
specification Adder32 = adder word32
specification FullAdder32 = fullAdder word32
specification Subtractor32 = subtractor word32
specification FullSubtractor32 = fullSubtractor word32
specification Multiplier32 = multiplier word32
specification FullMultiplier32 = fullMultiplier word32
specification Sha256HashBlock = Sha256.hashBlock

implementation :: CoreJet a b -> a -> Maybe b
implementation Adder32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementation FullAdder32 = \((x, y), c) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementation Subtractor32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementation FullSubtractor32 = \((x, y), b) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementation Multiplier32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementation FullMultiplier32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)
implementation Sha256HashBlock = FFI.sha256_hashBlock

-- | A canonical deserialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.getJetBit' method.
getJetBit :: (Monad m) => m Void -> m Bool -> m (SomeArrow CoreJet)
getJetBit abort next = (getWordJet & getFullWordJet) & (getHashJet & getEcJet)
 where
  getWordJet = (makeArrow Adder32 & makeArrow Subtractor32)
             & makeArrow Multiplier32
  getFullWordJet = (makeArrow FullAdder32 & makeArrow FullSubtractor32)
                 & makeArrow FullMultiplier32
  getHashJet = makeArrow Sha256HashBlock
  getEcJet = vacuous abort -- TODO
  l & r = next >>= \b -> if b then r else l
  -- makeArrow :: (TyC a, TyC b, Monad m) => (forall term. (Core term) => term a b) -> m (SomeArrow JetSpec)
  makeArrow p = return (SomeArrow p)

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit Adder32          = ([o,o,o,o]++)
putJetBit Subtractor32     = ([o,o,o,i]++)
putJetBit Multiplier32     = ([o,o,i]++)
putJetBit FullAdder32      = ([o,i,o,o]++)
putJetBit FullSubtractor32 = ([o,i,o,i]++)
putJetBit FullMultiplier32 = ([o,i,i]++)
putJetBit Sha256HashBlock  = ([i,o]++)

-- | A 'Map.Map' from the identity roots of the "core" jet specification to their corresponding token.
-- This can be used to help instantiate the 'Simplicity.JetType.matcher' method.
coreJetMap :: Map.Map Hash256 (SomeArrow CoreJet)
coreJetMap = Map.fromList
  [ mkAssoc Adder32
  , mkAssoc Subtractor32
  , mkAssoc Multiplier32
  , mkAssoc FullAdder32
  , mkAssoc FullSubtractor32
  , mkAssoc FullMultiplier32
  , mkAssoc Sha256HashBlock
  ]
 where
  mkAssoc :: (TyC a, TyC b) => CoreJet a b -> (Hash256, (SomeArrow CoreJet))
  mkAssoc jt = (identityRoot (specification jt), SomeArrow jt)

(o, i) = (False, True)
