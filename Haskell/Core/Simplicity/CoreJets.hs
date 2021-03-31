-- | This modules provides a GADT for a type of "core" Simplicity jets, i.e. those jets that don't use applicaiton specific primitives.
--
-- While the 'CoreJet' data type could be made an instance of 'Simplicity.JetType.JetType', we instead generally expect it to be used as a substructure of all jets used in each specific Simplicity application.
-- The other exports of this library aid in building an instance of 'Simplicity.JetType.JetType' for those that make use of 'CoreJet' as a substructure.
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.CoreJets
 ( CoreJet(..)
 , specification, coreJetMap, coreJetLookup
 , implementation
 , fastCoreEval
 , putJetBit, getJetBit
 , FastCoreEval
 ) where

import Prelude hiding (fail, drop, take, subtract)

import Control.Arrow (Kleisli(Kleisli), runKleisli)
import qualified Data.Map as Map
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.FFI.Jets as FFI
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Programs.Arith
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Term.Core

-- | A data type of (typed) tokens representing known "core" jets.
--
-- A core jet is a jet that doesn't use primitives.
data CoreJet a b where
  Add32 :: CoreJet (Word32, Word32) (Bit, Word32)
  FullAdd32 :: CoreJet (Bit, (Word32, Word32)) (Bit, Word32)
  Subtract32 :: CoreJet (Word32, Word32) (Bit, Word32)
  FullSubtract32 :: CoreJet (Bit, (Word32, Word32)) (Bit, Word32)
  Multiply32 :: CoreJet (Word32, Word32) Word64
  FullMultiply32 :: CoreJet ((Word32, Word32), (Word32, Word32)) Word64
  Sha256Block :: CoreJet (Sha256.Hash, Sha256.Block) Sha256.Hash

deriving instance Eq (CoreJet a b)
deriving instance Show (CoreJet a b)

-- | The specification of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.specification' method.
specification :: Assert term => CoreJet a b -> term a b
specification Add32 = add word32
specification FullAdd32 = full_add word32
specification Subtract32 = subtract word32
specification FullSubtract32 = full_subtract word32
specification Multiply32 = multiply word32
specification FullMultiply32 = full_multiply word32
specification Sha256Block = Sha256.hashBlock

-- | A jetted implementaiton for "core" jets.
--
-- @
-- 'implementation' x === 'runKleisli' ('specification' x)
-- @
implementation :: CoreJet a b -> a -> Maybe b
implementation Add32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementation FullAdd32 = \(c, (x, y)) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementation Subtract32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementation FullSubtract32 = \(b, (x, y)) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementation Multiply32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementation FullMultiply32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)
implementation Sha256Block = FFI.sha_256_block

-- | A canonical deserialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.getJetBit' method.
getJetBit :: (Monad m) => m Void -> m Bool -> m (SomeArrow CoreJet)
getJetBit abort next = (getWordJet & getFullWordJet) & (getHashJet & getEcJet)
 where
  getWordJet = (makeArrow Add32 & makeArrow Subtract32)
             & makeArrow Multiply32
  getFullWordJet = (makeArrow FullAdd32 & makeArrow FullSubtract32)
                 & makeArrow FullMultiply32
  getHashJet = makeArrow Sha256Block
  getEcJet = vacuous abort -- TODO
  l & r = next >>= \b -> if b then r else l
  -- makeArrow :: (TyC a, TyC b, Monad m) => (forall term. (Core term) => term a b) -> m (SomeArrow JetSpec)
  makeArrow p = return (SomeArrow p)

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit Add32            = ([o,o,o,o]++)
putJetBit Subtract32       = ([o,o,o,i]++)
putJetBit Multiply32       = ([o,o,i]++)
putJetBit FullAdd32        = ([o,i,o,o]++)
putJetBit FullSubtract32   = ([o,i,o,i]++)
putJetBit FullMultiply32   = ([o,i,i]++)
putJetBit Sha256Block      = ([i,o]++)

-- | A 'Map.Map' from the identity roots of the "core" jet specification to their corresponding token.
-- This can be used to help instantiate the 'Simplicity.JetType.matcher' method.
coreJetMap :: Map.Map Hash256 (SomeArrow CoreJet)
coreJetMap = Map.fromList
  [ mkAssoc Add32
  , mkAssoc Subtract32
  , mkAssoc Multiply32
  , mkAssoc FullAdd32
  , mkAssoc FullSubtract32
  , mkAssoc FullMultiply32
  , mkAssoc Sha256Block
  ]
 where
  mkAssoc :: (TyC a, TyC b) => CoreJet a b -> (Hash256, (SomeArrow CoreJet))
  mkAssoc jt = (identityRoot (specification jt), SomeArrow jt)

-- | Performs a lookup from `coreJetMap` from an `IdentityRoot`.
-- This operation preserves the Simplicity types.
coreJetLookup :: (TyC a, TyC b) => IdentityRoot a b -> Maybe (CoreJet a b)
coreJetLookup ir = do
  SomeArrow jt <- Map.lookup (identityRoot ir) coreJetMap
  let (ira, irb) = reifyArrow ir
  let (jta, jtb) = reifyArrow jt
  case (equalTyReflect ira jta, equalTyReflect irb jtb) of
    (Just Refl, Just Refl) -> return jt
    otherwise -> error "Simplicity.CoreJets.coreJetLookup: type match error"

(o, i) = (False, True)

-- | An Assert instance for 'fastCoreEval'.
data FastCoreEval a b = FastCoreEval { fastCoreEvalSem :: Kleisli Maybe a b
                                     , fastCoreEvalMatcher :: IdentityRoot a b
                                     }

-- | 'fastCoreEval' optimizes Simplicity with assertions evaluation using jets.
--
-- @
-- 'fastCoreEval' t === 'sem' t
-- @
fastCoreEval = runKleisli . fastCoreEvalSem

withJets :: (TyC a, TyC b) => FastCoreEval a b -> FastCoreEval a b
withJets ~(FastCoreEval _ ir) | Just cj <- coreJetLookup ir =
  FastCoreEval { fastCoreEvalSem = Kleisli $ implementation cj
               , fastCoreEvalMatcher = ir
               }
withJets fe | otherwise = fe

mkLeaf sComb jmComb = withJets $
  FastCoreEval { fastCoreEvalSem = sComb
               , fastCoreEvalMatcher = jmComb
               }

mkUnary sComb jmComb t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher t)
               }
mkBinary sComb jmComb s t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem s) (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher s) (fastCoreEvalMatcher t)
               }

instance Core FastCoreEval where
  iden = mkLeaf iden iden
  comp = mkBinary comp comp
  unit = mkLeaf unit unit
  injl = mkUnary injl injl
  injr = mkUnary injr injr
  match = mkBinary match match
  pair = mkBinary pair pair
  take = mkUnary take take
  drop = mkUnary drop drop

instance Assert FastCoreEval where
  assertl s h = mkUnary (flip assertl h) (flip assertl h) s
  assertr h t = mkUnary (assertr h) (assertr h) t
  fail b = mkLeaf (fail b) (fail b)
