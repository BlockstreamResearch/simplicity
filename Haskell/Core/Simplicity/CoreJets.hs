-- | This modules provides a GADT for a type of "core" Simplicity jets, i.e. those jets that don't use applicaiton specific primitives.
--
-- While the 'CoreJet' data type could be made an instance of 'Simplicity.JetType.JetType', we instead generally expect it to be used as a substructure of all jets used in each specific Simplicity application.
-- The other exports of this library aid in building an instance of 'Simplicity.JetType.JetType' for those that make use of 'CoreJet' as a substructure.
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.CoreJets
 ( CoreJet
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
  WordJet :: WordJet a b -> CoreJet a b
  ArithJet :: ArithJet a b -> CoreJet a b
  HashJet :: HashJet a b -> CoreJet a b
  Secp256k1Jet :: Secp256k1Jet a b -> CoreJet a b
  SignatureJet :: SignatureJet a b -> CoreJet a b
deriving instance Eq (CoreJet a b)
deriving instance Show (CoreJet a b)

data WordJet a b where
deriving instance Eq (WordJet a b)
deriving instance Show (WordJet a b)

data ArithJet a b where
  Add32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullAdd32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Subtract32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullSubtract32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Multiply32 :: ArithJet (Word32, Word32) Word64
  FullMultiply32 :: ArithJet ((Word32, Word32), (Word32, Word32)) Word64
deriving instance Eq (ArithJet a b)
deriving instance Show (ArithJet a b)

data HashJet a b where
  Sha256Block :: HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash
deriving instance Eq (HashJet a b)
deriving instance Show (HashJet a b)

data Secp256k1Jet a b where
deriving instance Eq (Secp256k1Jet a b)
deriving instance Show (Secp256k1Jet a b)

data SignatureJet a b where
deriving instance Eq (SignatureJet a b)
deriving instance Show (SignatureJet a b)


-- | The specification of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.specification' method.
specification :: Assert term => CoreJet a b -> term a b
specification (ArithJet x) = specificationArith x
specification (HashJet x) = specificationHash x

specificationArith :: Assert term => ArithJet a b -> term a b
specificationArith Add32 = add word32
specificationArith FullAdd32 = full_add word32
specificationArith Subtract32 = subtract word32
specificationArith FullSubtract32 = full_subtract word32
specificationArith Multiply32 = multiply word32
specificationArith FullMultiply32 = full_multiply word32

specificationHash :: Assert term => HashJet a b -> term a b
specificationHash Sha256Block = Sha256.hashBlock

-- | A jetted implementaiton for "core" jets.
--
-- @
-- 'implementation' x === 'runKleisli' ('specification' x)
-- @
implementation :: CoreJet a b -> a -> Maybe b
implementation (ArithJet x) = implementationArith x
implementation (HashJet x) = implementationHash x

implementationArith :: ArithJet a b -> a -> Maybe b
implementationArith Add32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith FullAdd32 = \(c, (x, y)) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith Subtract32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementationArith FullSubtract32 = \(b, (x, y)) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementationArith Multiply32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementationArith FullMultiply32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)

implementationHash :: HashJet a b -> a -> Maybe b
implementationHash Sha256Block = FFI.sha_256_block

-- | A canonical deserialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.getJetBit' method.
getJetBit :: (Monad m) => m Void -> m Bool -> m (SomeArrow CoreJet)
getJetBit abort next =  getPositive next >>= match
 where
  makeArrow p = return (SomeArrow p)
  match 2 = (someArrowMap ArithJet) <$> getJetBitArith abort next
  match 3 = (someArrowMap HashJet) <$> getJetBitHash abort next
  getJetBitArith :: (Monad m) => m Void -> m Bool -> m (SomeArrow ArithJet)
  getJetBitArith abort next = getPositive next >>= matchArith
   where
    matchArith 2 = getPositive next >>= matchFullAdd
    matchArith 3 = getPositive next >>= matchAdd
    matchArith 7 = getPositive next >>= matchFullSubtract
    matchArith 8 = getPositive next >>= matchSubtract
    matchArith 12 = getPositive next >>= matchFullMultiply
    matchArith 13 = getPositive next >>= matchMultiply
    matchArth _ = vacuous abort
    matchAdd 5 = makeArrow Add32
    matchAdd _ = vacuous abort
    matchFullAdd 5 = makeArrow FullAdd32
    matchFullAdd _ = vacuous abort
    matchSubtract 5 = makeArrow Subtract32
    matchSubtract _ = vacuous abort
    matchFullSubtract 5 = makeArrow FullSubtract32
    matchFullSubtract _ = vacuous abort
    matchMultiply 5 = makeArrow Multiply32
    matchMultiply _ = vacuous abort
    matchFullMultiply 5 = makeArrow FullMultiply32
    matchFullMultiply _ = vacuous abort
  getJetBitHash :: (Monad m) => m Void -> m Bool -> m (SomeArrow HashJet)
  getJetBitHash abort next = getPositive next >>= matchHash
   where
    matchHash 1 = getPositive next >>= matchSha2
    matchHash _ = vacuous abort
    matchSha2 1 = makeArrow Sha256Block
    matchSha2 _ = vacuous abort

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit (ArithJet x) = putPositive 2 . putJetBitArith x
putJetBit (HashJet x) = putPositive 3 . putJetBitHash x

putJetBitArith :: ArithJet a b -> DList Bool
putJetBitArith FullAdd32      = putPositive 2 . putPositive 5
putJetBitArith Add32          = putPositive 3 . putPositive 5
putJetBitArith FullSubtract32 = putPositive 7 . putPositive 5
putJetBitArith Subtract32     = putPositive 8 . putPositive 5
putJetBitArith FullMultiply32 = putPositive 12 . putPositive 5
putJetBitArith Multiply32     = putPositive 13 . putPositive 5

putJetBitHash :: HashJet a b -> DList Bool
putJetBitHash Sha256Block = putPositive 1 . putPositive 1

-- | A 'Map.Map' from the identity roots of the "core" jet specification to their corresponding token.
-- This can be used to help instantiate the 'Simplicity.JetType.matcher' method.
coreJetMap :: Map.Map Hash256 (SomeArrow CoreJet)
coreJetMap = Map.fromList
  [ -- ArithJet
    mkAssoc (ArithJet Add32)
  , mkAssoc (ArithJet Subtract32)
  , mkAssoc (ArithJet Multiply32)
  , mkAssoc (ArithJet FullAdd32)
  , mkAssoc (ArithJet FullSubtract32)
  , mkAssoc (ArithJet FullMultiply32)
    -- HashJet
  , mkAssoc (HashJet Sha256Block)
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
