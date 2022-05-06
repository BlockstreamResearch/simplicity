-- | This module provides a cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Elements.Jets
  ( JetType(..), ElementsJet(..), TimeLockJet(..), IssuanceJet(..)
  , jetSubst
  , getTermStopCode, putTermStopCode
  , getTermLengthCode, putTermLengthCode
  , fastEval
  , jetMap
  -- * Re-exports
  , WrappedSimplicity, unwrap
  , Simplicity.Elements.JetType.specification, Simplicity.Elements.JetType.implementation
  , Semantics.FastEval
  ) where

import Prelude hiding (fail, drop, take)

import Control.Monad (guard)
import Data.Either (isRight)
import qualified Data.Map as Map
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl))
import Data.Vector ((!?))
import Data.Void (Void, vacuous)
import Lens.Family2 (over, review)

import Simplicity.Digest
import Simplicity.CoreJets (CoreJet, coreJetMap)
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Elements.Dag hiding (jetSubst)
import qualified Simplicity.Elements.Dag as Dag
import Simplicity.Elements.Term
import Simplicity.Elements.DataTypes
import qualified Simplicity.Elements.JetType
import Simplicity.Elements.Primitive
import qualified Simplicity.Elements.Serialization.BitString as BitString
import qualified Simplicity.Elements.Semantics as Semantics
import qualified Simplicity.Elements.Programs.Issuance.Lib as Issuance
import qualified Simplicity.Elements.Programs.TimeLock as TimeLock
import Simplicity.MerkleRoot
import qualified Simplicity.Programs.Elements.Lib as Issuance
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word

-- | A type of tokens for the cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
--
-- The tokens themselves are not exported.  You are expected to use 'Simplicity.Dag.jetDag' to substitute known jets found in Simplicity expressions.
data JetType a b where
  CoreJet :: CoreJet a b -> JetType a b
  ElementsJet :: ElementsJet a b -> JetType a b
deriving instance Eq (JetType a b)
deriving instance Show (JetType a b)

data ElementsJet a b where
  TimeLockJet :: TimeLockJet a b -> ElementsJet a b
  IssuanceJet :: IssuanceJet a b -> ElementsJet a b
deriving instance Eq (ElementsJet a b)
deriving instance Show (ElementsJet a b)

data TimeLockJet a b where
  CheckLockHeight :: TimeLockJet TimeLock.Height ()
  CheckLockTime :: TimeLockJet TimeLock.Time ()
  CheckLockDistance :: TimeLockJet TimeLock.Distance ()
  CheckLockDuration :: TimeLockJet TimeLock.Duration ()
  TxLockHeight :: TimeLockJet () TimeLock.Height
  TxLockTime :: TimeLockJet () TimeLock.Time
  TxLockDistance :: TimeLockJet () TimeLock.Distance
  TxLockDuration :: TimeLockJet () TimeLock.Duration
  TxIsFinal :: TimeLockJet () TimeLock.Bit
deriving instance Eq (TimeLockJet a b)
deriving instance Show (TimeLockJet a b)

data IssuanceJet a b where
  InputIssuance :: IssuanceJet Word32 (S (S Bit))
  InputIssuanceAsset :: IssuanceJet Word32 (S (S Word256))
  InputIssuanceToken :: IssuanceJet Word32 (S (S Word256))
  InputIssuanceEntropy :: IssuanceJet Word32 (S (S Word256))
  CalculateIssuanceEntropy :: IssuanceJet ((Word256, Word32), Word256) Word256
  CalculateAsset :: IssuanceJet Word256 Word256
  CalculateExplicitToken :: IssuanceJet Word256 Word256
  CalculateConfidentialToken :: IssuanceJet Word256 Word256
deriving instance Eq (IssuanceJet a b)
deriving instance Show (IssuanceJet a b)

specificationElements :: (Assert term, Primitive term) => ElementsJet a b -> term a b
specificationElements (TimeLockJet x) = specificationTimeLock x
specificationElements (IssuanceJet x) = specificationIssuance x

specificationTimeLock :: (Assert term, Primitive term) => TimeLockJet a b -> term a b
specificationTimeLock CheckLockHeight = TimeLock.checkLockHeight
specificationTimeLock CheckLockTime = TimeLock.checkLockTime
specificationTimeLock CheckLockDistance = TimeLock.checkLockDistance
specificationTimeLock CheckLockDuration = TimeLock.checkLockDuration
specificationTimeLock TxLockHeight = TimeLock.txLockHeight
specificationTimeLock TxLockTime = TimeLock.txLockTime
specificationTimeLock TxLockDistance = TimeLock.txLockDistance
specificationTimeLock TxLockDuration = TimeLock.txLockDuration
specificationTimeLock TxIsFinal = TimeLock.txIsFinal

specificationIssuance :: (Assert term, Primitive term) => IssuanceJet a b -> term a b
specificationIssuance InputIssuance = Issuance.inputIssuance
specificationIssuance InputIssuanceAsset = Issuance.inputIssuanceAsset
specificationIssuance InputIssuanceToken = Issuance.inputIssuanceToken
specificationIssuance InputIssuanceEntropy = Issuance.inputIssuanceEntropy
specificationIssuance CalculateIssuanceEntropy = Issuance.calculateIssuanceEntropy
specificationIssuance CalculateAsset = Issuance.calculateAsset
specificationIssuance CalculateExplicitToken = Issuance.calculateExplicitToken
specificationIssuance CalculateConfidentialToken = Issuance.calculateConfidentialToken

implementationElements :: ElementsJet a b -> PrimEnv -> a -> Maybe b
implementationElements (TimeLockJet x) = implementationTimeLock x
implementationElements (IssuanceJet x) = implementationIssuance x

implementationTimeLock :: TimeLockJet a b -> PrimEnv -> a -> Maybe b
implementationTimeLock CheckLockHeight env x | txIsFinal (envTx env) = guard $ fromWord32 x <= 0
                                             | Left l <- parseLock lock = guard $ fromWord32 x <= fromIntegral l
                                             | otherwise = guard $ fromWord32 x <= 0
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock CheckLockTime env x | txIsFinal (envTx env) = guard $ fromWord32 x <= 0
                                           | Right l <- parseLock lock = guard $ fromWord32 x <= fromIntegral l
                                           | otherwise = guard $ fromWord32 x <= 0
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock CheckLockDistance env x | fromWord16 x <= fromIntegral (txLockDistance (envTx env)) = Just ()
                                               | otherwise = Nothing
implementationTimeLock CheckLockDuration env x | fromWord16 x <= fromIntegral (txLockDuration (envTx env)) = Just ()
                                               | otherwise = Nothing
implementationTimeLock TxLockHeight env () | txIsFinal (envTx env) = Just (toWord32 0)
                                           | Left l <- parseLock lock = Just . toWord32 $ fromIntegral l
                                           | otherwise = Just (toWord32 0)
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock TxLockTime env () | txIsFinal (envTx env) = Just (toWord32 0)
                                         | Right l <- parseLock lock = Just . toWord32 $ fromIntegral l
                                         | otherwise = Just (toWord32 0)
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock TxLockDistance env () = Just . toWord16 . fromIntegral $ txLockDistance (envTx env)
implementationTimeLock TxLockDuration env () = Just . toWord16 . fromIntegral $ txLockDuration (envTx env)
implementationTimeLock TxIsFinal env () = Just $ toBit (txIsFinal (envTx env))

implementationIssuance :: IssuanceJet a b -> PrimEnv -> a -> Maybe b
implementationIssuance InputIssuance env i = fmap (cast . fmap (cast . fmap toBit)) body
 where
  cast = maybe (Left ()) Right
  body = return $ fmap isRight . sigTxiIssuance <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance InputIssuanceEntropy env i = fmap (cast . fmap (cast . fmap fromHash)) body
 where
  cast = maybe (Left ()) Right
  fromHash = toWord256 . integerHash256
  body = return $ sigTxiIssuanceEntropy <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance InputIssuanceAsset env i = fmap (cast . fmap (cast . fmap fromHash)) body
 where
  cast = maybe (Left ()) Right
  fromHash = toWord256 . integerHash256
  body = return $ sigTxiIssuanceAsset <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance InputIssuanceToken env i = fmap (cast . fmap (cast . fmap fromHash)) body
 where
  cast = maybe (Left ()) Right
  fromHash = toWord256 . integerHash256
  body = return $ sigTxiIssuanceToken <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance CalculateIssuanceEntropy _ ((x,y), z) = Just (fromHash (calculateIssuanceEntropy op contract))
 where
  fromHash = toWord256 . integerHash256
  fromW256 = fromIntegral . fromWord256
  fromW32 = fromIntegral . fromWord32
  op = Outpoint (review (over be256) (fromW256 x)) (fromW32 y)
  contract = review (over be256) (fromW256 z)

implementationIssuance CalculateAsset _ x = Just (fromHash (calculateAsset entropy))
 where
  fromW256 = fromIntegral . fromWord256
  fromHash = toWord256 . integerHash256
  entropy = review (over be256) (fromW256 x)

implementationIssuance CalculateExplicitToken _ x = Just (fromHash (calculateToken (Amount (Explicit undefined)) entropy))
 where
  fromW256 = fromIntegral . fromWord256
  fromHash = toWord256 . integerHash256
  entropy = review (over be256) (fromW256 x)

implementationIssuance CalculateConfidentialToken _ x = Just (fromHash (calculateToken (Amount (Confidential undefined undefined)) entropy))
 where
  fromW256 = fromIntegral . fromWord256
  fromHash = toWord256 . integerHash256
  entropy = review (over be256) (fromW256 x)

getJetBitElements :: (Monad m) => m Void -> m Bool -> m (SomeArrow ElementsJet)
getJetBitElements abort next = getPositive next >>= match
 where
  makeArrow p = return (SomeArrow p)
  match 2 = (someArrowMap TimeLockJet) <$> getJetBitTimeLock
  match 3 = (someArrowMap IssuanceJet) <$> getJetBitIssuance
  match _ = vacuous abort
  getJetBitTimeLock = getPositive next >>= matchTimeLock
   where
    matchTimeLock 1 = makeArrow CheckLockHeight
    matchTimeLock 2 = makeArrow CheckLockTime
    matchTimeLock 3 = makeArrow CheckLockDistance
    matchTimeLock 4 = makeArrow CheckLockDuration
    matchTimeLock 5 = makeArrow TxLockHeight
    matchTimeLock 6 = makeArrow TxLockTime
    matchTimeLock 7 = makeArrow TxLockDistance
    matchTimeLock 8 = makeArrow TxLockDuration
    matchTimeLock 9 = makeArrow TxIsFinal
    matchTimeLock _ = vacuous abort
  getJetBitIssuance = getPositive next >>= matchIssuance
   where
    matchIssuance 1 = makeArrow InputIssuance
    matchIssuance 2 = makeArrow InputIssuanceAsset
    matchIssuance 3 = makeArrow InputIssuanceToken
    matchIssuance 4 = makeArrow InputIssuanceEntropy
    matchIssuance 5 = makeArrow CalculateIssuanceEntropy
    matchIssuance 6 = makeArrow CalculateAsset
    matchIssuance 7 = makeArrow CalculateExplicitToken
    matchIssuance 8 = makeArrow CalculateConfidentialToken

putJetBitElements :: ElementsJet a b -> DList Bool
putJetBitElements (TimeLockJet x) = putPositive 2 . putJetBitTimeLock x
putJetBitElements (IssuanceJet x) = putPositive 3 . putJetBitIssuance x

putJetBitTimeLock :: TimeLockJet a b -> DList Bool
putJetBitTimeLock CheckLockHeight   = putPositive 1
putJetBitTimeLock CheckLockTime     = putPositive 2
putJetBitTimeLock CheckLockDistance = putPositive 3
putJetBitTimeLock CheckLockDuration = putPositive 4
putJetBitTimeLock TxLockHeight   = putPositive 5
putJetBitTimeLock TxLockTime     = putPositive 6
putJetBitTimeLock TxLockDistance = putPositive 7
putJetBitTimeLock TxLockDuration = putPositive 8
putJetBitTimeLock TxIsFinal      = putPositive 9

putJetBitIssuance :: IssuanceJet a b -> DList Bool
putJetBitIssuance InputIssuance              = putPositive 1
putJetBitIssuance InputIssuanceAsset         = putPositive 2
putJetBitIssuance InputIssuanceToken         = putPositive 3
putJetBitIssuance InputIssuanceEntropy       = putPositive 4
putJetBitIssuance CalculateIssuanceEntropy   = putPositive 5
putJetBitIssuance CalculateAsset             = putPositive 6
putJetBitIssuance CalculateExplicitToken     = putPositive 7
putJetBitIssuance CalculateConfidentialToken = putPositive 8

elementsJetMap :: Map.Map Hash256 (SomeArrow ElementsJet)
elementsJetMap = Map.fromList
  [ -- TimeLockJet
    mkAssoc (TimeLockJet CheckLockHeight)
  , mkAssoc (TimeLockJet CheckLockTime)
  , mkAssoc (TimeLockJet CheckLockDistance)
  , mkAssoc (TimeLockJet CheckLockDuration)
  , mkAssoc (TimeLockJet TxLockHeight)
  , mkAssoc (TimeLockJet TxLockTime)
  , mkAssoc (TimeLockJet TxLockDistance)
  , mkAssoc (TimeLockJet TxLockDuration)
  , mkAssoc (TimeLockJet TxIsFinal)
    -- IssuanceJet
  , mkAssoc (IssuanceJet InputIssuance)
  , mkAssoc (IssuanceJet InputIssuanceAsset)
  , mkAssoc (IssuanceJet InputIssuanceToken)
  , mkAssoc (IssuanceJet InputIssuanceEntropy)
  , mkAssoc (IssuanceJet CalculateIssuanceEntropy)
  , mkAssoc (IssuanceJet CalculateAsset)
  , mkAssoc (IssuanceJet CalculateExplicitToken)
  , mkAssoc (IssuanceJet CalculateConfidentialToken)
  ]
 where
  mkAssoc :: (TyC a, TyC b) => ElementsJet a b -> (Hash256, (SomeArrow ElementsJet))
  mkAssoc jt = (identityRoot (specificationElements jt), SomeArrow jt)

data MatcherInfo a b = MatcherInfo (IdentityRoot a b)

instance Simplicity.Elements.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (CoreJet jt) = CoreJets.specification jt
  specification (ElementsJet jt) = specificationElements jt

  implementation (CoreJet jt) _env = CoreJets.implementation jt
  implementation (ElementsJet jt) env = implementationElements jt env

  matcher (MatcherInfo ir) = do
    SomeArrow jt <- Map.lookup (identityRoot ir) jetMap
    let (ira, irb) = reifyArrow ir
    let (jta, jtb) = reifyArrow jt
    -- If the error below is thrown it suggests there is some sort of type annotation mismatch in the map below
    case (equalTyReflect ira jta, equalTyReflect irb jtb) of
      (Just Refl, Just Refl) -> return jt
      otherwise -> error "mathcher{Simplicity.Elements.Jets.JetType}: type match error"

  getJetBit abort next = do
   b <- next
   if b then someArrowMap ElementsJet <$> getJetBitElements abort next
        else someArrowMap CoreJet <$> CoreJets.getJetBit abort next

  putJetBit = go
   where
    go (CoreJet jt) = ([o]++) . CoreJets.putJetBit jt
    go (ElementsJet jt) = ([i]++) . putJetBitElements jt
    (o,i) = (False,True)

-- This map is used in the 'matcher' method above.
-- We have floated it out here to make sure the map is shared between invokations of the 'matcher' function.
jetMap :: Map.Map Hash256 (SomeArrow JetType)
jetMap = Map.union (someArrowMap CoreJet <$> coreJetMap) (someArrowMap ElementsJet <$> elementsJetMap)

-- | Find all the expressions in a term that can be replaced with Elements jets.
-- Because discounted jets are not transparent, this replacement will change the CMR of the term.
-- In particular the CMR values passed to 'disconnect' may be different, and thus the result of
-- evaluation could change in the presence of 'disconnect'.
jetSubst :: (TyC a, TyC b) => JetDag JetType a b -> WrappedSimplicity a b
jetSubst = Dag.jetSubst

-- | This is an instance of 'BitString.getTermStopCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermStopCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermStopCode = BitString.getTermStopCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.getTermLengthCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermLengthCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermLengthCode = BitString.getTermLengthCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.putTermStopCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermStopCode :: (TyC a, TyC b) => JetDag JetType a b -> [Bool]
putTermStopCode = BitString.putTermStopCode

-- | This is an instance of 'BitString.putTermLengthCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermLengthCode :: (TyC a, TyC b) => JetDag JetType a b -> [Bool]
putTermLengthCode = BitString.putTermLengthCode

-- | 'fastEval' optimizes Simplicity evaluation using Elements jets.
-- Unlike using 'Simplicity.Dag.jetSubst', 'fastEval' will not modify the commitment roots and therefore will always return the same
-- result as 'sem' in the presence of 'disconnect'.
--
-- @
-- 'fastEval' t === 'sem' t
-- @
fastEval :: Semantics.FastEval JetType a b -> Semantics.PrimEnv -> a -> Maybe b
fastEval = Semantics.fastEval

instance Core MatcherInfo where
  iden = MatcherInfo iden
  unit = MatcherInfo unit
  injl (MatcherInfo ir) = MatcherInfo (injl ir)
  injr (MatcherInfo ir) = MatcherInfo (injr ir)
  drop (MatcherInfo ir) = MatcherInfo (drop ir)
  take (MatcherInfo ir) = MatcherInfo (take ir)
  pair (MatcherInfo irl) (MatcherInfo irr) = MatcherInfo (pair irl irr)
  match (MatcherInfo irl) (MatcherInfo irr) = MatcherInfo (match irl irr)
  comp (MatcherInfo irl) (MatcherInfo irr) = MatcherInfo (comp irl irr)

instance Assert MatcherInfo where
  assertl (MatcherInfo ir) h = MatcherInfo (assertl ir h)
  assertr h (MatcherInfo ir) = MatcherInfo (assertr h ir)
  fail b = MatcherInfo (fail b)

instance Primitive MatcherInfo where
  primitive p = MatcherInfo (primitive p)
