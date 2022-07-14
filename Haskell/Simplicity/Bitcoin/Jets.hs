-- | This module provides a cannonical set of known jets for Simplicity for Bitcoin. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Bitcoin.Jets
  ( JetType
  , jetSubst
  , getTermStopCode, putTermStopCode
  , getTermLengthCode, putTermLengthCode
  , fastEval
  , jetMap
  -- * Re-exports
  , WrappedSimplicity, unwrap
  , Simplicity.Bitcoin.JetType.specification, Simplicity.Bitcoin.JetType.implementation
  , Semantics.FastEval
  ) where

import Prelude hiding (fail, drop, take)

import qualified Data.Map as Map
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.CoreJets (CoreJet, coreJetMap)
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Bitcoin.Dag hiding (jetSubst)
import qualified Simplicity.Bitcoin.Dag as Dag
import Simplicity.Bitcoin.Term
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.JetType
import Simplicity.Bitcoin.Primitive (PrimEnv, envTx, PubKey)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Serialization.BitString as BitString
import qualified Simplicity.Bitcoin.Semantics as Semantics
import qualified Simplicity.Bitcoin.Programs.TimeLock as TimeLock
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word

-- | A type of tokens for the cannonical set of known jets for Simplicity for Bitcoin. (At the moment this just consists of 'CoreJet's.)
--
-- The tokens themselves are not exported.  You are expected to use 'Simplicity.Dag.jetDag' to substitute known jets found in Simplicity expressions.
data JetType a b where
  CoreJet :: CoreJet a b -> JetType a b
  BitcoinJet :: BitcoinJet a b -> JetType a b
deriving instance Eq (JetType a b)
deriving instance Show (JetType a b)

data BitcoinJet a b where
  TimeLockJet :: TimeLockJet a b -> BitcoinJet a b
  TransactionJet :: TransactionJet a b -> BitcoinJet a b
deriving instance Eq (BitcoinJet a b)
deriving instance Show (BitcoinJet a b)

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

data TransactionJet a b where
  ScriptCMR :: TransactionJet () Word256
  InternalKey :: TransactionJet () PubKey
  CurrentIndex :: TransactionJet () Word32
  NumInputs :: TransactionJet () Word32
  NumOutputs :: TransactionJet () Word32
  LockTime :: TransactionJet () Word32
  OutputValue :: TransactionJet Word32 (Either () Word64)
  OutputScriptHash :: TransactionJet Word32 (Either () Word256)
  TotalOutputValue :: TransactionJet () Word64
  CurrentPrevOutpoint :: TransactionJet () (Word256,Word32)
  CurrentValue :: TransactionJet () Word64
  CurrentSequence :: TransactionJet () Word32
  InputPrevOutpoint :: TransactionJet Word32 (Either () (Word256,Word32))
  InputValue :: TransactionJet Word32 (Either () Word64)
  InputSequence :: TransactionJet Word32 (Either () Word32)
  TotalInputValue :: TransactionJet () Word64
  TapleafVersion :: TransactionJet () Word8
  Tapbranch :: TransactionJet Word8 (Either () Word256)
  Version :: TransactionJet () Word32

deriving instance Eq (TransactionJet a b)
deriving instance Show (TransactionJet a b)

specificationBitcoin :: (Assert term, Primitive term) => BitcoinJet a b -> term a b
specificationBitcoin (TimeLockJet x) = specificationTimeLock x
specificationBitcoin (TransactionJet x) = specificationTransaction x

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

specificationTransaction :: (Assert term, Primitive term) => TransactionJet a b -> term a b
specificationTransaction ScriptCMR = primitive Prim.ScriptCMR
specificationTransaction InternalKey = primitive Prim.InternalKey
specificationTransaction CurrentIndex = primitive Prim.CurrentIndex
specificationTransaction NumInputs = primitive Prim.NumInputs
specificationTransaction NumOutputs = primitive Prim.NumOutputs
specificationTransaction LockTime = primitive Prim.LockTime
specificationTransaction OutputValue = primitive Prim.OutputValue
specificationTransaction OutputScriptHash = primitive Prim.OutputScriptHash
specificationTransaction TotalOutputValue = primitive Prim.TotalOutputValue
specificationTransaction CurrentPrevOutpoint = primitive Prim.CurrentPrevOutpoint
specificationTransaction CurrentValue = primitive Prim.CurrentValue
specificationTransaction CurrentSequence = primitive Prim.CurrentSequence
specificationTransaction InputPrevOutpoint = primitive Prim.InputPrevOutpoint
specificationTransaction InputValue = primitive Prim.InputValue
specificationTransaction InputSequence = primitive Prim.InputSequence
specificationTransaction TotalInputValue = primitive Prim.TotalInputValue
specificationTransaction TapleafVersion = primitive Prim.TapleafVersion
specificationTransaction Tapbranch = primitive Prim.Tapbranch
specificationTransaction Version = primitive Prim.Version

implementationBitcoin :: BitcoinJet a b -> PrimEnv -> a -> Maybe b
implementationBitcoin (TimeLockJet x) = implementationTimeLock x
implementationBitcoin (TransactionJet x) = implementationTransaction x

implementationTimeLock :: TimeLockJet a b -> PrimEnv -> a -> Maybe b
implementationTimeLock CheckLockDistance env x | fromWord16 x <= fromIntegral (txLockDistance (envTx env)) = Just ()
                                               | otherwise = Nothing
implementationTimeLock CheckLockDuration env x | fromWord16 x <= fromIntegral (txLockDuration (envTx env)) = Just ()
                                               | otherwise = Nothing
implementationTimeLock TxLockHeight env () | txIsFinal (envTx env) && lock < 500000000 = Just . toWord32 . fromIntegral . sigTxLock . envTx $ env
                                           | otherwise = Just (toWord32 0)
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock TxLockTime env () | txIsFinal (envTx env) && 500000000 <= lock = Just . toWord32 . fromIntegral . sigTxLock . envTx $ env
                                           | otherwise = Just (toWord32 0)
 where
  lock = fromIntegral . sigTxLock . envTx $ env
implementationTimeLock TxLockDistance env () = Just . toWord16 . fromIntegral $ txLockDistance (envTx env)
implementationTimeLock TxLockDuration env () = Just . toWord16 . fromIntegral $ txLockDuration (envTx env)
implementationTimeLock TxIsFinal env () = Just $ toBit (txIsFinal (envTx env))

implementationTransaction :: TransactionJet a b -> PrimEnv -> a -> Maybe b
implementationTransaction x env i = Semantics.sem (specificationTransaction x) env i

getJetBitBitcoin :: (Monad m) => m Void -> m Bool -> m (SomeArrow BitcoinJet)
getJetBitBitcoin abort next = getPositive next >>= match
 where
  makeArrow p = return (SomeArrow p)
  match 2 = (someArrowMap TimeLockJet) <$> getJetBitTimeLock
  match 3 = (someArrowMap TransactionJet) <$> getJetBitTransaction
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
  getJetBitTransaction = getPositive next >>= matchTransaction
   where
    matchTransaction 1 = makeArrow ScriptCMR
    matchTransaction 2 = makeArrow InternalKey
    matchTransaction 3 = makeArrow CurrentIndex
    matchTransaction 4 = makeArrow NumInputs
    matchTransaction 5 = makeArrow NumOutputs
    matchTransaction 6 = makeArrow LockTime

    matchTransaction 8 = makeArrow OutputValue
    matchTransaction 9 = makeArrow OutputScriptHash
    matchTransaction 10 = makeArrow TotalOutputValue
    matchTransaction 11 = makeArrow CurrentPrevOutpoint
    matchTransaction 12 = makeArrow CurrentValue

    matchTransaction 14 = makeArrow CurrentSequence


    matchTransaction 17 = makeArrow InputPrevOutpoint
    matchTransaction 18 = makeArrow InputValue

    matchTransaction 20 = makeArrow InputSequence


    matchTransaction 23 = makeArrow TotalInputValue
    matchTransaction 24 = makeArrow TapleafVersion
    matchTransaction 25 = makeArrow Tapbranch
    matchTransaction 26 = makeArrow Version

putJetBitBitcoin :: BitcoinJet a b -> DList Bool
putJetBitBitcoin (TimeLockJet x) = putPositive 2 . putJetBitTimeLock x
putJetBitBitcoin (TransactionJet x) = putPositive 3 . putJetBitTransaction x

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

putJetBitTransaction :: TransactionJet a b -> DList Bool
putJetBitTransaction ScriptCMR           = putPositive 1
putJetBitTransaction InternalKey         = putPositive 2
putJetBitTransaction CurrentIndex        = putPositive 3
putJetBitTransaction NumInputs           = putPositive 4
putJetBitTransaction NumOutputs          = putPositive 5
putJetBitTransaction LockTime            = putPositive 6

putJetBitTransaction OutputValue         = putPositive 8
putJetBitTransaction OutputScriptHash    = putPositive 9
putJetBitTransaction TotalOutputValue    = putPositive 10
putJetBitTransaction CurrentPrevOutpoint = putPositive 11
putJetBitTransaction CurrentValue        = putPositive 12

putJetBitTransaction CurrentSequence     = putPositive 14


putJetBitTransaction InputPrevOutpoint   = putPositive 17
putJetBitTransaction InputValue          = putPositive 18

putJetBitTransaction InputSequence       = putPositive 20


putJetBitTransaction TotalInputValue     = putPositive 23
putJetBitTransaction TapleafVersion      = putPositive 24
putJetBitTransaction Tapbranch           = putPositive 25
putJetBitTransaction Version             = putPositive 26

bitcoinJetMap :: Map.Map Hash256 (SomeArrow BitcoinJet)
bitcoinJetMap = Map.fromList
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
    -- TransactionJet
  , mkAssoc (TransactionJet ScriptCMR)
  , mkAssoc (TransactionJet InternalKey)
  , mkAssoc (TransactionJet CurrentIndex)
  , mkAssoc (TransactionJet NumInputs)
  , mkAssoc (TransactionJet NumOutputs)
  , mkAssoc (TransactionJet LockTime)
  , mkAssoc (TransactionJet OutputValue)
  , mkAssoc (TransactionJet OutputScriptHash)
  , mkAssoc (TransactionJet TotalOutputValue)
  , mkAssoc (TransactionJet CurrentPrevOutpoint)
  , mkAssoc (TransactionJet CurrentValue)
  , mkAssoc (TransactionJet CurrentSequence)
  , mkAssoc (TransactionJet InputPrevOutpoint)
  , mkAssoc (TransactionJet InputValue)
  , mkAssoc (TransactionJet InputSequence)
  , mkAssoc (TransactionJet TotalInputValue)
  , mkAssoc (TransactionJet TapleafVersion)
  , mkAssoc (TransactionJet Tapbranch)
  , mkAssoc (TransactionJet Version)
  ]
 where
  mkAssoc :: (TyC a, TyC b) => BitcoinJet a b -> (Hash256, (SomeArrow BitcoinJet))
  mkAssoc jt = (identityRoot (specificationBitcoin jt), SomeArrow jt)

data MatcherInfo a b = MatcherInfo (IdentityRoot a b)

instance Simplicity.Bitcoin.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (CoreJet jt) = CoreJets.specification jt
  specification (BitcoinJet jt) = specificationBitcoin jt

  implementation (CoreJet jt) _env = CoreJets.implementation jt
  implementation (BitcoinJet jt) env = implementationBitcoin jt env

  matcher (MatcherInfo ir) = do
    SomeArrow jt <- Map.lookup (identityRoot ir) jetMap
    let (ira, irb) = reifyArrow ir
    let (jta, jtb) = reifyArrow jt
    -- If the error below is thrown it suggests there is some sort of type annotation mismatch in the map below
    case (equalTyReflect ira jta, equalTyReflect irb jtb) of
      (Just Refl, Just Refl) -> return jt
      otherwise -> error "mathcher{Simplicity.Bitcoin.Jets.JetType}: type match error"

  getJetBit abort next = do
   b <- next
   if b then someArrowMap BitcoinJet <$> getJetBitBitcoin abort next
        else someArrowMap CoreJet <$> CoreJets.getJetBit abort next

  putJetBit = go
   where
    go (CoreJet jt) = ([o]++) . CoreJets.putJetBit jt
    go (BitcoinJet jt) = ([i]++) . putJetBitBitcoin jt
    (o,i) = (False,True)

-- This map is used in the 'matcher' method above.
-- We have floated it out here to make sure the map is shared between invokations of the 'matcher' function.
jetMap :: Map.Map Hash256 (SomeArrow JetType)
jetMap = Map.union (someArrowMap CoreJet <$> coreJetMap) (someArrowMap BitcoinJet <$> bitcoinJetMap)

-- | Find all the expressions in a term that can be replaced with Bitcoin jets.
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

-- | 'fastEval' optimizes Simplicity evaluation using Bitcoin jets.
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
