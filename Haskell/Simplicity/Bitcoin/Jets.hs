-- | This module provides a canonical set of known jets for Simplicity for Bitcoin. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Bitcoin.Jets
  ( JetType(..)
  , asJet
  , jetSubst, pruneSubst
  , getTermLengthCode, putTermLengthCode
  , fastEval
  , jetMap
  -- * Re-exports
  , WrappedSimplicity, unwrap
  , Simplicity.Bitcoin.JetType.specification, Simplicity.Bitcoin.JetType.implementation
  , Simplicity.Bitcoin.JetType.getJetBit, Simplicity.Bitcoin.JetType.putJetBit
  , Simplicity.Bitcoin.JetType.jetCost
  , Semantics.FastEval
  ) where

import Prelude hiding (fail, drop, take)

import Control.Applicative ((<|>))
import qualified Data.Map as Map
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.CoreJets (CoreJet, coreJetMap, ConstWordContent(..), SomeConstWordContent(..))
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Bitcoin.Dag hiding (jetSubst, pruneSubst)
import qualified Simplicity.Bitcoin.Dag as Dag
import Simplicity.Bitcoin.Term
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.JetType
import Simplicity.Bitcoin.Primitive (PrimEnv, envTx, PubKey)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Serialization.BitString as BitString
import qualified Simplicity.Bitcoin.Semantics as Semantics
import qualified Simplicity.Bitcoin.Programs.TimeLock as TimeLock
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Prog
import Simplicity.MerkleRoot
import Simplicity.Programs.Word
import Simplicity.Serialization
import Simplicity.Tensor
import Simplicity.Tree
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word

-- | A type of tokens for the canonical set of known jets for Simplicity for Bitcoin. (At the moment this just consists of 'CoreJet's.)
--
-- The tokens themselves are not exported.  You are expected to use 'Simplicity.Dag.jetDag' to substitute known jets found in Simplicity expressions.
data JetType a b where
  ConstWordJet :: ConstWordContent b -> JetType () b
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
  CurrentAnnexHash :: TransactionJet () (Either () Word256)
  CurrentScriptSigHash :: TransactionJet () Word256
  InputPrevOutpoint :: TransactionJet Word32 (Either () (Word256,Word32))
  InputValue :: TransactionJet Word32 (Either () Word64)
  InputSequence :: TransactionJet Word32 (Either () Word32)
  InputAnnexHash :: TransactionJet Word32 (Either () (Either () Word256))
  InputScriptSigHash :: TransactionJet Word32 (Either () Word256)
  TotalInputValue :: TransactionJet () Word64
  TapleafVersion :: TransactionJet () Word8
  Tappath :: TransactionJet Word8 (Either () Word256)
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
specificationTransaction NumInputs = Prog.numInputs
specificationTransaction NumOutputs = Prog.numOutputs
specificationTransaction LockTime = primitive Prim.LockTime
specificationTransaction OutputValue = primitive Prim.OutputValue
specificationTransaction OutputScriptHash = primitive Prim.OutputScriptHash
specificationTransaction TotalOutputValue = primitive Prim.TotalOutputValue
specificationTransaction CurrentPrevOutpoint = Prog.currentPrevOutpoint
specificationTransaction CurrentValue = Prog.currentValue
specificationTransaction CurrentSequence = Prog.currentSequence
specificationTransaction CurrentAnnexHash = Prog.currentAnnexHash
specificationTransaction CurrentScriptSigHash = Prog.currentScriptSigHash
specificationTransaction InputPrevOutpoint = primitive Prim.InputPrevOutpoint
specificationTransaction InputValue = primitive Prim.InputValue
specificationTransaction InputSequence = primitive Prim.InputSequence
specificationTransaction InputAnnexHash = primitive Prim.InputAnnexHash
specificationTransaction InputScriptSigHash = primitive Prim.InputScriptSigHash
specificationTransaction TotalInputValue = primitive Prim.TotalInputValue
specificationTransaction TapleafVersion = primitive Prim.TapleafVersion
specificationTransaction Tappath = primitive Prim.Tappath
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
getJetBitBitcoin = getCatalogue bitcoinCatalogue
 where
  bitcoinCatalogue = Shelf
   [ Missing
   , someArrowMap TimeLockJet <$> timeLockCatalogue
   , someArrowMap TransactionJet <$> transactionCatalogue
   ]
  timeLockCatalogue = book
   [ SomeArrow CheckLockHeight
   , SomeArrow CheckLockTime
   , SomeArrow CheckLockDistance
   , SomeArrow CheckLockDuration
   , SomeArrow TxLockHeight
   , SomeArrow TxLockTime
   , SomeArrow TxLockDistance
   , SomeArrow TxLockDuration
   , SomeArrow TxIsFinal
   ]
  transactionCatalogue = Shelf
   [ Item $ SomeArrow ScriptCMR
   , Item $ SomeArrow InternalKey
   , Item $ SomeArrow CurrentIndex
   , Item $ SomeArrow NumInputs
   , Item $ SomeArrow NumOutputs
   , Item $ SomeArrow LockTime
   , Missing
   , Item $ SomeArrow OutputValue
   , Item $ SomeArrow OutputScriptHash
   , Item $ SomeArrow TotalOutputValue
   , Item $ SomeArrow CurrentPrevOutpoint
   , Item $ SomeArrow CurrentValue
   , Missing
   , Item $ SomeArrow CurrentSequence
   , Item $ SomeArrow CurrentAnnexHash
   , Item $ SomeArrow CurrentScriptSigHash
   , Item $ SomeArrow InputPrevOutpoint
   , Item $ SomeArrow InputValue
   , Missing
   , Item $ SomeArrow InputSequence
   , Item $ SomeArrow InputAnnexHash
   , Item $ SomeArrow InputScriptSigHash
   , Item $ SomeArrow TotalInputValue
   , Item $ SomeArrow TapleafVersion
   , Item $ SomeArrow Tappath
   , Item $ SomeArrow Version
   ]

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
putJetBitTransaction ScriptCMR            = putPositive 1
putJetBitTransaction InternalKey          = putPositive 2
putJetBitTransaction CurrentIndex         = putPositive 3
putJetBitTransaction NumInputs            = putPositive 4
putJetBitTransaction NumOutputs           = putPositive 5
putJetBitTransaction LockTime             = putPositive 6

putJetBitTransaction OutputValue          = putPositive 8
putJetBitTransaction OutputScriptHash     = putPositive 9
putJetBitTransaction TotalOutputValue     = putPositive 10
putJetBitTransaction CurrentPrevOutpoint  = putPositive 11
putJetBitTransaction CurrentValue         = putPositive 12

putJetBitTransaction CurrentSequence      = putPositive 14
putJetBitTransaction CurrentAnnexHash     = putPositive 15
putJetBitTransaction CurrentScriptSigHash = putPositive 16
putJetBitTransaction InputPrevOutpoint    = putPositive 17
putJetBitTransaction InputValue           = putPositive 18

putJetBitTransaction InputSequence        = putPositive 20
putJetBitTransaction InputAnnexHash       = putPositive 21
putJetBitTransaction InputScriptSigHash   = putPositive 22
putJetBitTransaction TotalInputValue      = putPositive 23
putJetBitTransaction TapleafVersion       = putPositive 24
putJetBitTransaction Tappath            = putPositive 25
putJetBitTransaction Version              = putPositive 26

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
  , mkAssoc (TransactionJet CurrentAnnexHash)
  , mkAssoc (TransactionJet CurrentScriptSigHash)
  , mkAssoc (TransactionJet InputPrevOutpoint)
  , mkAssoc (TransactionJet InputValue)
  , mkAssoc (TransactionJet InputSequence)
  , mkAssoc (TransactionJet InputAnnexHash)
  , mkAssoc (TransactionJet InputScriptSigHash)
  , mkAssoc (TransactionJet TotalInputValue)
  , mkAssoc (TransactionJet TapleafVersion)
  , mkAssoc (TransactionJet Tappath)
  , mkAssoc (TransactionJet Version)
  ]
 where
  mkAssoc :: (TyC a, TyC b) => BitcoinJet a b -> (Hash256, (SomeArrow BitcoinJet))
  mkAssoc jt = (identityHash (specificationBitcoin jt), SomeArrow jt)

data MatcherInfo a b = MatcherInfo (Product ConstWord IdentityRoot a b)

instance Simplicity.Bitcoin.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (ConstWordJet cw) = CoreJets.specificationConstWord cw
  specification (CoreJet jt) = CoreJets.specification jt
  specification (BitcoinJet jt) = specificationBitcoin jt

  implementation (CoreJet jt) _env = CoreJets.implementation jt
  implementation (BitcoinJet jt) env = implementationBitcoin jt env

  matcher (MatcherInfo (Product cw ir)) = (do
    SomeArrow jt <- Map.lookup (identityHash ir) jetMap
    let (ira, irb) = reifyArrow ir
    let (jta, jtb) = reifyArrow jt
    -- If the error below is thrown it suggests there is some sort of type annotation mismatch in the map below
    case (equalTyReflect ira jta, equalTyReflect irb jtb) of
      (Just Refl, Just Refl) -> return jt
      otherwise -> error "mathcher{Simplicity.Bitcoin.Jets.JetType}: type match error"
    ) <|> case cw of
      (ConstWord w v) -> return (ConstWordJet (ConstWordContent w v))
      otherwise -> Nothing

  getJetBit abort next = do
    b <- next
    if b then do
               c <- next
               if c then someArrowMap BitcoinJet <$> getJetBitBitcoin abort next
                    else someArrowMap CoreJet <$> CoreJets.getJetBit abort next
         else mkConstWordJet <$> CoreJets.getConstWordBit abort next
   where
     mkConstWordJet (SomeConstWordContent cw) = SomeArrow (ConstWordJet cw)

  putJetBit = go
   where
    go (ConstWordJet cw) = ([o]++) . CoreJets.putConstWordBit cw
    go (CoreJet jt) = ([i,o]++) . CoreJets.putJetBit jt
    go (BitcoinJet jt) = ([i,i]++) . putJetBitBitcoin jt
    (o,i) = (False,True)

  jetCost (ConstWordJet cw) = CoreJets.costConstWord cw
  jetCost (CoreJet jt) = CoreJets.jetCost jt
  jetCost (BitcoinJet jt) = error "Simplicity.Bitcoin.Jets.jetCost: :TODO: Implement jets for Bitcoin and benchmark them."

-- | Generate a 'Jet' using the 'Simplicity.Bitcoin.JetType.jetCost' and 'Simplicity.Bitcoin.JetType.specification' of a 'JetType'.
asJet :: (Jet term, TyC a, TyC b) => JetType a b -> term a b
asJet = Simplicity.Bitcoin.JetType.asJet

-- This map is used in the 'matcher' method above.
-- We have floated it out here to make sure the map is shared between invocations of the 'matcher' function.
jetMap :: Map.Map Hash256 (SomeArrow JetType)
jetMap = Map.union (someArrowMap CoreJet <$> coreJetMap) (someArrowMap BitcoinJet <$> bitcoinJetMap)

-- | Find all the expressions in a term that can be replaced with Bitcoin jets.
-- Because discounted jets are not transparent, this replacement will change the CMR of the term.
-- In particular the CMR values passed to 'disconnect' may be different, and thus the result of
-- evaluation could change in the presence of 'disconnect'.
jetSubst :: (TyC a, TyC b) => JetDag JetType a b -> WrappedSimplicity a b
jetSubst = Dag.jetSubst

-- | Performs 'jetSubst' and then evaluates the program in the given environment to prune unused case branches,
-- which transforms some case expressions into assertions.
-- The resulting expression should always have the same CMR as the expression that 'jetSubst' would return.
pruneSubst :: JetDag JetType () () -> PrimEnv -> Maybe (WrappedSimplicity () ())
pruneSubst prog env = Dag.pruneSubst prog env ()

-- | This is an instance of 'BitString.getTermLengthCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermLengthCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermLengthCode = BitString.getTermLengthCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.putTermLengthCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermLengthCode :: (TyC a, TyC b) => JetDag JetType a b -> ([Bool],[Bool])
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
