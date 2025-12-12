-- | This module provides a canonical set of known jets for Simplicity for Bitcoin. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Bitcoin.Jets
  ( JetType(..), BitcoinJet(..), SigHashJet(..), TimeLockJet(..), TransactionJet(..)
  , bitcoinCatalogue
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
import Control.Monad (guard)
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl))
import Data.Serialize (runPut, put, putWord8)
import Data.String (fromString)
import Data.Vector ((!?))
import Data.Void (Void, vacuous)
import Lens.Family2 ((^..), over, review)

import Simplicity.Digest
import Simplicity.CoreJets hiding (BitcoinJet)
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Bitcoin.Benchmarks
import Simplicity.Bitcoin.Dag hiding (jetSubst, pruneSubst)
import qualified Simplicity.Bitcoin.Dag as Dag
import Simplicity.Bitcoin.Term
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.JetType
import Simplicity.Bitcoin.Primitive (PrimEnv, PubKey, primEnvHash, envTx, envTap)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Serialization.BitString as BitString
import qualified Simplicity.Bitcoin.Semantics as Semantics
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import qualified Simplicity.Bitcoin.Programs.TimeLock as TimeLock
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Prog
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.Sha256.Lib (Ctx8)
import qualified Simplicity.Programs.Bitcoin.Lib as Prog
import Simplicity.Programs.Word
import Simplicity.Serialization
import Simplicity.Tensor
import Simplicity.Tree
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Sha256
import Simplicity.Ty.Word
import qualified Simplicity.Word as W
import Simplicity.Weight

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
  SigHashJet :: SigHashJet a b -> BitcoinJet a b
  TimeLockJet :: TimeLockJet a b -> BitcoinJet a b
  TransactionJet :: TransactionJet a b -> BitcoinJet a b
deriving instance Eq (BitcoinJet a b)
deriving instance Show (BitcoinJet a b)

data SigHashJet a b where
  SigAllHash :: SigHashJet () Word256
  TxHash :: SigHashJet () Word256
  TapEnvHash :: SigHashJet () Word256
  OutputsHash :: SigHashJet () Word256
  InputsHash :: SigHashJet () Word256
  InputUtxosHash :: SigHashJet () Word256
  OutputHash :: SigHashJet Word32 (S Word256)
  OutputValuesHash :: SigHashJet () Word256
  OutputScriptsHash :: SigHashJet () Word256
  InputHash :: SigHashJet Word32 (S Word256)
  InputOutpointsHash :: SigHashJet () Word256
  InputSequencesHash :: SigHashJet () Word256
  InputAnnexesHash :: SigHashJet () Word256
  InputScriptSigsHash :: SigHashJet () Word256
  InputUtxoHash :: SigHashJet Word32 (S Word256)
  InputValuesHash :: SigHashJet () Word256
  InputScriptsHash :: SigHashJet () Word256
  TapleafHash :: SigHashJet () Word256
  TappathHash :: SigHashJet () Word256
  OutpointHash :: SigHashJet (Ctx8, (Word256, Word32)) Ctx8
  AnnexHash :: SigHashJet (Ctx8, S Word256) Ctx8
  BuildTapleafSimplicity :: SigHashJet Word256 Word256
  BuildTapbranch :: SigHashJet (Word256, Word256) Word256
  BuildTaptweak :: SigHashJet (PubKey, Word256) PubKey
deriving instance Eq (SigHashJet a b)
deriving instance Show (SigHashJet a b)

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
  Fee :: TransactionJet () Word64
  OutputValue :: TransactionJet Word32 (Either () Word64)
  OutputScriptHash :: TransactionJet Word32 (Either () Word256)
  TotalOutputValue :: TransactionJet () Word64
  CurrentPrevOutpoint :: TransactionJet () (Word256,Word32)
  CurrentValue :: TransactionJet () Word64
  CurrentScriptHash :: TransactionJet () Word256
  CurrentSequence :: TransactionJet () Word32
  CurrentAnnexHash :: TransactionJet () (Either () Word256)
  CurrentScriptSigHash :: TransactionJet () Word256
  InputPrevOutpoint :: TransactionJet Word32 (Either () (Word256,Word32))
  InputValue :: TransactionJet Word32 (Either () Word64)
  InputScriptHash :: TransactionJet Word32 (S Word256)
  InputSequence :: TransactionJet Word32 (Either () Word32)
  InputAnnexHash :: TransactionJet Word32 (Either () (Either () Word256))
  InputScriptSigHash :: TransactionJet Word32 (Either () Word256)
  TotalInputValue :: TransactionJet () Word64
  TapleafVersion :: TransactionJet () Word8
  Tappath :: TransactionJet Word8 (Either () Word256)
  Version :: TransactionJet () Word32
  TransactionId :: TransactionJet () Word256
deriving instance Eq (TransactionJet a b)
deriving instance Show (TransactionJet a b)

specificationBitcoin :: (Assert term, Primitive term) => BitcoinJet a b -> term a b
specificationBitcoin (SigHashJet x) = specificationSigHash x
specificationBitcoin (TimeLockJet x) = specificationTimeLock x
specificationBitcoin (TransactionJet x) = specificationTransaction x

specificationSigHash :: (Assert term, Primitive term) => SigHashJet a b -> term a b
specificationSigHash SigAllHash = SigHash.sigAllHash
specificationSigHash TxHash = SigHash.txHash
specificationSigHash TapEnvHash = SigHash.tapEnvHash
specificationSigHash OutputsHash = SigHash.outputsHash
specificationSigHash InputsHash = SigHash.inputsHash
specificationSigHash InputUtxosHash = SigHash.inputUtxosHash
specificationSigHash OutputHash = SigHash.outputHash
specificationSigHash OutputValuesHash = SigHash.outputValuesHash
specificationSigHash OutputScriptsHash = SigHash.outputScriptsHash
specificationSigHash InputHash = SigHash.inputHash
specificationSigHash InputOutpointsHash = SigHash.inputOutpointsHash
specificationSigHash InputSequencesHash = SigHash.inputSequencesHash
specificationSigHash InputAnnexesHash = SigHash.inputAnnexesHash
specificationSigHash InputScriptSigsHash = SigHash.inputScriptSigsHash
specificationSigHash InputUtxoHash = SigHash.inputUtxoHash
specificationSigHash InputValuesHash = SigHash.inputValuesHash
specificationSigHash InputScriptsHash = SigHash.inputScriptsHash
specificationSigHash TapleafHash = SigHash.tapleafHash
specificationSigHash TappathHash = SigHash.tappathHash
specificationSigHash OutpointHash = Prog.outpointHash
specificationSigHash AnnexHash = Prog.annexHash
specificationSigHash BuildTapleafSimplicity = Prog.buildTapleafSimplicity
specificationSigHash BuildTapbranch = Prog.buildTapbranch
specificationSigHash BuildTaptweak = Prog.buildTaptweak

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
specificationTransaction TotalOutputValue = Prog.totalOutputValue
specificationTransaction CurrentPrevOutpoint = Prog.currentPrevOutpoint
specificationTransaction CurrentValue = Prog.currentValue
specificationTransaction CurrentScriptHash = Prog.currentScriptHash
specificationTransaction CurrentSequence = Prog.currentSequence
specificationTransaction CurrentAnnexHash = Prog.currentAnnexHash
specificationTransaction CurrentScriptSigHash = Prog.currentScriptSigHash
specificationTransaction InputPrevOutpoint = primitive Prim.InputPrevOutpoint
specificationTransaction InputValue = primitive Prim.InputValue
specificationTransaction InputScriptHash = primitive Prim.InputScriptHash
specificationTransaction InputSequence = primitive Prim.InputSequence
specificationTransaction InputAnnexHash = primitive Prim.InputAnnexHash
specificationTransaction InputScriptSigHash = primitive Prim.InputScriptSigHash
specificationTransaction TotalInputValue = Prog.totalInputValue
specificationTransaction Fee = Prog.fee
specificationTransaction TapleafVersion = primitive Prim.TapleafVersion
specificationTransaction Tappath = primitive Prim.Tappath
specificationTransaction Version = primitive Prim.Version
specificationTransaction TransactionId = primitive Prim.TransactionId

implementationBitcoin :: BitcoinJet a b -> PrimEnv -> a -> Maybe b
implementationBitcoin (SigHashJet x) = implementationSigHash x
implementationBitcoin (TimeLockJet x) = implementationTimeLock x
implementationBitcoin (TransactionJet x) = implementationTransaction x

implementationSigHash :: SigHashJet a b -> PrimEnv -> a -> Maybe b
implementationSigHash SigAllHash env _ = Just . toWord256 . integerHash256 $ primEnvHash env
implementationSigHash TxHash env _ = Just . toWord256 . integerHash256 $ txHash (envTx env)
implementationSigHash TapEnvHash env _ = Just . toWord256 . integerHash256 $ tapEnvHash (envTap env)
implementationSigHash OutputsHash env _ = Just . toWord256 . integerHash256 $ outputsHash (envTx env)
implementationSigHash InputsHash env _ = Just . toWord256 . integerHash256 $ inputsHash (envTx env)
implementationSigHash InputUtxosHash env _ = Just . toWord256 . integerHash256 $ inputUtxosHash (envTx env)
implementationSigHash OutputHash env i = Just . fmap (toWord256 . integerHash256 . outputHash) . maybe (Left ()) Right
                                       $ sigTxOut (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash OutputValuesHash env _ = Just . toWord256 . integerHash256 $ outputValuesHash (envTx env)
implementationSigHash OutputScriptsHash env _ = Just . toWord256 . integerHash256 $ outputScriptsHash (envTx env)
implementationSigHash InputHash env i = Just . fmap (toWord256 . integerHash256 . inputHash) . maybe (Left ()) Right
                                      $ sigTxIn (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash InputOutpointsHash env _ = Just . toWord256 . integerHash256 $ inputOutpointsHash (envTx env)
implementationSigHash InputSequencesHash env _ = Just . toWord256 . integerHash256 $ inputSequencesHash (envTx env)
implementationSigHash InputAnnexesHash env _ = Just . toWord256 . integerHash256 $ inputAnnexesHash (envTx env)
implementationSigHash InputScriptSigsHash env _ = Just . toWord256 . integerHash256 $ inputScriptSigsHash (envTx env)
implementationSigHash InputUtxoHash env i = Just . fmap (toWord256 . integerHash256 . outputHash . sigTxiTxo) . maybe (Left ()) Right
                                          $ sigTxIn (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash InputValuesHash env _ = Just . toWord256 . integerHash256 $ inputValuesHash (envTx env)
implementationSigHash InputScriptsHash env _ = Just . toWord256 . integerHash256 $ inputScriptsHash (envTx env)
implementationSigHash TapleafHash env _ = Just . toWord256 . integerHash256 $ tapleafHash (envTap env)
implementationSigHash TappathHash env _ = Just . toWord256 . integerHash256 $ tappathHash (envTap env)
implementationSigHash OutpointHash _env (ctx, op) = toCtx8 <$> (flip ctxAdd (runPut (putOutpointBE (cast op))) =<< fromCtx8 ctx)
 where
  cast (h, i) = Outpoint (review (over be256) (fromW256 h)) (fromW32 i)
  fromW256 = fromIntegral . fromWord256
  fromW32 = fromIntegral . fromWord32
implementationSigHash AnnexHash _env (ctx, mw256) = toCtx8 <$> (flip ctxAdd (runPut . putMW256 $ mw256) =<< fromCtx8 ctx)
 where
  putMW256 (Left _) = putWord8 0x00
  putMW256 (Right w256) = putWord8 0x01 >> put (fromIntegral (fromWord256 w256) :: W.Word256)
implementationSigHash BuildTapleafSimplicity _env cmr = Just . toWord256 . integerHash256 . bsHash . runPut
                                                      $ put tag >> put tag >> putWord8 tapleafSimplicityVersion >> putWord8 32 >> put (fromW256 cmr)
 where
  tag = bsHash (fromString "TapLeaf")
  tapleafSimplicityVersion = 0xbe
  fromW256 :: Word256 -> W.Word256
  fromW256 = fromIntegral . fromWord256

implementationSigHash BuildTapbranch _env (wa,wb) = Just . toWord256 . integerHash256 . bsHash . runPut
                                                  $ put tag >> put tag >> put min >> put max
 where
  a = fromW256 wa
  b = fromW256 wb
  min = if a < b then a else b
  max = if a < b then b else a
  tag = bsHash (fromString "TapBranch")
  fromW256 :: Word256 -> W.Word256
  fromW256 = fromIntegral . fromWord256
implementationSigHash BuildTaptweak _env (key,h) = cast <$> taptweak pk h0
 where
  pk = Schnorr.PubKey (fromW256 key)
  h0 = review (over be256) (fromW256 h)
  cast (Schnorr.PubKey k) = toWord256 . toInteger $ k
  fromW256 :: Word256 -> W.Word256
  fromW256 = fromIntegral . fromWord256

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

implementationTransaction :: TransactionJet a b -> PrimEnv -> a -> Maybe b
implementationTransaction TotalOutputValue env _ = Just . toWord64 . fromIntegral $ txTotalOutputValue (envTx env)
implementationTransaction TotalInputValue env _ = Just . toWord64 . fromIntegral $ txTotalInputValue (envTx env)
implementationTransaction Fee env _ = Just . toWord64 . fromIntegral $ txFee (envTx env)
implementationTransaction x env i = Semantics.sem (specificationTransaction x) env i

getJetBitBitcoin :: (Monad m) => m Void -> m Bool -> m (SomeArrow BitcoinJet)
getJetBitBitcoin = getCatalogue bitcoinCatalogue

bitcoinCatalogue :: Catalogue (SomeArrow BitcoinJet)
bitcoinCatalogue = Shelf
 [ someArrowMap SigHashJet <$> sigHashCatalogue
 , someArrowMap TimeLockJet <$> timeLockCatalogue
 , someArrowMap TransactionJet <$> transactionCatalogue
 ]
sigHashCatalogue = book
 [ SomeArrow SigAllHash
 , SomeArrow TxHash
 , SomeArrow TapEnvHash
 , SomeArrow OutputsHash
 , SomeArrow InputsHash
 , SomeArrow InputUtxosHash
 , SomeArrow OutputHash
 , SomeArrow OutputValuesHash
 , SomeArrow OutputScriptsHash
 , SomeArrow InputHash
 , SomeArrow InputOutpointsHash
 , SomeArrow InputSequencesHash
 , SomeArrow InputAnnexesHash
 , SomeArrow InputScriptSigsHash
 , SomeArrow InputUtxoHash
 , SomeArrow InputValuesHash
 , SomeArrow InputScriptsHash
 , SomeArrow TapleafHash
 , SomeArrow TappathHash
 , SomeArrow OutpointHash
 , SomeArrow AnnexHash
 , SomeArrow BuildTapleafSimplicity
 , SomeArrow BuildTapbranch
 , SomeArrow BuildTaptweak
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
transactionCatalogue = book
 [ SomeArrow ScriptCMR
 , SomeArrow InternalKey
 , SomeArrow CurrentIndex
 , SomeArrow NumInputs
 , SomeArrow NumOutputs
 , SomeArrow LockTime
 , SomeArrow Fee
 , SomeArrow OutputValue
 , SomeArrow OutputScriptHash
 , SomeArrow TotalOutputValue
 , SomeArrow CurrentPrevOutpoint
 , SomeArrow CurrentValue
 , SomeArrow CurrentScriptHash
 , SomeArrow CurrentSequence
 , SomeArrow CurrentAnnexHash
 , SomeArrow CurrentScriptSigHash
 , SomeArrow InputPrevOutpoint
 , SomeArrow InputValue
 , SomeArrow InputScriptHash
 , SomeArrow InputSequence
 , SomeArrow InputAnnexHash
 , SomeArrow InputScriptSigHash
 , SomeArrow TotalInputValue
 , SomeArrow TapleafVersion
 , SomeArrow Tappath
 , SomeArrow Version
 , SomeArrow TransactionId
 ]

putJetBitBitcoin :: BitcoinJet a b -> DList Bool
putJetBitBitcoin (SigHashJet x) = putPositive 1 . putJetBitSigHash x
putJetBitBitcoin (TimeLockJet x) = putPositive 2 . putJetBitTimeLock x
putJetBitBitcoin (TransactionJet x) = putPositive 3 . putJetBitTransaction x

putJetBitSigHash :: SigHashJet a b -> DList Bool
putJetBitSigHash SigAllHash             = putPositive 1
putJetBitSigHash TxHash                 = putPositive 2
putJetBitSigHash TapEnvHash             = putPositive 3
putJetBitSigHash OutputsHash            = putPositive 4
putJetBitSigHash InputsHash             = putPositive 5
putJetBitSigHash InputUtxosHash         = putPositive 6
putJetBitSigHash OutputHash             = putPositive 7
putJetBitSigHash OutputValuesHash       = putPositive 8
putJetBitSigHash OutputScriptsHash      = putPositive 9
putJetBitSigHash InputHash              = putPositive 10
putJetBitSigHash InputOutpointsHash     = putPositive 11
putJetBitSigHash InputSequencesHash     = putPositive 12
putJetBitSigHash InputAnnexesHash       = putPositive 13
putJetBitSigHash InputScriptSigsHash    = putPositive 14
putJetBitSigHash InputUtxoHash          = putPositive 15
putJetBitSigHash InputValuesHash        = putPositive 16
putJetBitSigHash InputScriptsHash       = putPositive 17
putJetBitSigHash TapleafHash            = putPositive 18
putJetBitSigHash TappathHash            = putPositive 19
putJetBitSigHash OutpointHash           = putPositive 20
putJetBitSigHash AnnexHash              = putPositive 21
putJetBitSigHash BuildTapleafSimplicity = putPositive 22
putJetBitSigHash BuildTapbranch         = putPositive 23
putJetBitSigHash BuildTaptweak          = putPositive 24

putJetBitTimeLock :: TimeLockJet a b -> DList Bool
putJetBitTimeLock CheckLockHeight   = putPositive 1
putJetBitTimeLock CheckLockTime     = putPositive 2
putJetBitTimeLock CheckLockDistance = putPositive 3
putJetBitTimeLock CheckLockDuration = putPositive 4
putJetBitTimeLock TxLockHeight      = putPositive 5
putJetBitTimeLock TxLockTime        = putPositive 6
putJetBitTimeLock TxLockDistance    = putPositive 7
putJetBitTimeLock TxLockDuration    = putPositive 8
putJetBitTimeLock TxIsFinal         = putPositive 9

putJetBitTransaction :: TransactionJet a b -> DList Bool
putJetBitTransaction ScriptCMR            = putPositive 1
putJetBitTransaction InternalKey          = putPositive 2
putJetBitTransaction CurrentIndex         = putPositive 3
putJetBitTransaction NumInputs            = putPositive 4
putJetBitTransaction NumOutputs           = putPositive 5
putJetBitTransaction LockTime             = putPositive 6
putJetBitTransaction Fee                  = putPositive 7
putJetBitTransaction OutputValue          = putPositive 8
putJetBitTransaction OutputScriptHash     = putPositive 9
putJetBitTransaction TotalOutputValue     = putPositive 10
putJetBitTransaction CurrentPrevOutpoint  = putPositive 11
putJetBitTransaction CurrentValue         = putPositive 12
putJetBitTransaction CurrentScriptHash    = putPositive 13
putJetBitTransaction CurrentSequence      = putPositive 14
putJetBitTransaction CurrentAnnexHash     = putPositive 15
putJetBitTransaction CurrentScriptSigHash = putPositive 16
putJetBitTransaction InputPrevOutpoint    = putPositive 17
putJetBitTransaction InputValue           = putPositive 18
putJetBitTransaction InputScriptHash      = putPositive 19
putJetBitTransaction InputSequence        = putPositive 20
putJetBitTransaction InputAnnexHash       = putPositive 21
putJetBitTransaction InputScriptSigHash   = putPositive 22
putJetBitTransaction TotalInputValue      = putPositive 23
putJetBitTransaction TapleafVersion       = putPositive 24
putJetBitTransaction Tappath              = putPositive 25
putJetBitTransaction Version              = putPositive 26
putJetBitTransaction TransactionId        = putPositive 27

bitcoinJetMap :: Map.Map Hash256 (SomeArrow BitcoinJet)
bitcoinJetMap = Map.fromList . fmap mkAssoc $ toList bitcoinCatalogue
 where
  mkAssoc :: SomeArrow BitcoinJet -> (Hash256, (SomeArrow BitcoinJet))
  mkAssoc wrapped@(SomeArrow jt) = (identityHash (specificationBitcoin jt), wrapped)

data MatcherInfo a b = MatcherInfo (Product ConstWord IdentityRoot a b)

instance Simplicity.Bitcoin.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (ConstWordJet cw) = CoreJets.specificationConstWord cw
  specification (CoreJet jt) = CoreJets.specification jt
  specification (BitcoinJet jt) = specificationBitcoin jt

  implementation (ConstWordJet cw) _env = CoreJets.implementationConstWord cw
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

  jetCost (ConstWordJet cw) = jetCostConstWord cw
  jetCost (CoreJet jt) = jetCostCore jt
  jetCost (BitcoinJet jt) = jetCostBitcoin jt

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

-- | Returns the cost of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
jetCostConstWord :: ConstWordContent b -> Weight
jetCostConstWord (ConstWordContent w _) = milli (wordSize w)

-- | The costs of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.jetCost' method.
jetCostCore :: CoreJet a b -> Weight
jetCostCore (WordJet x) = jetCostWord x
jetCostCore (ArithJet x) = jetCostArith x
jetCostCore (HashJet x) = jetCostHash x
jetCostCore (Secp256k1Jet x) = jetCostSecp256k1 x
jetCostCore (SignatureJet x) = jetCostSignature x
jetCostCore (CoreJets.BitcoinJet x) = jetCostCoreBitcoin x

jetCostWord :: WordJet a b -> Weight
jetCostWord Verify = cost "Verify"
jetCostWord Low1 = cost "Low1"
jetCostWord Low8 = cost "Low8"
jetCostWord Low16 = cost "Low16"
jetCostWord Low32 = cost "Low32"
jetCostWord Low64 = cost "Low64"
jetCostWord High1 = cost "High1"
jetCostWord High8 = cost "High8"
jetCostWord High16 = cost "High16"
jetCostWord High32 = cost "High32"
jetCostWord High64 = cost "High64"
jetCostWord Complement1 = cost "Complement1"
jetCostWord Complement8 = cost "Complement8"
jetCostWord Complement16 = cost "Complement16"
jetCostWord Complement32 = cost "Complement32"
jetCostWord Complement64 = cost "Complement64"
jetCostWord And1 = cost "And1"
jetCostWord And8 = cost "And8"
jetCostWord And16 = cost "And16"
jetCostWord And32 = cost "And32"
jetCostWord And64 = cost "And64"
jetCostWord Or1 = cost "Or1"
jetCostWord Or8 = cost "Or8"
jetCostWord Or16 = cost "Or16"
jetCostWord Or32 = cost "Or32"
jetCostWord Or64 = cost "Or64"
jetCostWord Xor1 = cost "Xor1"
jetCostWord Xor8 = cost "Xor8"
jetCostWord Xor16 = cost "Xor16"
jetCostWord Xor32 = cost "Xor32"
jetCostWord Xor64 = cost "Xor64"
jetCostWord Maj1 = cost "Maj1"
jetCostWord Maj8 = cost "Maj8"
jetCostWord Maj16 = cost "Maj16"
jetCostWord Maj32 = cost "Maj32"
jetCostWord Maj64 = cost "Maj64"
jetCostWord XorXor1 = cost "XorXor1"
jetCostWord XorXor8 = cost "XorXor8"
jetCostWord XorXor16 = cost "XorXor16"
jetCostWord XorXor32 = cost "XorXor32"
jetCostWord XorXor64 = cost "XorXor64"
jetCostWord Ch1 = cost "Ch1"
jetCostWord Ch8 = cost "Ch8"
jetCostWord Ch16 = cost "Ch16"
jetCostWord Ch32 = cost "Ch32"
jetCostWord Ch64 = cost "Ch64"
jetCostWord Some1 = cost "Some1"
jetCostWord Some8 = cost "Some8"
jetCostWord Some16 = cost "Some16"
jetCostWord Some32 = cost "Some32"
jetCostWord Some64 = cost "Some64"
jetCostWord All8 = cost "All8"
jetCostWord All16 = cost "All16"
jetCostWord All32 = cost "All32"
jetCostWord All64 = cost "All64"
jetCostWord Eq1 = cost "Eq1"
jetCostWord Eq8 = cost "Eq8"
jetCostWord Eq16 = cost "Eq16"
jetCostWord Eq32 = cost "Eq32"
jetCostWord Eq64 = cost "Eq64"
jetCostWord Eq256 = cost "Eq256"
jetCostWord FullLeftShift8_1 = cost "FullLeftShift8_1"
jetCostWord FullLeftShift8_2 = cost "FullLeftShift8_2"
jetCostWord FullLeftShift8_4 = cost "FullLeftShift8_4"
jetCostWord FullLeftShift16_1 = cost "FullLeftShift16_1"
jetCostWord FullLeftShift16_2 = cost "FullLeftShift16_2"
jetCostWord FullLeftShift16_4 = cost "FullLeftShift16_4"
jetCostWord FullLeftShift16_8 = cost "FullLeftShift16_8"
jetCostWord FullLeftShift32_1 = cost "FullLeftShift32_1"
jetCostWord FullLeftShift32_2 = cost "FullLeftShift32_2"
jetCostWord FullLeftShift32_4 = cost "FullLeftShift32_4"
jetCostWord FullLeftShift32_8 = cost "FullLeftShift32_8"
jetCostWord FullLeftShift32_16 = cost "FullLeftShift32_16"
jetCostWord FullLeftShift64_1 = cost "FullLeftShift64_1"
jetCostWord FullLeftShift64_2 = cost "FullLeftShift64_2"
jetCostWord FullLeftShift64_4 = cost "FullLeftShift64_4"
jetCostWord FullLeftShift64_8 = cost "FullLeftShift64_8"
jetCostWord FullLeftShift64_16 = cost "FullLeftShift64_16"
jetCostWord FullLeftShift64_32 = cost "FullLeftShift64_32"
jetCostWord FullRightShift8_1 = cost "FullRightShift8_1"
jetCostWord FullRightShift8_2 = cost "FullRightShift8_2"
jetCostWord FullRightShift8_4 = cost "FullRightShift8_4"
jetCostWord FullRightShift16_1 = cost "FullRightShift16_1"
jetCostWord FullRightShift16_2 = cost "FullRightShift16_2"
jetCostWord FullRightShift16_4 = cost "FullRightShift16_4"
jetCostWord FullRightShift16_8 = cost "FullRightShift16_8"
jetCostWord FullRightShift32_1 = cost "FullRightShift32_1"
jetCostWord FullRightShift32_2 = cost "FullRightShift32_2"
jetCostWord FullRightShift32_4 = cost "FullRightShift32_4"
jetCostWord FullRightShift32_8 = cost "FullRightShift32_8"
jetCostWord FullRightShift32_16 = cost "FullRightShift32_16"
jetCostWord FullRightShift64_1 = cost "FullRightShift64_1"
jetCostWord FullRightShift64_2 = cost "FullRightShift64_2"
jetCostWord FullRightShift64_4 = cost "FullRightShift64_4"
jetCostWord FullRightShift64_8 = cost "FullRightShift64_8"
jetCostWord FullRightShift64_16 = cost "FullRightShift64_16"
jetCostWord FullRightShift64_32 = cost "FullRightShift64_32"
jetCostWord Leftmost8_1 = cost "Leftmost8_1"
jetCostWord Leftmost8_2 = cost "Leftmost8_2"
jetCostWord Leftmost8_4 = cost "Leftmost8_4"
jetCostWord Leftmost16_1 = cost "Leftmost16_1"
jetCostWord Leftmost16_2 = cost "Leftmost16_2"
jetCostWord Leftmost16_4 = cost "Leftmost16_4"
jetCostWord Leftmost16_8 = cost "Leftmost16_8"
jetCostWord Leftmost32_1 = cost "Leftmost32_1"
jetCostWord Leftmost32_2 = cost "Leftmost32_2"
jetCostWord Leftmost32_4 = cost "Leftmost32_4"
jetCostWord Leftmost32_8 = cost "Leftmost32_8"
jetCostWord Leftmost32_16 = cost "Leftmost32_16"
jetCostWord Leftmost64_1 = cost "Leftmost64_1"
jetCostWord Leftmost64_2 = cost "Leftmost64_2"
jetCostWord Leftmost64_4 = cost "Leftmost64_4"
jetCostWord Leftmost64_8 = cost "Leftmost64_8"
jetCostWord Leftmost64_16 = cost "Leftmost64_16"
jetCostWord Leftmost64_32 = cost "Leftmost64_32"
jetCostWord Rightmost8_1 = cost "Rightmost8_1"
jetCostWord Rightmost8_2 = cost "Rightmost8_2"
jetCostWord Rightmost8_4 = cost "Rightmost8_4"
jetCostWord Rightmost16_1 = cost "Rightmost16_1"
jetCostWord Rightmost16_2 = cost "Rightmost16_2"
jetCostWord Rightmost16_4 = cost "Rightmost16_4"
jetCostWord Rightmost16_8 = cost "Rightmost16_8"
jetCostWord Rightmost32_1 = cost "Rightmost32_1"
jetCostWord Rightmost32_2 = cost "Rightmost32_2"
jetCostWord Rightmost32_4 = cost "Rightmost32_4"
jetCostWord Rightmost32_8 = cost "Rightmost32_8"
jetCostWord Rightmost32_16 = cost "Rightmost32_16"
jetCostWord Rightmost64_1 = cost "Rightmost64_1"
jetCostWord Rightmost64_2 = cost "Rightmost64_2"
jetCostWord Rightmost64_4 = cost "Rightmost64_4"
jetCostWord Rightmost64_8 = cost "Rightmost64_8"
jetCostWord Rightmost64_16 = cost "Rightmost64_16"
jetCostWord Rightmost64_32 = cost "Rightmost64_32"
jetCostWord LeftPadLow1_8 = cost "LeftPadLow1_8"
jetCostWord LeftPadLow1_16 = cost "LeftPadLow1_16"
jetCostWord LeftPadLow8_16 = cost "LeftPadLow8_16"
jetCostWord LeftPadLow1_32 = cost "LeftPadLow1_32"
jetCostWord LeftPadLow8_32 = cost "LeftPadLow8_32"
jetCostWord LeftPadLow16_32 = cost "LeftPadLow16_32"
jetCostWord LeftPadLow1_64 = cost "LeftPadLow1_64"
jetCostWord LeftPadLow8_64 = cost "LeftPadLow8_64"
jetCostWord LeftPadLow16_64 = cost "LeftPadLow16_64"
jetCostWord LeftPadLow32_64 = cost "LeftPadLow32_64"
jetCostWord LeftPadHigh1_8 = cost "LeftPadHigh1_8"
jetCostWord LeftPadHigh1_16 = cost "LeftPadHigh1_16"
jetCostWord LeftPadHigh8_16 = cost "LeftPadHigh8_16"
jetCostWord LeftPadHigh1_32 = cost "LeftPadHigh1_32"
jetCostWord LeftPadHigh8_32 = cost "LeftPadHigh8_32"
jetCostWord LeftPadHigh16_32 = cost "LeftPadHigh16_32"
jetCostWord LeftPadHigh1_64 = cost "LeftPadHigh1_64"
jetCostWord LeftPadHigh8_64 = cost "LeftPadHigh8_64"
jetCostWord LeftPadHigh16_64 = cost "LeftPadHigh16_64"
jetCostWord LeftPadHigh32_64 = cost "LeftPadHigh32_64"
jetCostWord LeftExtend1_8 = cost "LeftExtend1_8"
jetCostWord LeftExtend1_16 = cost "LeftExtend1_16"
jetCostWord LeftExtend8_16 = cost "LeftExtend8_16"
jetCostWord LeftExtend1_32 = cost "LeftExtend1_32"
jetCostWord LeftExtend8_32 = cost "LeftExtend8_32"
jetCostWord LeftExtend16_32 = cost "LeftExtend16_32"
jetCostWord LeftExtend1_64 = cost "LeftExtend1_64"
jetCostWord LeftExtend8_64 = cost "LeftExtend8_64"
jetCostWord LeftExtend16_64 = cost "LeftExtend16_64"
jetCostWord LeftExtend32_64 = cost "LeftExtend32_64"
jetCostWord RightPadLow1_8 = cost "RightPadLow1_8"
jetCostWord RightPadLow1_16 = cost "RightPadLow1_16"
jetCostWord RightPadLow8_16 = cost "RightPadLow8_16"
jetCostWord RightPadLow1_32 = cost "RightPadLow1_32"
jetCostWord RightPadLow8_32 = cost "RightPadLow8_32"
jetCostWord RightPadLow16_32 = cost "RightPadLow16_32"
jetCostWord RightPadLow1_64 = cost "RightPadLow1_64"
jetCostWord RightPadLow8_64 = cost "RightPadLow8_64"
jetCostWord RightPadLow16_64 = cost "RightPadLow16_64"
jetCostWord RightPadLow32_64 = cost "RightPadLow32_64"
jetCostWord RightPadHigh1_8 = cost "RightPadHigh1_8"
jetCostWord RightPadHigh1_16 = cost "RightPadHigh1_16"
jetCostWord RightPadHigh8_16 = cost "RightPadHigh8_16"
jetCostWord RightPadHigh1_32 = cost "RightPadHigh1_32"
jetCostWord RightPadHigh8_32 = cost "RightPadHigh8_32"
jetCostWord RightPadHigh16_32 = cost "RightPadHigh16_32"
jetCostWord RightPadHigh1_64 = cost "RightPadHigh1_64"
jetCostWord RightPadHigh8_64 = cost "RightPadHigh8_64"
jetCostWord RightPadHigh16_64 = cost "RightPadHigh16_64"
jetCostWord RightPadHigh32_64 = cost "RightPadHigh32_64"
jetCostWord RightExtend8_16 = cost "RightExtend8_16"
jetCostWord RightExtend8_32 = cost "RightExtend8_32"
jetCostWord RightExtend16_32 = cost "RightExtend16_32"
jetCostWord RightExtend8_64 = cost "RightExtend8_64"
jetCostWord RightExtend16_64 = cost "RightExtend16_64"
jetCostWord RightExtend32_64 = cost "RightExtend32_64"
jetCostWord LeftShiftWith8 = cost "LeftShiftWith8"
jetCostWord LeftShiftWith16 = cost "LeftShiftWith16"
jetCostWord LeftShiftWith32 = cost "LeftShiftWith32"
jetCostWord LeftShiftWith64 = cost "LeftShiftWith64"
jetCostWord LeftShift8 = cost "LeftShift8"
jetCostWord LeftShift16 = cost "LeftShift16"
jetCostWord LeftShift32 = cost "LeftShift32"
jetCostWord LeftShift64 = cost "LeftShift64"
jetCostWord RightShiftWith8 = cost "RightShiftWith8"
jetCostWord RightShiftWith16 = cost "RightShiftWith16"
jetCostWord RightShiftWith32 = cost "RightShiftWith32"
jetCostWord RightShiftWith64 = cost "RightShiftWith64"
jetCostWord RightShift8 = cost "RightShift8"
jetCostWord RightShift16 = cost "RightShift16"
jetCostWord RightShift32 = cost "RightShift32"
jetCostWord RightShift64 = cost "RightShift64"
jetCostWord LeftRotate8 = cost "LeftRotate8"
jetCostWord LeftRotate16 = cost "LeftRotate16"
jetCostWord LeftRotate32 = cost "LeftRotate32"
jetCostWord LeftRotate64 = cost "LeftRotate64"
jetCostWord RightRotate8 = cost "RightRotate8"
jetCostWord RightRotate16 = cost "RightRotate16"
jetCostWord RightRotate32 = cost "RightRotate32"
jetCostWord RightRotate64 = cost "RightRotate64"

jetCostArith :: ArithJet a b -> Weight
jetCostArith One8 = cost "One8"
jetCostArith One16 = cost "One16"
jetCostArith One32 = cost "One32"
jetCostArith One64 = cost "One64"
jetCostArith FullAdd8 = cost "FullAdd8"
jetCostArith FullAdd16 = cost "FullAdd16"
jetCostArith FullAdd32 = cost "FullAdd32"
jetCostArith FullAdd64 = cost "FullAdd64"
jetCostArith Add8 = cost "Add8"
jetCostArith Add16 = cost "Add16"
jetCostArith Add32 = cost "Add32"
jetCostArith Add64 = cost "Add64"
jetCostArith FullIncrement8 = cost "FullIncrement8"
jetCostArith FullIncrement16 = cost "FullIncrement16"
jetCostArith FullIncrement32 = cost "FullIncrement32"
jetCostArith FullIncrement64 = cost "FullIncrement64"
jetCostArith Increment8 = cost "Increment8"
jetCostArith Increment16 = cost "Increment16"
jetCostArith Increment32 = cost "Increment32"
jetCostArith Increment64 = cost "Increment64"
jetCostArith FullSubtract8 = cost "FullSubtract8"
jetCostArith FullSubtract16 = cost "FullSubtract16"
jetCostArith FullSubtract32 = cost "FullSubtract32"
jetCostArith FullSubtract64 = cost "FullSubtract64"
jetCostArith Subtract8 = cost "Subtract8"
jetCostArith Subtract16 = cost "Subtract16"
jetCostArith Subtract32 = cost "Subtract32"
jetCostArith Subtract64 = cost "Subtract64"
jetCostArith Negate8 = cost "Negate8"
jetCostArith Negate16 = cost "Negate16"
jetCostArith Negate32 = cost "Negate32"
jetCostArith Negate64 = cost "Negate64"
jetCostArith FullDecrement8 = cost "FullDecrement8"
jetCostArith FullDecrement16 = cost "FullDecrement16"
jetCostArith FullDecrement32 = cost "FullDecrement32"
jetCostArith FullDecrement64 = cost "FullDecrement64"
jetCostArith Decrement8 = cost "Decrement8"
jetCostArith Decrement16 = cost "Decrement16"
jetCostArith Decrement32 = cost "Decrement32"
jetCostArith Decrement64 = cost "Decrement64"
jetCostArith Multiply8 = cost "Multiply8"
jetCostArith Multiply16 = cost "Multiply16"
jetCostArith Multiply32 = cost "Multiply32"
jetCostArith Multiply64 = cost "Multiply64"
jetCostArith FullMultiply8 = cost "FullMultiply8"
jetCostArith FullMultiply16 = cost "FullMultiply16"
jetCostArith FullMultiply32 = cost "FullMultiply32"
jetCostArith FullMultiply64 = cost "FullMultiply64"
jetCostArith IsZero8 = cost "IsZero8"
jetCostArith IsZero16 = cost "IsZero16"
jetCostArith IsZero32 = cost "IsZero32"
jetCostArith IsZero64 = cost "IsZero64"
jetCostArith IsOne8 = cost "IsOne8"
jetCostArith IsOne16 = cost "IsOne16"
jetCostArith IsOne32 = cost "IsOne32"
jetCostArith IsOne64 = cost "IsOne64"
jetCostArith Le8 = cost "Le8"
jetCostArith Le16 = cost "Le16"
jetCostArith Le32 = cost "Le32"
jetCostArith Le64 = cost "Le64"
jetCostArith Lt8 = cost "Lt8"
jetCostArith Lt16 = cost "Lt16"
jetCostArith Lt32 = cost "Lt32"
jetCostArith Lt64 = cost "Lt64"
jetCostArith Min8 = cost "Min8"
jetCostArith Min16 = cost "Min16"
jetCostArith Min32 = cost "Min32"
jetCostArith Min64 = cost "Min64"
jetCostArith Max8 = cost "Max8"
jetCostArith Max16 = cost "Max16"
jetCostArith Max32 = cost "Max32"
jetCostArith Max64 = cost "Max64"
jetCostArith Median8 = cost "Median8"
jetCostArith Median16 = cost "Median16"
jetCostArith Median32 = cost "Median32"
jetCostArith Median64 = cost "Median64"
jetCostArith DivMod128_64 = cost "DivMod128_64"
jetCostArith DivMod8 = cost "DivMod8"
jetCostArith DivMod16 = cost "DivMod16"
jetCostArith DivMod32 = cost "DivMod32"
jetCostArith DivMod64 = cost "DivMod64"
jetCostArith Divide8 = cost "Divide8"
jetCostArith Divide16 = cost "Divide16"
jetCostArith Divide32 = cost "Divide32"
jetCostArith Divide64 = cost "Divide64"
jetCostArith Modulo8 = cost "Modulo8"
jetCostArith Modulo16 = cost "Modulo16"
jetCostArith Modulo32 = cost "Modulo32"
jetCostArith Modulo64 = cost "Modulo64"
jetCostArith Divides8 = cost "Divides8"
jetCostArith Divides16 = cost "Divides16"
jetCostArith Divides32 = cost "Divides32"
jetCostArith Divides64 = cost "Divides64"

jetCostHash :: HashJet a b -> Weight
jetCostHash Sha256Block = cost "Sha256Block"
jetCostHash Sha256Iv = cost "Sha256Iv"
jetCostHash Sha256Ctx8Add1 = cost "Sha256Ctx8Add1"
jetCostHash Sha256Ctx8Add2 = cost "Sha256Ctx8Add2"
jetCostHash Sha256Ctx8Add4 = cost "Sha256Ctx8Add4"
jetCostHash Sha256Ctx8Add8 = cost "Sha256Ctx8Add8"
jetCostHash Sha256Ctx8Add16 = cost "Sha256Ctx8Add16"
jetCostHash Sha256Ctx8Add32 = cost "Sha256Ctx8Add32"
jetCostHash Sha256Ctx8Add64 = cost "Sha256Ctx8Add64"
jetCostHash Sha256Ctx8Add128 = cost "Sha256Ctx8Add128"
jetCostHash Sha256Ctx8Add256 = cost "Sha256Ctx8Add256"
jetCostHash Sha256Ctx8Add512 = cost "Sha256Ctx8Add512"
jetCostHash Sha256Ctx8AddBuffer511 = cost "Sha256Ctx8AddBuffer511"
jetCostHash Sha256Ctx8Finalize = cost "Sha256Ctx8Finalize"
jetCostHash Sha256Ctx8Init = cost "Sha256Ctx8Init"

jetCostSecp256k1 :: Secp256k1Jet a b -> Weight
jetCostSecp256k1 FeNormalize = cost "FeNormalize"
jetCostSecp256k1 FeNegate = cost "FeNegate"
jetCostSecp256k1 FeAdd = cost "FeAdd"
jetCostSecp256k1 FeSquare = cost "FeSquare"
jetCostSecp256k1 FeMultiply = cost "FeMultiply"
jetCostSecp256k1 FeMultiplyBeta = cost "FeMultiplyBeta"
jetCostSecp256k1 FeInvert = cost "FeInvert"
jetCostSecp256k1 FeSquareRoot = cost "FeSquareRoot"
jetCostSecp256k1 FeIsZero = cost "FeIsZero"
jetCostSecp256k1 FeIsOdd = cost "FeIsOdd"
jetCostSecp256k1 ScalarNormalize = cost "ScalarNormalize"
jetCostSecp256k1 ScalarNegate = cost "ScalarNegate"
jetCostSecp256k1 ScalarAdd = cost "ScalarAdd"
jetCostSecp256k1 ScalarSquare = cost "ScalarSquare"
jetCostSecp256k1 ScalarMultiply = cost "ScalarMultiply"
jetCostSecp256k1 ScalarMultiplyLambda = cost "ScalarMultiplyLambda"
jetCostSecp256k1 ScalarInvert = cost "ScalarInvert"
jetCostSecp256k1 ScalarIsZero = cost "ScalarIsZero"
jetCostSecp256k1 GejInfinity = cost "GejInfinity"
jetCostSecp256k1 GejNormalize = cost "GejNormalize"
jetCostSecp256k1 GejNegate = cost "GejNegate"
jetCostSecp256k1 GeNegate = cost "GeNegate"
jetCostSecp256k1 GejDouble = cost "GejDouble"
jetCostSecp256k1 GejAdd = cost "GejAdd"
jetCostSecp256k1 GejGeAddEx = cost "GejGeAddEx"
jetCostSecp256k1 GejGeAdd = cost "GejGeAdd"
jetCostSecp256k1 GejRescale = cost "GejRescale"
jetCostSecp256k1 GejIsInfinity = cost "GejIsInfinity"
jetCostSecp256k1 GejEquiv = cost "GejEquiv"
jetCostSecp256k1 GejGeEquiv = cost "GejGeEquiv"
jetCostSecp256k1 GejXEquiv = cost "GejXEquiv"
jetCostSecp256k1 GejYIsOdd = cost "GejYIsOdd"
jetCostSecp256k1 GejIsOnCurve = cost "GejIsOnCurve"
jetCostSecp256k1 GeIsOnCurve = cost "GeIsOnCurve"
jetCostSecp256k1 Generate = cost "Generate"
jetCostSecp256k1 Scale = cost "Scale"
jetCostSecp256k1 LinearCombination1 = cost "LinearCombination1"
jetCostSecp256k1 LinearVerify1 = cost "LinearVerify1"
jetCostSecp256k1 PointVerify1 = cost "PointVerify1"
jetCostSecp256k1 Decompress = cost "Decompress"
jetCostSecp256k1 Swu = cost "Swu"
jetCostSecp256k1 HashToCurve = cost "HashToCurve"

jetCostSignature :: SignatureJet a b -> Weight
jetCostSignature CheckSigVerify = cost "CheckSigVerify"
jetCostSignature Bip0340Verify = cost "Bip0340Verify"

jetCostCoreBitcoin :: CoreJets.BitcoinJet a b -> Weight
jetCostCoreBitcoin ParseLock = cost "ParseLock"
jetCostCoreBitcoin ParseSequence = cost "ParseSequence"
jetCostCoreBitcoin TapdataInit = cost "TapdataInit"

jetCostBitcoin :: BitcoinJet a b -> Weight
jetCostBitcoin (SigHashJet x) = jetCostSigHash x
jetCostBitcoin (TimeLockJet x) = jetCostTimeLock x
jetCostBitcoin (TransactionJet x) = jetCostTransaction x

jetCostSigHash :: SigHashJet a b -> Weight
jetCostSigHash SigAllHash = cost "SigAllHash"
jetCostSigHash TxHash = cost "TxHash"
jetCostSigHash TapEnvHash = cost "TapEnvHash"
jetCostSigHash OutputsHash = cost "OutputsHash"
jetCostSigHash InputsHash = cost "InputsHash"
jetCostSigHash InputUtxosHash = cost "InputUtxosHash"
jetCostSigHash OutputHash = cost "OutputHash"
jetCostSigHash OutputValuesHash = cost "OutputValuesHash"
jetCostSigHash OutputScriptsHash = cost "OutputScriptsHash"
jetCostSigHash InputHash = cost "InputHash"
jetCostSigHash InputOutpointsHash = cost "InputOutpointsHash"
jetCostSigHash InputSequencesHash = cost "InputSequencesHash"
jetCostSigHash InputAnnexesHash = cost "InputAnnexesHash"
jetCostSigHash InputScriptSigsHash = cost "InputScriptSigsHash"
jetCostSigHash InputUtxoHash = cost "InputUtxoHash"
jetCostSigHash InputValuesHash = cost "InputValuesHash"
jetCostSigHash InputScriptsHash = cost "InputScriptsHash"
jetCostSigHash TapleafHash = cost "TapleafHash"
jetCostSigHash TappathHash = cost "TappathHash"
jetCostSigHash OutpointHash = cost "OutpointHash"
jetCostSigHash AnnexHash = cost "AnnexHash"
jetCostSigHash BuildTapleafSimplicity = cost "BuildTapleafSimplicity"
jetCostSigHash BuildTapbranch = cost "BuildTapbranch"
jetCostSigHash BuildTaptweak = cost "BuildTaptweak"

jetCostTimeLock :: TimeLockJet a b -> Weight
jetCostTimeLock CheckLockHeight = cost "CheckLockHeight"
jetCostTimeLock CheckLockTime = cost "CheckLockTime"
jetCostTimeLock CheckLockDistance = cost "CheckLockDistance"
jetCostTimeLock CheckLockDuration = cost "CheckLockDuration"
jetCostTimeLock TxLockHeight = cost "TxLockHeight"
jetCostTimeLock TxLockTime = cost "TxLockTime"
jetCostTimeLock TxLockDistance = cost "TxLockDistance"
jetCostTimeLock TxLockDuration = cost "TxLockDuration"
jetCostTimeLock TxIsFinal = cost "TxIsFinal"

jetCostTransaction :: TransactionJet a b -> Weight
jetCostTransaction ScriptCMR = cost "ScriptCMR"
jetCostTransaction InternalKey = cost "InternalKey"
jetCostTransaction CurrentIndex = cost "CurrentIndex"
jetCostTransaction NumInputs = cost "NumInputs"
jetCostTransaction NumOutputs = cost "NumOutputs"
jetCostTransaction LockTime = cost "LockTime"
jetCostTransaction Fee = cost "Fee"
jetCostTransaction OutputValue = cost "OutputValue"
jetCostTransaction OutputScriptHash = cost "OutputScriptHash"
jetCostTransaction TotalOutputValue = cost "TotalOutputValue"
jetCostTransaction CurrentPrevOutpoint = cost "CurrentPrevOutpoint"
jetCostTransaction CurrentValue = cost "CurrentValue"
jetCostTransaction CurrentScriptHash = cost "CurrentScriptHash"
jetCostTransaction CurrentSequence = cost "CurrentSequence"
jetCostTransaction CurrentAnnexHash = cost "CurrentAnnexHash"
jetCostTransaction CurrentScriptSigHash = cost "CurrentScriptSigHash"
jetCostTransaction InputPrevOutpoint = cost "InputPrevOutpoint"
jetCostTransaction InputValue = cost "InputValue"
jetCostTransaction InputScriptHash = cost "InputScriptHash"
jetCostTransaction InputSequence = cost "InputSequence"
jetCostTransaction InputAnnexHash = cost "InputAnnexHash"
jetCostTransaction InputScriptSigHash = cost "InputScriptSigHash"
jetCostTransaction TotalInputValue = cost "TotalInputValue"
jetCostTransaction TapleafVersion = cost "TapleafVersion"
jetCostTransaction Tappath = cost "Tappath"
jetCostTransaction Version = cost "Version"
jetCostTransaction TransactionId = cost "TransactionId"
