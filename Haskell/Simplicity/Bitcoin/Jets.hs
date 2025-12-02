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
import Simplicity.CoreJets (CoreJet, coreJetMap, ConstWordContent(..), SomeConstWordContent(..))
import qualified Simplicity.CoreJets as CoreJets
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
