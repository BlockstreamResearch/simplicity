-- | This module provides a cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Elements.Jets
  ( JetType(..), ElementsJet(..), SigHashJet(..), TimeLockJet(..), IssuanceJet(..), TransactionJet(..)
  , asJet
  , jetSubst, pruneSubst
  , getTermStopCode, putTermStopCode
  , getTermLengthCode, putTermLengthCode
  , fastEval
  , jetMap
  -- * Re-exports
  , WrappedSimplicity, unwrap
  , Simplicity.Elements.JetType.specification, Simplicity.Elements.JetType.implementation
  , Simplicity.Elements.JetType.getJetBit, Simplicity.Elements.JetType.putJetBit
  , Simplicity.Elements.JetType.jetCost
  , Semantics.FastEval
  ) where

import Prelude hiding (fail, drop, take)

import Control.Applicative ((<|>))
import Control.Arrow ((***), (+++))
import Control.Monad (guard)
import qualified Data.ByteString as BS
import Data.Either (isRight)
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Proxy (Proxy(Proxy))
import Data.Serialize (runPut, put, putWord8)
import Data.String (fromString)
import Data.Type.Equality ((:~:)(Refl))
import Data.Vector ((!?))
import Data.Void (Void, vacuous)
import Lens.Family2 ((^..), over, review)

import qualified Simplicity.Benchmarks as Benchmarks
import Simplicity.Digest
import Simplicity.CoreJets (CoreJet, coreJetMap, ConstWordContent(..), SomeConstWordContent(..))
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Elements.Dag hiding (jetSubst, pruneSubst)
import qualified Simplicity.Elements.Dag as Dag
import Simplicity.Elements.Term
import Simplicity.Elements.DataTypes
import qualified Simplicity.Elements.JetType
import Simplicity.Elements.Primitive (PrimEnv, S, Conf, PubKey, primEnvHash, envTx, envTap)
import qualified Simplicity.Elements.Primitive as Prim
import qualified Simplicity.Elements.Serialization.BitString as BitString
import qualified Simplicity.Elements.Semantics as Semantics
import qualified Simplicity.Elements.Programs.SigHash.Lib as SigHash
import qualified Simplicity.Elements.Programs.Issuance.Lib as Issuance
import qualified Simplicity.Elements.Programs.TimeLock as TimeLock
import qualified Simplicity.Elements.Programs.Transaction.Lib as Prog
import Simplicity.LibSecp256k1.Spec (fe)
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.Elements.Lib (Ctx8)
import qualified Simplicity.Programs.Elements.Lib as Prog
import Simplicity.Programs.Word
import Simplicity.Serialization
import Simplicity.Tensor
import Simplicity.Tree
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word
import qualified Simplicity.Word as W
import Simplicity.Weight

-- | A type of tokens for the cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
--
-- The tokens themselves are not exported.  You are expected to use 'Simplicity.Dag.jetDag' to substitute known jets found in Simplicity expressions.
data JetType a b where
  ConstWordJet :: ConstWordContent b -> JetType () b
  CoreJet :: CoreJet a b -> JetType a b
  ElementsJet :: ElementsJet a b -> JetType a b
deriving instance Eq (JetType a b)
deriving instance Show (JetType a b)

data ElementsJet a b where
  SigHashJet :: SigHashJet a b -> ElementsJet a b
  TimeLockJet :: TimeLockJet a b -> ElementsJet a b
  IssuanceJet :: IssuanceJet a b -> ElementsJet a b
  TransactionJet :: TransactionJet a b -> ElementsJet a b
deriving instance Eq (ElementsJet a b)
deriving instance Show (ElementsJet a b)

data SigHashJet a b where
  SigAllHash :: SigHashJet () Word256
  TxHash :: SigHashJet () Word256
  TapEnvHash :: SigHashJet () Word256
  OutputsHash :: SigHashJet () Word256
  InputsHash :: SigHashJet () Word256
  IssuancesHash :: SigHashJet () Word256
  InputUtxosHash :: SigHashJet () Word256
  OutputHash :: SigHashJet Word32 (S Word256)
  OutputAmountsHash :: SigHashJet () Word256
  OutputScriptsHash :: SigHashJet () Word256
  OutputNoncesHash :: SigHashJet () Word256
  OutputRangeProofsHash :: SigHashJet () Word256
  OutputSurjectionProofsHash :: SigHashJet () Word256
  InputHash :: SigHashJet Word32 (S Word256)
  InputOutpointsHash :: SigHashJet () Word256
  InputSequencesHash :: SigHashJet () Word256
  InputAnnexesHash :: SigHashJet () Word256
  InputScriptSigsHash :: SigHashJet () Word256
  IssuanceHash :: SigHashJet Word32 (S Word256)
  IssuanceAssetAmountsHash :: SigHashJet () Word256
  IssuanceTokenAmountsHash :: SigHashJet () Word256
  IssuanceRangeProofsHash :: SigHashJet () Word256
  IssuanceBlindingEntropyHash :: SigHashJet () Word256
  InputUtxoHash :: SigHashJet Word32 (S Word256)
  InputAmountsHash :: SigHashJet () Word256
  InputScriptsHash :: SigHashJet () Word256
  TapleafHash :: SigHashJet () Word256
  TappathHash :: SigHashJet () Word256
  OutpointHash :: SigHashJet (Ctx8, (S Word256, (Word256, Word32))) Ctx8
  AssetAmountHash :: SigHashJet (Ctx8, (Conf Word256, Conf Word64)) Ctx8
  NonceHash :: SigHashJet (Ctx8, S (Conf Word256)) Ctx8
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

data IssuanceJet a b where
  Issuance :: IssuanceJet Word32 (S (S Bit))
  IssuanceAsset :: IssuanceJet Word32 (S (S Word256))
  IssuanceToken :: IssuanceJet Word32 (S (S Word256))
  IssuanceEntropy :: IssuanceJet Word32 (S (S Word256))
  CalculateIssuanceEntropy :: IssuanceJet ((Word256, Word32), Word256) Word256
  CalculateAsset :: IssuanceJet Word256 Word256
  CalculateExplicitToken :: IssuanceJet Word256 Word256
  CalculateConfidentialToken :: IssuanceJet Word256 Word256
  LbtcAsset :: IssuanceJet () Word256
deriving instance Eq (IssuanceJet a b)
deriving instance Show (IssuanceJet a b)

data TransactionJet a b where
  ScriptCMR :: TransactionJet () Word256
  InternalKey :: TransactionJet () PubKey
  CurrentIndex :: TransactionJet () Word32
  NumInputs :: TransactionJet () Word32
  NumOutputs :: TransactionJet () Word32
  LockTime :: TransactionJet () Word32
  OutputAsset :: TransactionJet Word32 (S (Conf Word256))
  OutputAmount :: TransactionJet Word32 (S (Conf Word256, Conf Word64))
  OutputNonce :: TransactionJet Word32 (S (S (Conf Word256)))
  OutputScriptHash :: TransactionJet Word32 (S Word256)
  OutputNullDatum :: TransactionJet (Word32, Word32) (S (S (Either (Word2, Word256) (Either Bit Word4))))
  OutputIsFee :: TransactionJet Word32 (S Bit)
  OutputSurjectionProof :: TransactionJet Word32 (S Word256)
  OutputRangeProof :: TransactionJet Word32 (S Word256)
  TotalFee :: TransactionJet Word256 Word64
  CurrentPegin :: TransactionJet () (S Word256)
  CurrentPrevOutpoint :: TransactionJet () (Word256,Word32)
  CurrentAsset :: TransactionJet () (Conf Word256)
  CurrentAmount :: TransactionJet () (Conf Word256, Conf Word64)
  CurrentScriptHash :: TransactionJet () Word256
  CurrentSequence :: TransactionJet () Word32
  CurrentAnnexHash :: TransactionJet () (S Word256)
  CurrentScriptSigHash :: TransactionJet () Word256
  CurrentReissuanceBlinding :: TransactionJet () (S Word256)
  CurrentNewIssuanceContract :: TransactionJet () (S Word256)
  CurrentReissuanceEntropy :: TransactionJet () (S Word256)
  CurrentIssuanceAssetAmount :: TransactionJet () (S (Conf Word64))
  CurrentIssuanceTokenAmount :: TransactionJet () (S (Conf Word64))
  CurrentIssuanceAssetProof :: TransactionJet () Word256
  CurrentIssuanceTokenProof :: TransactionJet () Word256
  InputPegin :: TransactionJet Word32 (S (S Word256))
  InputPrevOutpoint :: TransactionJet Word32 (S (Word256,Word32))
  InputAsset :: TransactionJet Word32 (S (Conf Word256))
  InputAmount :: TransactionJet Word32 (S (Conf Word256, Conf Word64))
  InputScriptHash :: TransactionJet Word32 (S Word256)
  InputSequence :: TransactionJet Word32 (S Word32)
  InputAnnexHash :: TransactionJet Word32 (S (S Word256))
  InputScriptSigHash :: TransactionJet Word32 (S Word256)
  ReissuanceBlinding :: TransactionJet Word32 (S (S Word256))
  NewIssuanceContract :: TransactionJet Word32 (S (S Word256))
  ReissuanceEntropy :: TransactionJet Word32 (S (S Word256))
  IssuanceAssetAmount :: TransactionJet Word32 (S (S (Conf Word64)))
  IssuanceTokenAmount :: TransactionJet Word32 (S (S (Conf Word64)))
  IssuanceAssetProof :: TransactionJet Word32 (S Word256)
  IssuanceTokenProof :: TransactionJet Word32 (S Word256)
  TapleafVersion :: TransactionJet () Word8
  Tappath :: TransactionJet Word8 (S Word256)
  Version :: TransactionJet () Word32
  GenesisBlockHash :: TransactionJet () Word256
  TransactionId :: TransactionJet () Word256
deriving instance Eq (TransactionJet a b)
deriving instance Show (TransactionJet a b)

specificationElements :: (Assert term, Primitive term) => ElementsJet a b -> term a b
specificationElements (SigHashJet x) = specificationSigHash x
specificationElements (TimeLockJet x) = specificationTimeLock x
specificationElements (IssuanceJet x) = specificationIssuance x
specificationElements (TransactionJet x) = specificationTransaction x

specificationSigHash :: (Assert term, Primitive term) => SigHashJet a b -> term a b
specificationSigHash SigAllHash = SigHash.sigAllHash
specificationSigHash TxHash = SigHash.txHash
specificationSigHash TapEnvHash = SigHash.tapEnvHash
specificationSigHash OutputsHash = SigHash.outputsHash
specificationSigHash InputsHash = SigHash.inputsHash
specificationSigHash IssuancesHash = SigHash.issuancesHash
specificationSigHash InputUtxosHash = SigHash.inputUtxosHash
specificationSigHash OutputHash = SigHash.outputHash
specificationSigHash OutputAmountsHash = SigHash.outputAmountsHash
specificationSigHash OutputScriptsHash = SigHash.outputScriptsHash
specificationSigHash OutputNoncesHash = SigHash.outputNoncesHash
specificationSigHash OutputRangeProofsHash = SigHash.outputRangeProofsHash
specificationSigHash OutputSurjectionProofsHash = SigHash.outputSurjectionProofsHash
specificationSigHash InputHash = SigHash.inputHash
specificationSigHash InputOutpointsHash = SigHash.inputOutpointsHash
specificationSigHash InputSequencesHash = SigHash.inputSequencesHash
specificationSigHash InputAnnexesHash = SigHash.inputAnnexesHash
specificationSigHash InputScriptSigsHash = SigHash.inputScriptSigsHash
specificationSigHash IssuanceHash = SigHash.issuanceHash
specificationSigHash IssuanceAssetAmountsHash = SigHash.issuanceAssetAmountsHash
specificationSigHash IssuanceTokenAmountsHash = SigHash.issuanceTokenAmountsHash
specificationSigHash IssuanceRangeProofsHash = SigHash.issuanceRangeProofsHash
specificationSigHash IssuanceBlindingEntropyHash = SigHash.issuanceBlindingEntropyHash
specificationSigHash InputUtxoHash = SigHash.inputUtxoHash
specificationSigHash InputAmountsHash = SigHash.inputAmountsHash
specificationSigHash InputScriptsHash = SigHash.inputScriptsHash
specificationSigHash TapleafHash = SigHash.tapleafHash
specificationSigHash TappathHash = SigHash.tappathHash
specificationSigHash OutpointHash = Prog.outpointHash
specificationSigHash AssetAmountHash = Prog.assetAmountHash
specificationSigHash NonceHash = Prog.nonceHash
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

specificationIssuance :: (Assert term, Primitive term) => IssuanceJet a b -> term a b
specificationIssuance Issuance = Issuance.issuance
specificationIssuance IssuanceAsset = Issuance.issuanceAsset
specificationIssuance IssuanceToken = Issuance.issuanceToken
specificationIssuance IssuanceEntropy = Issuance.issuanceEntropy
specificationIssuance CalculateIssuanceEntropy = Prog.calculateIssuanceEntropy
specificationIssuance CalculateAsset = Prog.calculateAsset
specificationIssuance CalculateExplicitToken = Prog.calculateExplicitToken
specificationIssuance CalculateConfidentialToken = Prog.calculateConfidentialToken
specificationIssuance LbtcAsset = Prog.lbtcAsset

specificationTransaction :: (Assert term, Primitive term) => TransactionJet a b -> term a b
specificationTransaction ScriptCMR = primitive Prim.ScriptCMR
specificationTransaction InternalKey = primitive Prim.InternalKey
specificationTransaction CurrentIndex = primitive Prim.CurrentIndex
specificationTransaction NumInputs = Prog.numInputs
specificationTransaction NumOutputs = Prog.numOutputs
specificationTransaction LockTime = primitive Prim.LockTime
specificationTransaction OutputAsset = primitive Prim.OutputAsset
specificationTransaction OutputAmount = Prog.outputAmount
specificationTransaction OutputNonce = primitive Prim.OutputNonce
specificationTransaction OutputScriptHash = primitive Prim.OutputScriptHash
specificationTransaction OutputNullDatum = primitive Prim.OutputNullDatum
specificationTransaction OutputIsFee = Prog.outputIsFee
specificationTransaction OutputSurjectionProof = primitive Prim.OutputSurjectionProof
specificationTransaction OutputRangeProof = primitive Prim.OutputRangeProof
specificationTransaction TotalFee = Prog.totalFee
specificationTransaction CurrentPegin = Prog.currentPegin
specificationTransaction CurrentPrevOutpoint = Prog.currentPrevOutpoint
specificationTransaction CurrentAsset = Prog.currentAsset
specificationTransaction CurrentAmount = Prog.currentAmount
specificationTransaction CurrentScriptHash = Prog.currentScriptHash
specificationTransaction CurrentSequence = Prog.currentSequence
specificationTransaction CurrentAnnexHash = Prog.currentAnnexHash
specificationTransaction CurrentScriptSigHash = Prog.currentScriptSigHash
specificationTransaction CurrentReissuanceBlinding = Prog.currentReissuanceBlinding
specificationTransaction CurrentNewIssuanceContract = Prog.currentNewIssuanceContract
specificationTransaction CurrentReissuanceEntropy = Prog.currentReissuanceEntropy
specificationTransaction CurrentIssuanceAssetAmount = Prog.currentIssuanceAssetAmount
specificationTransaction CurrentIssuanceTokenAmount = Prog.currentIssuanceTokenAmount
specificationTransaction CurrentIssuanceAssetProof = Prog.currentIssuanceAssetProof
specificationTransaction CurrentIssuanceTokenProof = Prog.currentIssuanceTokenProof
specificationTransaction InputPegin = primitive Prim.InputPegin
specificationTransaction InputPrevOutpoint = primitive Prim.InputPrevOutpoint
specificationTransaction InputAsset = primitive Prim.InputAsset
specificationTransaction InputAmount = Prog.inputAmount
specificationTransaction InputScriptHash = primitive Prim.InputScriptHash
specificationTransaction InputSequence = primitive Prim.InputSequence
specificationTransaction InputAnnexHash = primitive Prim.InputAnnexHash
specificationTransaction InputScriptSigHash = primitive Prim.InputScriptSigHash
specificationTransaction ReissuanceBlinding = primitive Prim.ReissuanceBlinding
specificationTransaction NewIssuanceContract = primitive Prim.NewIssuanceContract
specificationTransaction ReissuanceEntropy = primitive Prim.ReissuanceEntropy
specificationTransaction IssuanceAssetAmount = primitive Prim.IssuanceAssetAmount
specificationTransaction IssuanceTokenAmount = primitive Prim.IssuanceTokenAmount
specificationTransaction IssuanceAssetProof = primitive Prim.IssuanceAssetProof
specificationTransaction IssuanceTokenProof = primitive Prim.IssuanceTokenProof
specificationTransaction TapleafVersion = primitive Prim.TapleafVersion
specificationTransaction Tappath = primitive Prim.Tappath
specificationTransaction Version = primitive Prim.Version
specificationTransaction GenesisBlockHash = primitive Prim.GenesisBlockHash
specificationTransaction TransactionId = primitive Prim.TransactionId

implementationElements :: ElementsJet a b -> PrimEnv -> a -> Maybe b
implementationElements (SigHashJet x) = implementationSigHash x
implementationElements (TimeLockJet x) = implementationTimeLock x
implementationElements (IssuanceJet x) = implementationIssuance x
implementationElements (TransactionJet x) = implementationTransaction x

implementationSigHash :: SigHashJet a b -> PrimEnv -> a -> Maybe b
implementationSigHash SigAllHash env _ = Just . toWord256 . integerHash256 $ primEnvHash env
implementationSigHash TxHash env _ = Just . toWord256 . integerHash256 $ txHash (envTx env)
implementationSigHash TapEnvHash env _ = Just . toWord256 . integerHash256 $ tapEnvHash (envTap env)
implementationSigHash OutputsHash env _ = Just . toWord256 . integerHash256 $ outputsHash (envTx env)
implementationSigHash InputsHash env _ = Just . toWord256 . integerHash256 $ inputsHash (envTx env)
implementationSigHash IssuancesHash env _ = Just . toWord256 . integerHash256 $ issuancesHash (envTx env)
implementationSigHash InputUtxosHash env _ = Just . toWord256 . integerHash256 $ inputUtxosHash (envTx env)
implementationSigHash OutputHash env i = Just . fmap (toWord256 . integerHash256 . outputHash) . maybe (Left ()) Right
                                       $ sigTxOut (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash OutputAmountsHash env _ = Just . toWord256 . integerHash256 $ outputAmountsHash (envTx env)
implementationSigHash OutputScriptsHash env _ = Just . toWord256 . integerHash256 $ outputScriptsHash (envTx env)
implementationSigHash OutputNoncesHash env _ = Just . toWord256 . integerHash256 $ outputNoncesHash (envTx env)
implementationSigHash OutputRangeProofsHash env _ = Just . toWord256 . integerHash256 $ outputRangeProofsHash (envTx env)
implementationSigHash OutputSurjectionProofsHash env _ = Just . toWord256 . integerHash256 $ outputSurjectionProofsHash (envTx env)
implementationSigHash InputHash env i = Just . fmap (toWord256 . integerHash256 . inputHash) . maybe (Left ()) Right
                                      $ sigTxIn (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash InputOutpointsHash env _ = Just . toWord256 . integerHash256 $ inputOutpointsHash (envTx env)
implementationSigHash InputSequencesHash env _ = Just . toWord256 . integerHash256 $ inputSequencesHash (envTx env)
implementationSigHash InputAnnexesHash env _ = Just . toWord256 . integerHash256 $ inputAnnexesHash (envTx env)
implementationSigHash InputScriptSigsHash env _ = Just . toWord256 . integerHash256 $ inputScriptSigsHash (envTx env)
implementationSigHash IssuanceHash env i = Just . fmap (toWord256 . integerHash256 . issuanceHash) . maybe (Left ()) Right
                                         $ sigTxIn (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash IssuanceAssetAmountsHash env _ = Just . toWord256 . integerHash256 $ issuanceAssetAmountsHash (envTx env)
implementationSigHash IssuanceTokenAmountsHash env _ = Just . toWord256 . integerHash256 $ issuanceTokenAmountsHash (envTx env)
implementationSigHash IssuanceRangeProofsHash env _ = Just . toWord256 . integerHash256 $ issuanceRangeProofsHash (envTx env)
implementationSigHash IssuanceBlindingEntropyHash env _ = Just . toWord256 . integerHash256 $ issuanceBlindingEntropyHash (envTx env)
implementationSigHash InputUtxoHash env i = Just . fmap (toWord256 . integerHash256 . inputUtxoHash . sigTxiTxo) . maybe (Left ()) Right
                                          $ sigTxIn (envTx env) !? (fromIntegral $ fromWord32 i)
implementationSigHash InputAmountsHash env _ = Just . toWord256 . integerHash256 $ inputAmountsHash (envTx env)
implementationSigHash InputScriptsHash env _ = Just . toWord256 . integerHash256 $ inputScriptsHash (envTx env)
implementationSigHash TapleafHash env _ = Just . toWord256 . integerHash256 $ tapleafHash (envTap env)
implementationSigHash TappathHash env _ = Just . toWord256 . integerHash256 $ tappathHash (envTap env)
implementationSigHash OutpointHash _env (ctx, (mw256, op)) = toCtx <$> (flip ctxAdd (runPut (putMW256 mw256 >> putOutpointBE (cast op))) =<< fromCtx ctx)
 where
  putMW256 (Left _) = putWord8 0x00
  putMW256 (Right w256) = putWord8 0x01 >> put (fromIntegral (fromWord256 w256) :: W.Word256)
  cast (h, i) = Outpoint (review (over be256) (fromW256 h)) (fromW32 i)
  fromW256 = fromIntegral . fromWord256
  fromW32 = fromIntegral . fromWord32
implementationSigHash AssetAmountHash _env (ctx, (cw256, cw64)) = toCtx <$> (flip ctxAdd (runPut (put256 cw256 >> put64 cw64)) =<< fromCtx ctx)
 where
  put256 (Left (by, x)) = putWord8 (if fromBit by then 0xb else 0x0a) >> put (fromW256 x)
  put256 (Right w256) = putWord8 0x01 >> put (fromW256 w256)
  put64 (Left (by, x)) = putWord8 (if fromBit by then 0x9 else 0x08) >> put (fromW256 x)
  put64 (Right w64) = putWord8 0x01 >> put (fromW64 w64)
  fromW256 :: Word256 -> W.Word256
  fromW256 = fromIntegral . fromWord256
  fromW64 :: Word64 -> W.Word64
  fromW64 = fromIntegral . fromWord64
implementationSigHash NonceHash _env (ctx, mcw256) = toCtx <$> (flip ctxAdd (runPut . putNonce $ nonce) =<< fromCtx ctx)
 where
  nonce = either (const Nothing) (Just . Nonce . ((fromBit *** (fromIntegral . fromWord256)) +++ fromHash)) mcw256
implementationSigHash AnnexHash _env (ctx, mw256) = toCtx <$> (flip ctxAdd (runPut . putMW256 $ mw256) =<< fromCtx ctx)
 where
  putMW256 (Left _) = putWord8 0x00
  putMW256 (Right w256) = putWord8 0x01 >> put (fromIntegral (fromWord256 w256) :: W.Word256)
implementationSigHash BuildTapleafSimplicity _env cmr = Just . toWord256 . integerHash256 . bsHash . runPut
                                                      $ put tag >> put tag >> putWord8 tapleafSimplicityVersion >> putWord8 32 >> put (fromW256 cmr)
 where
  tag = bsHash (fromString "TapLeaf/elements")
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
  tag = bsHash (fromString "TapBranch/elements")
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

implementationIssuance :: IssuanceJet a b -> PrimEnv -> a -> Maybe b
implementationIssuance Issuance env i = fmap (cast . fmap (cast . fmap toBit)) body
 where
  cast = maybe (Left ()) Right
  body = return $ fmap isRight . sigTxiIssuance <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance IssuanceEntropy env i = fmap (cast . fmap (cast . fmap fromHash)) body
 where
  cast = maybe (Left ()) Right
  fromHash = toWord256 . integerHash256
  body = return $ sigTxiIssuanceEntropy <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance IssuanceAsset env i = fmap (cast . fmap (cast . fmap fromHash)) body
 where
  cast = maybe (Left ()) Right
  fromHash = toWord256 . integerHash256
  body = return $ sigTxiIssuanceAsset <$> sigTxIn (envTx env) !? (fromIntegral (fromWord32 i))

implementationIssuance IssuanceToken env i = fmap (cast . fmap (cast . fmap fromHash)) body
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

implementationIssuance LbtcAsset _ _ = Just (fromHash lBtcAsset)
 where
  fromHash = toWord256 . integerHash256

implementationTransaction :: TransactionJet a b -> PrimEnv -> a -> Maybe b
implementationTransaction OutputIsFee env i = Just . cast $ toBit . isJust . outputFee <$> sigTxOut (envTx env) !? (fromIntegral (fromWord32 i))
 where
  cast = maybe (Left ()) Right
implementationTransaction TotalFee env x = Just . fromValue . Map.findWithDefault 0 assetId $ totalFee (envTx env)
 where
  fromValue = toWord64 . toInteger
  fromW256 = fromIntegral . fromWord256
  assetId = review (over be256) (fromW256 x)
implementationTransaction x env i = Semantics.sem (specificationTransaction x) env i

getJetBitElements :: (Monad m) => m Void -> m Bool -> m (SomeArrow ElementsJet)
getJetBitElements = getCatalogue elementsCatalogue

elementsCatalogue :: Catalogue (SomeArrow ElementsJet)
elementsCatalogue = Shelf
 [ someArrowMap SigHashJet <$> sigHashCatalogue
 , someArrowMap TimeLockJet <$> timeLockCatalogue
 , someArrowMap IssuanceJet <$> issuanceCatalogue
 , someArrowMap TransactionJet <$> transactionCatalogue
 ]
sigHashCatalogue = book
 [ SomeArrow SigAllHash
 , SomeArrow TxHash
 , SomeArrow TapEnvHash
 , SomeArrow OutputsHash
 , SomeArrow InputsHash
 , SomeArrow IssuancesHash
 , SomeArrow InputUtxosHash
 , SomeArrow OutputHash
 , SomeArrow OutputAmountsHash
 , SomeArrow OutputScriptsHash
 , SomeArrow OutputNoncesHash
 , SomeArrow OutputRangeProofsHash
 , SomeArrow OutputSurjectionProofsHash
 , SomeArrow InputHash
 , SomeArrow InputOutpointsHash
 , SomeArrow InputSequencesHash
 , SomeArrow InputAnnexesHash
 , SomeArrow InputScriptSigsHash
 , SomeArrow IssuanceHash
 , SomeArrow IssuanceAssetAmountsHash
 , SomeArrow IssuanceTokenAmountsHash
 , SomeArrow IssuanceRangeProofsHash
 , SomeArrow IssuanceBlindingEntropyHash
 , SomeArrow InputUtxoHash
 , SomeArrow InputAmountsHash
 , SomeArrow InputScriptsHash
 , SomeArrow TapleafHash
 , SomeArrow TappathHash
 , SomeArrow OutpointHash
 , SomeArrow AssetAmountHash
 , SomeArrow NonceHash
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
issuanceCatalogue = book
 [ SomeArrow Issuance
 , SomeArrow IssuanceAsset
 , SomeArrow IssuanceToken
 , SomeArrow IssuanceEntropy
 , SomeArrow CalculateIssuanceEntropy
 , SomeArrow CalculateAsset
 , SomeArrow CalculateExplicitToken
 , SomeArrow CalculateConfidentialToken
 , SomeArrow LbtcAsset
 ]
transactionCatalogue = book
 [ SomeArrow ScriptCMR
 , SomeArrow InternalKey
 , SomeArrow CurrentIndex
 , SomeArrow NumInputs
 , SomeArrow NumOutputs
 , SomeArrow LockTime
 , SomeArrow OutputAsset
 , SomeArrow OutputAmount
 , SomeArrow OutputNonce
 , SomeArrow OutputScriptHash
 , SomeArrow OutputNullDatum
 , SomeArrow OutputIsFee
 , SomeArrow OutputSurjectionProof
 , SomeArrow OutputRangeProof
 , SomeArrow TotalFee
 , SomeArrow CurrentPegin
 , SomeArrow CurrentPrevOutpoint
 , SomeArrow CurrentAsset
 , SomeArrow CurrentAmount
 , SomeArrow CurrentScriptHash
 , SomeArrow CurrentSequence
 , SomeArrow CurrentAnnexHash
 , SomeArrow CurrentScriptSigHash
 , SomeArrow CurrentReissuanceBlinding
 , SomeArrow CurrentNewIssuanceContract
 , SomeArrow CurrentReissuanceEntropy
 , SomeArrow CurrentIssuanceAssetAmount
 , SomeArrow CurrentIssuanceTokenAmount
 , SomeArrow CurrentIssuanceAssetProof
 , SomeArrow CurrentIssuanceTokenProof
 , SomeArrow InputPegin
 , SomeArrow InputPrevOutpoint
 , SomeArrow InputAsset
 , SomeArrow InputAmount
 , SomeArrow InputScriptHash
 , SomeArrow InputSequence
 , SomeArrow InputAnnexHash
 , SomeArrow InputScriptSigHash
 , SomeArrow ReissuanceBlinding
 , SomeArrow NewIssuanceContract
 , SomeArrow ReissuanceEntropy
 , SomeArrow IssuanceAssetAmount
 , SomeArrow IssuanceTokenAmount
 , SomeArrow IssuanceAssetProof
 , SomeArrow IssuanceTokenProof
 , SomeArrow TapleafVersion
 , SomeArrow Tappath
 , SomeArrow Version
 , SomeArrow GenesisBlockHash
 , SomeArrow TransactionId
 ]

putJetBitElements :: ElementsJet a b -> DList Bool
putJetBitElements (SigHashJet x)     = putPositive 1 . putJetBitSigHash x
putJetBitElements (TimeLockJet x)    = putPositive 2 . putJetBitTimeLock x
putJetBitElements (IssuanceJet x)    = putPositive 3 . putJetBitIssuance x
putJetBitElements (TransactionJet x) = putPositive 4 . putJetBitTransaction x

putJetBitSigHash :: SigHashJet a b -> DList Bool
putJetBitSigHash SigAllHash                  = putPositive 1
putJetBitSigHash TxHash                      = putPositive 2
putJetBitSigHash TapEnvHash                  = putPositive 3
putJetBitSigHash OutputsHash                 = putPositive 4
putJetBitSigHash InputsHash                  = putPositive 5
putJetBitSigHash IssuancesHash               = putPositive 6
putJetBitSigHash InputUtxosHash              = putPositive 7
putJetBitSigHash OutputHash                  = putPositive 8
putJetBitSigHash OutputAmountsHash           = putPositive 9
putJetBitSigHash OutputScriptsHash           = putPositive 10
putJetBitSigHash OutputNoncesHash            = putPositive 11
putJetBitSigHash OutputRangeProofsHash       = putPositive 12
putJetBitSigHash OutputSurjectionProofsHash  = putPositive 13
putJetBitSigHash InputHash                   = putPositive 14
putJetBitSigHash InputOutpointsHash          = putPositive 15
putJetBitSigHash InputSequencesHash          = putPositive 16
putJetBitSigHash InputAnnexesHash            = putPositive 17
putJetBitSigHash InputScriptSigsHash         = putPositive 18
putJetBitSigHash IssuanceHash                = putPositive 19
putJetBitSigHash IssuanceAssetAmountsHash    = putPositive 20
putJetBitSigHash IssuanceTokenAmountsHash    = putPositive 21
putJetBitSigHash IssuanceRangeProofsHash     = putPositive 22
putJetBitSigHash IssuanceBlindingEntropyHash = putPositive 23
putJetBitSigHash InputUtxoHash               = putPositive 24
putJetBitSigHash InputAmountsHash            = putPositive 25
putJetBitSigHash InputScriptsHash            = putPositive 26
putJetBitSigHash TapleafHash                 = putPositive 27
putJetBitSigHash TappathHash                 = putPositive 28
putJetBitSigHash OutpointHash                = putPositive 29
putJetBitSigHash AssetAmountHash             = putPositive 30
putJetBitSigHash NonceHash                   = putPositive 31
putJetBitSigHash AnnexHash                   = putPositive 32
putJetBitSigHash BuildTapleafSimplicity      = putPositive 33
putJetBitSigHash BuildTapbranch              = putPositive 34
putJetBitSigHash BuildTaptweak               = putPositive 35

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

putJetBitIssuance :: IssuanceJet a b -> DList Bool
putJetBitIssuance Issuance                   = putPositive 1
putJetBitIssuance IssuanceAsset              = putPositive 2
putJetBitIssuance IssuanceToken              = putPositive 3
putJetBitIssuance IssuanceEntropy            = putPositive 4
putJetBitIssuance CalculateIssuanceEntropy   = putPositive 5
putJetBitIssuance CalculateAsset             = putPositive 6
putJetBitIssuance CalculateExplicitToken     = putPositive 7
putJetBitIssuance CalculateConfidentialToken = putPositive 8
putJetBitIssuance LbtcAsset                  = putPositive 9

putJetBitTransaction :: TransactionJet a b -> DList Bool
putJetBitTransaction ScriptCMR                  = putPositive 1
putJetBitTransaction InternalKey                = putPositive 2
putJetBitTransaction CurrentIndex               = putPositive 3
putJetBitTransaction NumInputs                  = putPositive 4
putJetBitTransaction NumOutputs                 = putPositive 5
putJetBitTransaction LockTime                   = putPositive 6
putJetBitTransaction OutputAsset                = putPositive 7
putJetBitTransaction OutputAmount               = putPositive 8
putJetBitTransaction OutputNonce                = putPositive 9
putJetBitTransaction OutputScriptHash           = putPositive 10
putJetBitTransaction OutputNullDatum            = putPositive 11
putJetBitTransaction OutputIsFee                = putPositive 12
putJetBitTransaction OutputSurjectionProof      = putPositive 13
putJetBitTransaction OutputRangeProof           = putPositive 14
putJetBitTransaction TotalFee                   = putPositive 15
putJetBitTransaction CurrentPegin               = putPositive 16
putJetBitTransaction CurrentPrevOutpoint        = putPositive 17
putJetBitTransaction CurrentAsset               = putPositive 18
putJetBitTransaction CurrentAmount              = putPositive 19
putJetBitTransaction CurrentScriptHash          = putPositive 20
putJetBitTransaction CurrentSequence            = putPositive 21
putJetBitTransaction CurrentAnnexHash           = putPositive 22
putJetBitTransaction CurrentScriptSigHash       = putPositive 23
putJetBitTransaction CurrentReissuanceBlinding  = putPositive 24
putJetBitTransaction CurrentNewIssuanceContract = putPositive 25
putJetBitTransaction CurrentReissuanceEntropy   = putPositive 26
putJetBitTransaction CurrentIssuanceAssetAmount = putPositive 27
putJetBitTransaction CurrentIssuanceTokenAmount = putPositive 28
putJetBitTransaction CurrentIssuanceAssetProof  = putPositive 29
putJetBitTransaction CurrentIssuanceTokenProof  = putPositive 30
putJetBitTransaction InputPegin                 = putPositive 31
putJetBitTransaction InputPrevOutpoint          = putPositive 32
putJetBitTransaction InputAsset                 = putPositive 33
putJetBitTransaction InputAmount                = putPositive 34
putJetBitTransaction InputScriptHash            = putPositive 35
putJetBitTransaction InputSequence              = putPositive 36
putJetBitTransaction InputAnnexHash             = putPositive 37
putJetBitTransaction InputScriptSigHash         = putPositive 38
putJetBitTransaction ReissuanceBlinding         = putPositive 39
putJetBitTransaction NewIssuanceContract        = putPositive 40
putJetBitTransaction ReissuanceEntropy          = putPositive 41
putJetBitTransaction IssuanceAssetAmount        = putPositive 42
putJetBitTransaction IssuanceTokenAmount        = putPositive 43
putJetBitTransaction IssuanceAssetProof         = putPositive 44
putJetBitTransaction IssuanceTokenProof         = putPositive 45
putJetBitTransaction TapleafVersion             = putPositive 46
putJetBitTransaction Tappath                    = putPositive 47
putJetBitTransaction Version                    = putPositive 48
putJetBitTransaction GenesisBlockHash           = putPositive 49
putJetBitTransaction TransactionId              = putPositive 50

elementsJetMap :: Map.Map Hash256 (SomeArrow ElementsJet)
elementsJetMap = Map.fromList . fmap mkAssoc $ toList elementsCatalogue
 where
  mkAssoc :: SomeArrow ElementsJet -> (Hash256, (SomeArrow ElementsJet))
  mkAssoc wrapped@(SomeArrow jt) = (identityRoot (specificationElements jt), wrapped)

data MatcherInfo a b = MatcherInfo (Product ConstWord IdentityRoot a b)

instance Simplicity.Elements.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (ConstWordJet cw) = CoreJets.specificationConstWord cw
  specification (CoreJet jt) = CoreJets.specification jt
  specification (ElementsJet jt) = specificationElements jt

  implementation (ConstWordJet cw) _env = CoreJets.implementationConstWord cw
  implementation (CoreJet jt) _env = CoreJets.implementation jt
  implementation (ElementsJet jt) env = implementationElements jt env

  matcher (MatcherInfo (Product cw ir)) = (do
    SomeArrow jt <- Map.lookup (identityRoot ir) jetMap
    let (ira, irb) = reifyArrow ir
    let (jta, jtb) = reifyArrow jt
    -- If the error below is thrown it suggests there is some sort of type annotation mismatch in the map below
    case (equalTyReflect ira jta, equalTyReflect irb jtb) of
      (Just Refl, Just Refl) -> return jt
      otherwise -> error "mathcher{Simplicity.Elements.Jets.JetType}: type match error"
    ) <|> case cw of
      (ConstWord w v) -> return (ConstWordJet (ConstWordContent w v))
      otherwise -> Nothing

  getJetBit abort next = do
    b <- next
    if b then do
               c <- next
               if c then someArrowMap ElementsJet <$> getJetBitElements abort next
                    else someArrowMap CoreJet <$> CoreJets.getJetBit abort next
         else mkConstWordJet <$> CoreJets.getConstWordBit abort next
   where
    mkConstWordJet (SomeConstWordContent cw) = SomeArrow (ConstWordJet cw)

  putJetBit = go
   where
    go (ConstWordJet cw) = ([o]++) . CoreJets.putConstWordBit cw
    go (CoreJet jt) = ([i,o]++) . CoreJets.putJetBit jt
    go (ElementsJet jt) = ([i,i]++) . putJetBitElements jt
    (o,i) = (False,True)

  jetCost (ConstWordJet cw) = CoreJets.costConstWord cw
  jetCost (CoreJet jt) = CoreJets.jetCost jt
  jetCost (ElementsJet jt) = jetCostElements jt

jetCostElements :: ElementsJet a b -> Weight
jetCostElements (SigHashJet x) = jetCostSigHash x
jetCostElements (TimeLockJet x) = jetCostTimeLock x
jetCostElements (IssuanceJet x) = jetCostIssuance x
jetCostElements (TransactionJet x) = jetCostTransaction x

jetCostSigHash :: SigHashJet a b -> Weight
jetCostSigHash SigAllHash = Benchmarks.cost "SigAllHash"
jetCostSigHash TxHash = Benchmarks.cost "TxHash"
jetCostSigHash TapEnvHash = Benchmarks.cost "TapEnvHash"
jetCostSigHash OutputsHash = Benchmarks.cost "OutputsHash"
jetCostSigHash InputsHash = Benchmarks.cost "InputsHash"
jetCostSigHash IssuancesHash = Benchmarks.cost "IssuancesHash"
jetCostSigHash InputUtxosHash = Benchmarks.cost "InputUtxosHash"
jetCostSigHash OutputHash = Benchmarks.cost "OutputHash"
jetCostSigHash OutputAmountsHash = Benchmarks.cost "OutputAmountsHash"
jetCostSigHash OutputScriptsHash = Benchmarks.cost "OutputScriptsHash"
jetCostSigHash OutputNoncesHash = Benchmarks.cost "OutputNoncesHash"
jetCostSigHash OutputRangeProofsHash = Benchmarks.cost "OutputRangeProofsHash"
jetCostSigHash OutputSurjectionProofsHash = Benchmarks.cost "OutputSurjectionProofsHash"
jetCostSigHash InputHash = Benchmarks.cost "InputHash"
jetCostSigHash InputOutpointsHash = Benchmarks.cost "InputOutpointsHash"
jetCostSigHash InputSequencesHash = Benchmarks.cost "InputSequencesHash"
jetCostSigHash InputAnnexesHash = Benchmarks.cost "InputAnnexesHash"
jetCostSigHash InputScriptSigsHash = Benchmarks.cost "InputScriptSigsHash"
jetCostSigHash IssuanceHash = Benchmarks.cost "IssuanceHash"
jetCostSigHash IssuanceAssetAmountsHash = Benchmarks.cost "IssuanceAssetAmountsHash"
jetCostSigHash IssuanceTokenAmountsHash = Benchmarks.cost "IssuanceTokenAmountsHash"
jetCostSigHash IssuanceRangeProofsHash = Benchmarks.cost "IssuanceRangeProofsHash"
jetCostSigHash IssuanceBlindingEntropyHash = Benchmarks.cost "IssuanceBlindingEntropyHash"
jetCostSigHash InputUtxoHash = Benchmarks.cost "InputUtxoHash"
jetCostSigHash InputAmountsHash = Benchmarks.cost "InputAmountsHash"
jetCostSigHash InputScriptsHash = Benchmarks.cost "InputScriptsHash"
jetCostSigHash TapleafHash = Benchmarks.cost "TapleafHash"
jetCostSigHash TappathHash = Benchmarks.cost "TappathHash"
jetCostSigHash OutpointHash = Benchmarks.cost "OutpointHash"
jetCostSigHash AssetAmountHash = Benchmarks.cost "AssetAmountHash"
jetCostSigHash NonceHash = Benchmarks.cost "NonceHash"
jetCostSigHash AnnexHash = Benchmarks.cost "AnnexHash"
jetCostSigHash BuildTapleafSimplicity = Benchmarks.cost "BuildTapleafSimplicity"
jetCostSigHash BuildTapbranch = Benchmarks.cost "BuildTapbranch"
jetCostSigHash BuildTaptweak = Benchmarks.cost "BuildTaptweak"

jetCostTimeLock :: TimeLockJet a b -> Weight
jetCostTimeLock CheckLockHeight = Benchmarks.cost "CheckLockHeight"
jetCostTimeLock CheckLockTime = Benchmarks.cost "CheckLockTime"
jetCostTimeLock CheckLockDistance = Benchmarks.cost "CheckLockDistance"
jetCostTimeLock CheckLockDuration = Benchmarks.cost "CheckLockDuration"
jetCostTimeLock TxLockHeight = Benchmarks.cost "TxLockHeight"
jetCostTimeLock TxLockTime = Benchmarks.cost "TxLockTime"
jetCostTimeLock TxLockDistance = Benchmarks.cost "TxLockDistance"
jetCostTimeLock TxLockDuration = Benchmarks.cost "TxLockDuration"
jetCostTimeLock TxIsFinal = Benchmarks.cost "TxIsFinal"

jetCostIssuance :: IssuanceJet a b -> Weight
jetCostIssuance Issuance = Benchmarks.cost "Issuance"
jetCostIssuance IssuanceAsset = Benchmarks.cost "IssuanceAsset"
jetCostIssuance IssuanceToken = Benchmarks.cost "IssuanceToken"
jetCostIssuance IssuanceEntropy = Benchmarks.cost "IssuanceEntropy"
jetCostIssuance CalculateIssuanceEntropy = Benchmarks.cost "CalculateIssuanceEntropy"
jetCostIssuance CalculateAsset = Benchmarks.cost "CalculateAsset"
jetCostIssuance CalculateExplicitToken = Benchmarks.cost "CalculateExplicitToken"
jetCostIssuance CalculateConfidentialToken = Benchmarks.cost "CalculateConfidentialToken"
jetCostIssuance LbtcAsset = Benchmarks.cost "LbtcAsset"

jetCostTransaction :: TransactionJet a b -> Weight
jetCostTransaction ScriptCMR = Benchmarks.cost "ScriptCMR"
jetCostTransaction InternalKey = Benchmarks.cost "InternalKey"
jetCostTransaction CurrentIndex = Benchmarks.cost "CurrentIndex"
jetCostTransaction NumInputs = Benchmarks.cost "NumInputs"
jetCostTransaction NumOutputs = Benchmarks.cost "NumOutputs"
jetCostTransaction LockTime = Benchmarks.cost "LockTime"
jetCostTransaction OutputAsset = Benchmarks.cost "OutputAsset"
jetCostTransaction OutputAmount = Benchmarks.cost "OutputAmount"
jetCostTransaction OutputNonce = Benchmarks.cost "OutputNonce"
jetCostTransaction OutputScriptHash = Benchmarks.cost "OutputScriptHash"
jetCostTransaction OutputNullDatum = Benchmarks.cost "OutputNullDatum"
jetCostTransaction OutputIsFee = Benchmarks.cost "OutputIsFee"
jetCostTransaction OutputSurjectionProof = Benchmarks.cost "OutputSurjectionProof"
jetCostTransaction OutputRangeProof = Benchmarks.cost "OutputRangeProof"
jetCostTransaction TotalFee = Benchmarks.cost "TotalFee"
jetCostTransaction CurrentPegin = Benchmarks.cost "CurrentPegin"
jetCostTransaction CurrentPrevOutpoint = Benchmarks.cost "CurrentPrevOutpoint"
jetCostTransaction CurrentAsset = Benchmarks.cost "CurrentAsset"
jetCostTransaction CurrentAmount = Benchmarks.cost "CurrentAmount"
jetCostTransaction CurrentScriptHash = Benchmarks.cost "CurrentScriptHash"
jetCostTransaction CurrentSequence = Benchmarks.cost "CurrentSequence"
jetCostTransaction CurrentAnnexHash = Benchmarks.cost "CurrentAnnexHash"
jetCostTransaction CurrentScriptSigHash = Benchmarks.cost "CurrentScriptSigHash"
jetCostTransaction CurrentReissuanceBlinding = Benchmarks.cost "CurrentReissuanceBlinding"
jetCostTransaction CurrentNewIssuanceContract = Benchmarks.cost "CurrentNewIssuanceContract"
jetCostTransaction CurrentReissuanceEntropy = Benchmarks.cost "CurrentReissuanceEntropy"
jetCostTransaction CurrentIssuanceAssetAmount = Benchmarks.cost "CurrentIssuanceAssetAmount"
jetCostTransaction CurrentIssuanceTokenAmount = Benchmarks.cost "CurrentIssuanceTokenAmount"
jetCostTransaction CurrentIssuanceAssetProof = Benchmarks.cost "CurrentIssuanceAssetProof"
jetCostTransaction CurrentIssuanceTokenProof = Benchmarks.cost "CurrentIssuanceTokenProof"
jetCostTransaction InputPegin = Benchmarks.cost "InputPegin"
jetCostTransaction InputPrevOutpoint = Benchmarks.cost "InputPrevOutpoint"
jetCostTransaction InputAsset = Benchmarks.cost "InputAsset"
jetCostTransaction InputAmount = Benchmarks.cost "InputAmount"
jetCostTransaction InputScriptHash = Benchmarks.cost "InputScriptHash"
jetCostTransaction InputSequence = Benchmarks.cost "InputSequence"
jetCostTransaction InputAnnexHash = Benchmarks.cost "InputAnnexHash"
jetCostTransaction InputScriptSigHash = Benchmarks.cost "InputScriptSigHash"
jetCostTransaction ReissuanceBlinding = Benchmarks.cost "ReissuanceBlinding"
jetCostTransaction NewIssuanceContract = Benchmarks.cost "NewIssuanceContract"
jetCostTransaction ReissuanceEntropy = Benchmarks.cost "ReissuanceEntropy"
jetCostTransaction IssuanceAssetAmount = Benchmarks.cost "IssuanceAssetAmount"
jetCostTransaction IssuanceTokenAmount = Benchmarks.cost "IssuanceTokenAmount"
jetCostTransaction IssuanceAssetProof = Benchmarks.cost "IssuanceAssetProof"
jetCostTransaction IssuanceTokenProof = Benchmarks.cost "IssuanceTokenProof"
jetCostTransaction TapleafVersion = Benchmarks.cost "TapleafVersion"
jetCostTransaction Tappath = Benchmarks.cost "Tappath"
jetCostTransaction Version = Benchmarks.cost "Version"
jetCostTransaction GenesisBlockHash = Benchmarks.cost "GenesisBlockHash"
jetCostTransaction TransactionId = Benchmarks.cost "TransactionId"

-- | Generate a 'Jet' using the 'Simplicity.Elements.JetType.jetCost' and 'Simplicity.Elements.JetType.specification' of a 'JetType'.
asJet :: (Jet term, TyC a, TyC b) => JetType a b -> term a b
asJet = Simplicity.Elements.JetType.asJet

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

-- | Performs 'jetSubst' and then evaluates the program in the given environment to prune unused case branches,
-- which transforms some case expressions into assertions.
-- The resulting expression should always have the same CMR as the expression that 'jetSubst' would return.
pruneSubst :: JetDag JetType () () -> PrimEnv -> Maybe (WrappedSimplicity () ())
pruneSubst prog env = Dag.pruneSubst prog env ()

-- | This is an instance of 'BitString.getTermStopCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermStopCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermStopCode = BitString.getTermStopCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.getTermLengthCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermLengthCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermLengthCode = BitString.getTermLengthCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.putTermStopCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermStopCode :: (TyC a, TyC b) => JetDag JetType a b -> ([Bool],[Bool])
putTermStopCode = BitString.putTermStopCode

-- | This is an instance of 'BitString.putTermLengthCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermLengthCode :: (TyC a, TyC b) => JetDag JetType a b -> ([Bool],[Bool])
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

fromPoint (by, x) = Point (fromBit by) (fe (fromWord256 x))
fromHash = review (over be256) . fromIntegral . fromWord256
fromCtx (buffer, (count, midstate)) = ctxBuild (fromInteger . fromWord8 <$> buffer^..buffer_ buffer63)
                                               (fromWord64 count)
                                               (fromHash midstate)
toCtx ctx = (buffer, (count, midstate))
 where
  buffer = fst $ bufferFill buffer63 (toWord8 . fromIntegral <$> BS.unpack (ctxBuffer ctx))
  count = toWord64 . fromIntegral $ ctxCounter ctx
  midstate = toWord256 . integerHash256 . ivHash $ ctxIV ctx
