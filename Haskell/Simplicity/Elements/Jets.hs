-- | This module provides a canonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Elements.Jets
  ( JetType(..), ElementsJet(..), SigHashJet(..), TimeLockJet(..), IssuanceJet(..), TransactionJet(..)
  , elementsCatalogue
  , asJet
  , jetSubst, pruneSubst
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

import Simplicity.Digest
import Simplicity.CoreJets
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Elements.Benchmarks
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
import Simplicity.Programs.Sha256.Lib (Ctx8)
import qualified Simplicity.Programs.Elements.Lib as Prog
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

-- | A type of tokens for the canonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
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
implementationSigHash OutpointHash _env (ctx, (mw256, op)) = toCtx8 <$> (flip ctxAdd (runPut (putMW256 mw256 >> putOutpointBE (cast op))) =<< fromCtx8 ctx)
 where
  putMW256 (Left _) = putWord8 0x00
  putMW256 (Right w256) = putWord8 0x01 >> put (fromIntegral (fromWord256 w256) :: W.Word256)
  cast (h, i) = Outpoint (review (over be256) (fromW256 h)) (fromW32 i)
  fromW256 = fromIntegral . fromWord256
  fromW32 = fromIntegral . fromWord32
implementationSigHash AssetAmountHash _env (ctx, (cw256, cw64)) = toCtx8 <$> (flip ctxAdd (runPut (put256 cw256 >> put64 cw64)) =<< fromCtx8 ctx)
 where
  put256 (Left (by, x)) = putWord8 (if fromBit by then 0xb else 0x0a) >> put (fromW256 x)
  put256 (Right w256) = putWord8 0x01 >> put (fromW256 w256)
  put64 (Left (by, x)) = putWord8 (if fromBit by then 0x9 else 0x08) >> put (fromW256 x)
  put64 (Right w64) = putWord8 0x01 >> put (fromW64 w64)
  fromW256 :: Word256 -> W.Word256
  fromW256 = fromIntegral . fromWord256
  fromW64 :: Word64 -> W.Word64
  fromW64 = fromIntegral . fromWord64
implementationSigHash NonceHash _env (ctx, mcw256) = toCtx8 <$> (flip ctxAdd (runPut . putNonce $ nonce) =<< fromCtx8 ctx)
 where
  nonce = either (const Nothing) (Just . Nonce . ((fromBit *** (fromIntegral . fromWord256)) +++ fromHash)) mcw256
implementationSigHash AnnexHash _env (ctx, mw256) = toCtx8 <$> (flip ctxAdd (runPut . putMW256 $ mw256) =<< fromCtx8 ctx)
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
  mkAssoc wrapped@(SomeArrow jt) = (identityHash (specificationElements jt), wrapped)

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
    SomeArrow jt <- Map.lookup (identityHash ir) jetMap
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

  jetCost (ConstWordJet cw) = jetCostConstWord cw
  jetCost (CoreJet jt) = jetCostCore jt
  jetCost (ElementsJet jt) = jetCostElements jt

-- | Generate a 'Jet' using the 'Simplicity.Elements.JetType.jetCost' and 'Simplicity.Elements.JetType.specification' of a 'JetType'.
asJet :: (Jet term, TyC a, TyC b) => JetType a b -> term a b
asJet = Simplicity.Elements.JetType.asJet

-- This map is used in the 'matcher' method above.
-- We have floated it out here to make sure the map is shared between invocations of the 'matcher' function.
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

-- | This is an instance of 'BitString.getTermLengthCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermLengthCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermLengthCode = BitString.getTermLengthCode (Proxy :: Proxy (SomeArrow JetType))

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
jetCostCore (BitcoinJet x) = jetCostBitcoin x

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

jetCostBitcoin :: BitcoinJet a b -> Weight
jetCostBitcoin ParseLock = cost "ParseLock"
jetCostBitcoin ParseSequence = cost "ParseSequence"
jetCostBitcoin TapdataInit = cost "TapdataInit"

jetCostElements :: ElementsJet a b -> Weight
jetCostElements (SigHashJet x) = jetCostSigHash x
jetCostElements (TimeLockJet x) = jetCostTimeLock x
jetCostElements (IssuanceJet x) = jetCostIssuance x
jetCostElements (TransactionJet x) = jetCostTransaction x

jetCostSigHash :: SigHashJet a b -> Weight
jetCostSigHash SigAllHash = cost "SigAllHash"
jetCostSigHash TxHash = cost "TxHash"
jetCostSigHash TapEnvHash = cost "TapEnvHash"
jetCostSigHash OutputsHash = cost "OutputsHash"
jetCostSigHash InputsHash = cost "InputsHash"
jetCostSigHash IssuancesHash = cost "IssuancesHash"
jetCostSigHash InputUtxosHash = cost "InputUtxosHash"
jetCostSigHash OutputHash = cost "OutputHash"
jetCostSigHash OutputAmountsHash = cost "OutputAmountsHash"
jetCostSigHash OutputScriptsHash = cost "OutputScriptsHash"
jetCostSigHash OutputNoncesHash = cost "OutputNoncesHash"
jetCostSigHash OutputRangeProofsHash = cost "OutputRangeProofsHash"
jetCostSigHash OutputSurjectionProofsHash = cost "OutputSurjectionProofsHash"
jetCostSigHash InputHash = cost "InputHash"
jetCostSigHash InputOutpointsHash = cost "InputOutpointsHash"
jetCostSigHash InputSequencesHash = cost "InputSequencesHash"
jetCostSigHash InputAnnexesHash = cost "InputAnnexesHash"
jetCostSigHash InputScriptSigsHash = cost "InputScriptSigsHash"
jetCostSigHash IssuanceHash = cost "IssuanceHash"
jetCostSigHash IssuanceAssetAmountsHash = cost "IssuanceAssetAmountsHash"
jetCostSigHash IssuanceTokenAmountsHash = cost "IssuanceTokenAmountsHash"
jetCostSigHash IssuanceRangeProofsHash = cost "IssuanceRangeProofsHash"
jetCostSigHash IssuanceBlindingEntropyHash = cost "IssuanceBlindingEntropyHash"
jetCostSigHash InputUtxoHash = cost "InputUtxoHash"
jetCostSigHash InputAmountsHash = cost "InputAmountsHash"
jetCostSigHash InputScriptsHash = cost "InputScriptsHash"
jetCostSigHash TapleafHash = cost "TapleafHash"
jetCostSigHash TappathHash = cost "TappathHash"
jetCostSigHash OutpointHash = cost "OutpointHash"
jetCostSigHash AssetAmountHash = cost "AssetAmountHash"
jetCostSigHash NonceHash = cost "NonceHash"
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

jetCostIssuance :: IssuanceJet a b -> Weight
jetCostIssuance Issuance = cost "Issuance"
jetCostIssuance IssuanceAsset = cost "IssuanceAsset"
jetCostIssuance IssuanceToken = cost "IssuanceToken"
jetCostIssuance IssuanceEntropy = cost "IssuanceEntropy"
jetCostIssuance CalculateIssuanceEntropy = cost "CalculateIssuanceEntropy"
jetCostIssuance CalculateAsset = cost "CalculateAsset"
jetCostIssuance CalculateExplicitToken = cost "CalculateExplicitToken"
jetCostIssuance CalculateConfidentialToken = cost "CalculateConfidentialToken"
jetCostIssuance LbtcAsset = cost "LbtcAsset"

jetCostTransaction :: TransactionJet a b -> Weight
jetCostTransaction ScriptCMR = cost "ScriptCMR"
jetCostTransaction InternalKey = cost "InternalKey"
jetCostTransaction CurrentIndex = cost "CurrentIndex"
jetCostTransaction NumInputs = cost "NumInputs"
jetCostTransaction NumOutputs = cost "NumOutputs"
jetCostTransaction LockTime = cost "LockTime"
jetCostTransaction OutputAsset = cost "OutputAsset"
jetCostTransaction OutputAmount = cost "OutputAmount"
jetCostTransaction OutputNonce = cost "OutputNonce"
jetCostTransaction OutputScriptHash = cost "OutputScriptHash"
jetCostTransaction OutputNullDatum = cost "OutputNullDatum"
jetCostTransaction OutputIsFee = cost "OutputIsFee"
jetCostTransaction OutputSurjectionProof = cost "OutputSurjectionProof"
jetCostTransaction OutputRangeProof = cost "OutputRangeProof"
jetCostTransaction TotalFee = cost "TotalFee"
jetCostTransaction CurrentPegin = cost "CurrentPegin"
jetCostTransaction CurrentPrevOutpoint = cost "CurrentPrevOutpoint"
jetCostTransaction CurrentAsset = cost "CurrentAsset"
jetCostTransaction CurrentAmount = cost "CurrentAmount"
jetCostTransaction CurrentScriptHash = cost "CurrentScriptHash"
jetCostTransaction CurrentSequence = cost "CurrentSequence"
jetCostTransaction CurrentAnnexHash = cost "CurrentAnnexHash"
jetCostTransaction CurrentScriptSigHash = cost "CurrentScriptSigHash"
jetCostTransaction CurrentReissuanceBlinding = cost "CurrentReissuanceBlinding"
jetCostTransaction CurrentNewIssuanceContract = cost "CurrentNewIssuanceContract"
jetCostTransaction CurrentReissuanceEntropy = cost "CurrentReissuanceEntropy"
jetCostTransaction CurrentIssuanceAssetAmount = cost "CurrentIssuanceAssetAmount"
jetCostTransaction CurrentIssuanceTokenAmount = cost "CurrentIssuanceTokenAmount"
jetCostTransaction CurrentIssuanceAssetProof = cost "CurrentIssuanceAssetProof"
jetCostTransaction CurrentIssuanceTokenProof = cost "CurrentIssuanceTokenProof"
jetCostTransaction InputPegin = cost "InputPegin"
jetCostTransaction InputPrevOutpoint = cost "InputPrevOutpoint"
jetCostTransaction InputAsset = cost "InputAsset"
jetCostTransaction InputAmount = cost "InputAmount"
jetCostTransaction InputScriptHash = cost "InputScriptHash"
jetCostTransaction InputSequence = cost "InputSequence"
jetCostTransaction InputAnnexHash = cost "InputAnnexHash"
jetCostTransaction InputScriptSigHash = cost "InputScriptSigHash"
jetCostTransaction ReissuanceBlinding = cost "ReissuanceBlinding"
jetCostTransaction NewIssuanceContract = cost "NewIssuanceContract"
jetCostTransaction ReissuanceEntropy = cost "ReissuanceEntropy"
jetCostTransaction IssuanceAssetAmount = cost "IssuanceAssetAmount"
jetCostTransaction IssuanceTokenAmount = cost "IssuanceTokenAmount"
jetCostTransaction IssuanceAssetProof = cost "IssuanceAssetProof"
jetCostTransaction IssuanceTokenProof = cost "IssuanceTokenProof"
jetCostTransaction TapleafVersion = cost "TapleafVersion"
jetCostTransaction Tappath = cost "Tappath"
jetCostTransaction Version = cost "Version"
jetCostTransaction GenesisBlockHash = cost "GenesisBlockHash"
jetCostTransaction TransactionId = cost "TransactionId"
