{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.SigHash
 ( Lib(Lib), mkLib
 , outputAssetAmountsHash, outputNoncesHash, outputScriptsHash
 , outputRangeProofsHash, outputSurjectionProofsHash, outputsHash
 , inputAssetAmountsHash, inputScriptsHash, inputUtxosHash
 , inputOutpointsHash, inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash
 , issuanceAssetAmountsHash, issuanceTokenAmountsHash, issuanceRangeProofsHash, issuanceBlindingEntropyHash, issuancesHash
 , txHash
 , tapleafHash, tapbranchHash, tapEnvHash
 , sigAllHash
 -- * Example instances
 , lib
 ) where

import Prelude hiding (Word, all, drop, max, not, take)
import Data.String (fromString)

import Simplicity.Digest
import Simplicity.Elements.Primitive
import Simplicity.Elements.Term hiding (one)
import Simplicity.Functor
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 (Ctx8)
import Simplicity.Elements.Programs.Issuance.Lib
import qualified Simplicity.Elements.Programs.Transaction as Transaction
import Simplicity.Programs.Elements.Lib

data Lib term =
 Lib
  { -- | A hash of all 'Transaction.outputAssetAmount's.
    outputAssetAmountsHash :: term () Word256
    -- | A hash of all 'OutputNonce's.
  , outputNoncesHash :: term () Word256
    -- | A hash of all 'OutputScriptHash's.
  , outputScriptsHash :: term () Word256
    -- | A hash of all 'OutputRangeProofHash's.
  , outputRangeProofsHash :: term () Word256
    -- | A hash of all 'OutputSurjectionProofHash's.
  , outputSurjectionProofsHash :: term () Word256
    -- | A hash of
    --
    -- * 'outputAssetAmountsHash'
    -- * 'outputNoncesHash'
    -- * 'outputScriptsHash'
    -- * 'outputRangeProofsHash'
    --
    -- Note that 'outputSurjectionProofsHash' is excluded.
  , outputsHash :: term () Word256
    -- | A hash of all 'Transaction.inputAssetAmount's.
  , inputAssetAmountsHash :: term () Word256
    -- | A hash of all 'InputScriptHash's.
  , inputScriptsHash :: term () Word256
    -- | A hash of
    --
    -- * 'inputAssetAmountsHash'
    -- * 'inputScriptsHash'
  , inputUtxosHash :: term () Word256
    -- | A hash of all 'InputPegin' and 'InputPrevOutpoint' pairs.
  , inputOutpointsHash :: term () Word256
    -- | A hash of all 'InputSequence's.
  , inputSequencesHash :: term () Word256
    -- | A hash of all 'InputAnnexHash's.
  , inputAnnexesHash :: term () Word256
    -- | A hash of all 'InputScriptSigHash's.
  , inputScriptSigsHash :: term () Word256
    -- | A hash of
    --
    -- * 'inputOutpointsHash'
    -- * 'inputSequencesHash'
    -- * 'inputAnnexesHash'
    --
    -- Note that 'InputScriptSigHash' is excluded.
  , inputsHash :: term () Word256
    -- | A hash of 'issuanceAsset' and 'IssuanceAssetAmt' pairs as an asset-amount hash.
    --
    -- Note that "null" amount is hashed as if it were an explicit zero.
    --
    -- When an input has no issuance, a pair of zero bytes, @0x00 0x00@ are hashed.
  , issuanceAssetAmountsHash :: term () Word256
    -- | A hash of 'issuanceToken' and 'IssuanceAssetAmt' pairs as an asset-amount hash.
    --
    -- Note that "null" amount is hashed as if it were an explicit zero.
    --
    -- When an input has no issuance, a pair of zero bytes, @0x00 0x00@ are hashed.
  , issuanceTokenAmountsHash :: term () Word256
    -- | A hash of all 'IssuanceAssetProof' and 'IssuanceTokenProof' pairs.
  , issuanceRangeProofsHash :: term () Word256
    -- | A hash of all 'NewIssuanceContract', 'ReissuanceBlinding', 'ReissuanceBlinding' values.
  , issuanceBlindingEntropyHash :: term () Word256
    -- | A hash of
    --
    -- * 'issuanceAssetAmountsHash'
    -- * 'issuanceTokenAmountsHash'
    -- * 'issuanceRangeProofsHash'
    -- * 'issuanceBlindingEntropyHash'
  , issuancesHash :: term () Word256
    -- | A hash of
    --
    -- * 'Version'
    -- * 'LockTime'
    -- * 'inputsHash'
    -- * 'outputsHash'
    -- * 'issuancesHash'
    -- * 'outputSurjectionProofsHash'
    -- * 'inputUtxosHash'
  , txHash :: term () Word256
    -- | A hash of
    --
    -- * 'TapleafVersion'
    -- * 'ScriptCMR'
  , tapleafHash :: term () Word256
    -- | A hash of all 'Tapbranch's.
  , tapbranchHash :: term () Word256
    -- | A hash of
    --
    -- * 'tapleafHash'
    -- * 'tapbranchHash'
    -- * 'InternalKey'
  , tapEnvHash :: term () Word256
    -- | A hash of
    --
    -- * 'GenesisBlockHash' twice (This is effectively a tag.)
    -- * 'tapEnvHash'
    -- * 'CurrentIndex'
  , sigAllHash :: term () Word256
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    {
      outputAssetAmountsHash = m outputAssetAmountsHash
    , outputNoncesHash = m outputNoncesHash
    , outputScriptsHash = m outputScriptsHash
    , outputRangeProofsHash = m outputRangeProofsHash
    , outputSurjectionProofsHash = m outputSurjectionProofsHash
    , outputsHash = m outputsHash
    , inputAssetAmountsHash = m inputAssetAmountsHash
    , inputScriptsHash = m inputScriptsHash
    , inputUtxosHash = m inputUtxosHash
    , inputOutpointsHash = m inputOutpointsHash
    , inputSequencesHash = m inputSequencesHash
    , inputAnnexesHash = m inputAnnexesHash
    , inputsHash = m inputsHash
    , issuanceAssetAmountsHash = m issuanceAssetAmountsHash
    , issuanceTokenAmountsHash = m issuanceTokenAmountsHash
    , issuanceRangeProofsHash = m issuanceRangeProofsHash
    , issuanceBlindingEntropyHash = m issuanceBlindingEntropyHash
    , issuancesHash = m issuancesHash
    , inputScriptSigsHash = m inputScriptSigsHash
    , txHash = m txHash
    , tapleafHash = m tapleafHash
    , tapbranchHash = m tapbranchHash
    , tapEnvHash = m tapEnvHash
    , sigAllHash = m sigAllHash
    }

mkLib :: forall term. (Assert term, Primitive term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                                    -> Sha256.LibAssert term -- ^ "Simplicity.Programs.Sha256"
                                                    -> Transaction.Lib term -- ^ "Simplicity.Elements.Programs.Transaction"
                                                    -> Lib term
mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib
 where
  lib@Lib{..} = Lib {
    outputAssetAmountsHash =
     let
       finalize = ctx8Finalize
       body = take (drop outputAssetAmount) &&& ih
          >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , outputNoncesHash =
     let
      finalize = ctx8Finalize
      body = take (drop (primitive OutputNonce)) &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> nonceHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , outputScriptsHash = hashWord256s32 (drop (primitive OutputScriptHash))

  , outputRangeProofsHash = hashWord256s32 (drop (primitive OutputRangeProof))

  , outputSurjectionProofsHash = hashWord256s32 (drop (primitive OutputSurjectionProof))

  , outputsHash = ctx8Init &&& ((outputAssetAmountsHash &&& outputNoncesHash) &&& (outputScriptsHash &&& outputRangeProofsHash))
              >>> ctx8Addn vector128 >>> ctx8Finalize

  , inputAssetAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop inputAssetAmount) &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , inputScriptsHash = hashWord256s32 (drop (primitive InputScriptHash))

  , inputUtxosHash = ctx8Init &&& (inputAssetAmountsHash &&& inputScriptsHash) >>> ctx8Addn vector64 >>> ctx8Finalize

  , inputOutpointsHash =
     let
      finalize = ctx8Finalize
      body = take (drop (primitive InputPegin)) &&& (take (drop (primitive InputPrevOutpoint)) &&& ih)
         >>> match (injl iih) (ioh &&& (oh &&& iih)
         >>> match (injl iih) (injr (iih &&& (ioh &&& oh) >>> outpointHash)))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , inputSequencesHash = hashWord32s (drop (primitive InputSequence))

  , inputAnnexesHash =
     let
      finalize = ctx8Finalize
      body = take (drop (primitive InputAnnexHash)) &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> annexHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , inputScriptSigsHash = hashWord256s32 (drop (primitive InputScriptSigHash))

  , inputsHash = (ctx8Init &&& (inputOutpointsHash &&& inputSequencesHash) >>> ctx8Addn vector64)
             &&& inputAnnexesHash >>> ctx8Addn vector32 >>> ctx8Finalize

    -- Note a "null" amount is serialized as an explicit value of 0.  The asset id is still serialized in this case.
    -- Only when there is no issuance are two "null" values (i.e. 0x00 0x00) are serialized.
  , issuanceAssetAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop issuanceAsset) &&& (take (drop (primitive IssuanceAssetAmt)) &&& ih)
         >>> match (injl iih) (match (injr (iih &&& (unit >>> zero word16) >>> ctx8Addn vector2)) (ioh &&& (oh &&& iih)
         >>> match (injl iih) (match (injl iih) (injr (iih &&& (injr ioh &&& oh) >>> assetAmountHash)))))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuanceTokenAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop issuanceToken) &&& (take (drop (primitive IssuanceTokenAmt)) &&& ih)
         >>> match (injl iih) (match (injr (iih &&& (unit >>> zero word16) >>> ctx8Addn vector2)) (ioh &&& (oh &&& iih)
         >>> match (injl iih) (match (injl iih) (injr (iih &&& (injr ioh &&& oh) >>> assetAmountHash)))))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuanceRangeProofsHash =
     let
      finalize = ctx8Finalize
      body = take (drop (primitive IssuanceAssetProof)) &&& (take (drop (primitive IssuanceTokenProof)) &&& ih)
         >>> match (injl iih) (ioh &&& (oh &&& iih)
         >>> match (injl iih) (injr (iih &&& (ioh &&& oh) >>> ctx8Addn vector64)))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuanceBlindingEntropyHash =
     let
      finalize = ctx8Finalize
      body = take (drop (primitive NewIssuanceContract)) &&& (take (drop (primitive ReissuanceBlinding)) &&& (take (drop (primitive ReissuanceEntropy)) &&& ih))
         >>> match (injl iiih) (match (drop body2) (injr ((iiih &&& (unit >>> one word8) >>> ctx8Add1) &&& ((unit >>> zero word256) &&& oh) >>> ctx8Addn vector64)))
      body2 = match (injl iih) (match (injr (iih &&& (unit >>> zero word8) >>> ctx8Add1)) (ioh &&& (oh &&& iih)
          >>> match (injl iih) (injr (match (iih &&& (unit >>> zero word8) >>> ctx8Add1) ((iih &&& (unit >>> one word8) >>> ctx8Add1) &&& (ioh &&& oh) >>> ctx8Add64)))))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuancesHash = (ctx8Init &&& ((issuanceAssetAmountsHash &&& issuanceTokenAmountsHash) &&& (issuanceRangeProofsHash &&& issuanceBlindingEntropyHash)) >>> ctx8Addn vector128) >>> ctx8Finalize

  , txHash = ((ctx8Init &&& (primitive Version &&& primitive LockTime) >>> ctx8Addn vector8)
         &&& ((inputsHash &&& outputsHash) &&& (issuancesHash &&& outputSurjectionProofsHash)) >>> ctx8Addn vector128)
         &&& inputUtxosHash >>> ctx8Addn vector32 >>> ctx8Finalize

  , tapleafHash = ((ctx8Init &&& (scribe tapleafTag &&& scribe tapleafTag) >>> ctx8Addn vector64)
              &&& (primitive TapleafVersion &&& scribe (toWord8 32)) >>> ctx8Addn vector2)
              &&& (primitive ScriptCMR) >>> ctx8Addn vector32 >>> ctx8Finalize

  , tapbranchHash = hashWord256s8 (drop (primitive Tapbranch))

  , tapEnvHash = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)
             &&& (tapbranchHash &&& primitive InternalKey) >>> ctx8Addn vector64 >>> ctx8Finalize

  , sigAllHash = (ctx8Init &&& ((primitive GenesisBlockHash >>> iden &&& iden) &&& (txHash &&& tapEnvHash)) >>> ctx8Addn vector128)
             &&& primitive CurrentIndex >>> ctx8Addn vector4 >>> ctx8Finalize
  }
  tapleafTag = toWord256 . integerHash256 . bsHash $ fromString "TapLeaf/elements"
  hashLoop256 :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term (c, Ctx8) Ctx8
  hashLoop256 = Sha256.hashLoop vector32
  hashWord256s :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term c Word256
  hashWord256s w array = iden &&& (unit >>> ctx8Init) >>> hashLoop256 w array >>> ctx8Finalize
  hashWord256s32 = hashWord256s word32
  hashWord256s8 = hashWord256s word8
  hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize
  ctx8Add64 = ctx8Addn vector64

-- | An instance of the SigHash 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: (Assert term, Primitive term) => Lib term
lib = mkLib Sha256.lib Sha256.libAssert Transaction.lib
