{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.SigHash
 ( Lib(Lib), mkLib
 , outputAmountsHash, outputNoncesHash, outputScriptsHash
 , outputRangeProofsHash, outputSurjectionProofsHash, outputsHash, outputHash
 , inputAmountsHash, inputScriptsHash, inputUtxosHash, inputUtxoHash
 , inputOutpointsHash, inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash, inputHash
 , issuanceAssetAmountsHash, issuanceTokenAmountsHash, issuanceRangeProofsHash, issuanceBlindingEntropyHash, issuancesHash, issuanceHash
 , txHash
 , tapleafHash, tappathHash, tapEnvHash
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
  { -- | A hash of all 'Transaction.outputAmount's.
    outputAmountsHash :: term () Word256
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
    -- * 'outputAmountsHash'
    -- * 'outputNoncesHash'
    -- * 'outputScriptsHash'
    -- * 'outputRangeProofsHash'
    --
    -- Note that 'outputSurjectionProofsHash' is excluded.
  , outputsHash :: term () Word256
    -- | If the given output index exists, returns a hash of
    --
    -- * The serialization of the output's asset and amount fields.
    -- * The serialization of the output's nonce field.
    -- * A hash of the output's scriptPubKey.
    -- * A hash of the output's range proof.
    --
    -- Note that output's surjection proof is excluded.
  , outputHash :: term Word32 (S Word256)
    -- | A hash of all 'Transaction.inputAmount's.
  , inputAmountsHash :: term () Word256
    -- | A hash of all 'InputScriptHash's.
  , inputScriptsHash :: term () Word256
    -- | A hash of
    --
    -- * 'inputAmountsHash'
    -- * 'inputScriptsHash'
  , inputUtxosHash :: term () Word256
    -- | If the given input index exists, returns a hash of
    --
    -- * The serialization of the input UTXO's asset and amount fields.
    -- * A hash of the input UTXO's scriptPubKey.
  , inputUtxoHash :: term Word32 (S Word256)
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
    -- | If the given input index exists, returns a hash of
    --
    -- * If the input is not a pegin, then the byte 0x00.
    -- * If the input is a pegin, then the byte 0x01 followed by the parent chain's genesis hash.
    -- * The input's serialized previous transaction id.
    -- * The input's previous transaction index in big endian format.
    -- * The input's sequence number in big endian format.
    -- * If the input has no annex, or isn't a taproot spend, then the byte 0x00.
    -- * If the input has an annex, then the byte 0x01 followed by a SHA256 hash of the annex.
  , inputHash :: term Word32 (S Word256)
    -- | A hash of 'issuanceAsset' and 'IssuanceAssetAmount' pairs as an asset-amount hash.
    --
    -- Note that "null" amount is hashed as if it were an explicit zero.
    --
    -- When an input has no issuance, a pair of zero bytes, @0x00 0x00@ are hashed.
  , issuanceAssetAmountsHash :: term () Word256
    -- | A hash of 'issuanceToken' and 'IssuanceAssetAmount' pairs as an asset-amount hash.
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
    -- | If the given input index exists, returns a hash of
    --
    -- 1. The asset issuance:
    --
    --     * If the input has no issuance then the two bytes 0x00 0x00.
    --     * If the input has a new issuance then the byte 0x01 followed by a serialization of the calculated issued asset id,
    --       followed by the serialization of the (possibly confidential) issued asset amount.
    --     * If the input has a reissuance then the byte 0x01 followed by a serialization of the issued asset id,
    --       followed by the serialization of the (possibly confidential) issued asset amount.
    --
    -- 2. The token issuance:
    --
    --     * If the input has no issuance then another two bytes 0x00 0x00.
    --     * If the input has a new issuance then the byte 0x01 followed by a serialization of the calculated issued token id,
    --       followed by the serialization of the (possibly confidential) issued token amount.
    --     * If the input has a re-issuance then the byte 0x01 followed by a serialization of the issued token id,
    --       followed by the serialization of the explicit 0 amount (i.e. 0x01 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x00 )
    --
    -- 3. The range proofs:
    --
    --     * A hash of the range proof of the input's issuance asset amount.
    --     * A hash of the range proof of the input's issuance token amount.
    --
    --    (Note: in the case of no issuese these will both be a hash of the empty proof)
    --
    -- 4. The blinding entropy:
    --
    --     * If the input has no issuance then another 0x00 byte.
    --     * If the input is a new issuance then the 0x01 byte followed by 32 0x00 bytes followed by the new issuance's contract hash field.
    --     * If the input is a reissuance then the 0x01 byte followed by the reissuance's blinding nonce field followed by the reissuance's entropy field.
  , issuanceHash :: term Word32 (S Word256)
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
    -- | A hash of all 'Tappath's.
  , tappathHash :: term () Word256
    -- | A hash of
    --
    -- * 'tapleafHash'
    -- * 'tappathHash'
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
    { outputAmountsHash = m outputAmountsHash
    , outputNoncesHash = m outputNoncesHash
    , outputScriptsHash = m outputScriptsHash
    , outputRangeProofsHash = m outputRangeProofsHash
    , outputSurjectionProofsHash = m outputSurjectionProofsHash
    , outputsHash = m outputsHash
    , outputHash = m outputHash
    , inputAmountsHash = m inputAmountsHash
    , inputScriptsHash = m inputScriptsHash
    , inputUtxosHash = m inputUtxosHash
    , inputUtxoHash = m inputUtxoHash
    , inputOutpointsHash = m inputOutpointsHash
    , inputSequencesHash = m inputSequencesHash
    , inputAnnexesHash = m inputAnnexesHash
    , inputsHash = m inputsHash
    , inputHash = m inputHash
    , issuanceAssetAmountsHash = m issuanceAssetAmountsHash
    , issuanceTokenAmountsHash = m issuanceTokenAmountsHash
    , issuanceRangeProofsHash = m issuanceRangeProofsHash
    , issuanceBlindingEntropyHash = m issuanceBlindingEntropyHash
    , issuancesHash = m issuancesHash
    , issuanceHash = m issuanceHash
    , inputScriptSigsHash = m inputScriptSigsHash
    , txHash = m txHash
    , tapleafHash = m tapleafHash
    , tappathHash = m tappathHash
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
    outputAmountsHash =
     let
       finalize = ctx8Finalize
       body = take (drop outputAmount) &&& ih
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

  , outputsHash = ctx8Init &&& ((outputAmountsHash &&& outputNoncesHash) &&& (outputScriptsHash &&& outputRangeProofsHash))
              >>> ctx8Addn vector128 >>> ctx8Finalize

  , outputHash = (outputAmount &&& (primitive OutputNonce &&& primitive OutputScriptHash &&& primitive OutputRangeProof))
             >>> match (injl unit)
                       (injr (((((unit >>> ctx8Init) &&& oh >>> assetAmountHash)
                     &&& (drop . take . assert $ iden) >>> nonceHash)
                     &&& (drop . drop . take . assert $ iden) >>> ctx8Add32)
                     &&& (drop . drop . drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))

  , inputAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop inputAmount) &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , inputScriptsHash = hashWord256s32 (drop (primitive InputScriptHash))

  , inputUtxosHash = ctx8Init &&& (inputAmountsHash &&& inputScriptsHash) >>> ctx8Addn vector64 >>> ctx8Finalize

  , inputUtxoHash = (inputAmount &&& primitive InputScriptHash)
             >>> match (injl unit)
                       (injr (((unit >>> ctx8Init) &&& oh >>> assetAmountHash)
                         &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))

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

  , inputHash = (primitive InputPegin &&& (primitive InputPrevOutpoint &&& primitive InputSequence &&& primitive InputAnnexHash))
            >>> match (injl unit)
                      (injr ((((unit >>> ctx8Init)
                    &&& (oh &&& (drop . take . assert $ iden)) >>> outpointHash)
                    &&& (drop . drop . take . assert $ iden) >>> ctx8Add4)
                    &&& (drop . drop . drop . assert $ iden) >>> annexHash >>> ctx8Finalize))
    -- Note a "null" amount is serialized as an explicit value of 0.  The asset id is still serialized in this case.
    -- Only when there is no issuance are two "null" values (i.e. 0x00 0x00) are serialized.
  , issuanceAssetAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop issuanceAssetAmount) &&& ih >>> match (injl ih) (injr (ih &&& oh >>> issuanceAssetAmountHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuanceTokenAmountsHash =
     let
      finalize = ctx8Finalize
      body = take (drop issuanceTokenAmount) &&& ih >>> match (injl ih) (injr (ih &&& oh >>> issuanceAssetAmountHash))
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
      body = take (drop issuanceBlindingEntropy) &&& ih
         >>> match (injl ih) (injr (ih &&& oh >>> blindingEntropyHash))
     in
      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize

  , issuancesHash = (ctx8Init &&& ((issuanceAssetAmountsHash &&& issuanceTokenAmountsHash) &&& (issuanceRangeProofsHash &&& issuanceBlindingEntropyHash)) >>> ctx8Addn vector128) >>> ctx8Finalize

  , issuanceHash = issuanceAssetAmount &&& issuanceTokenAmount &&& (primitive IssuanceAssetProof &&& primitive IssuanceTokenProof) &&& issuanceBlindingEntropy
             >>> match (injl unit)
                       (injr ((((((unit >>> ctx8Init) &&& oh >>> issuanceAssetAmountHash)
                         &&& (drop . take . assert $ iden) >>> issuanceAssetAmountHash)
                         &&& (drop . drop . take . take . assert $ iden) >>> ctx8Add32)
                         &&& (drop . drop . take . drop . assert $ iden) >>> ctx8Add32)
                         &&& (drop . drop . drop . assert $ iden) >>> blindingEntropyHash >>> ctx8Finalize))

  , txHash = ((ctx8Init &&& (primitive Version &&& primitive LockTime) >>> ctx8Addn vector8)
         &&& ((inputsHash &&& outputsHash) &&& (issuancesHash &&& outputSurjectionProofsHash)) >>> ctx8Addn vector128)
         &&& inputUtxosHash >>> ctx8Addn vector32 >>> ctx8Finalize

  , tapleafHash = ((Sha256.ctx8InitTag "TapLeaf/elements")
              &&& (primitive TapleafVersion &&& scribe (toWord8 32)) >>> ctx8Addn vector2)
              &&& (primitive ScriptCMR) >>> ctx8Addn vector32 >>> ctx8Finalize

  , tappathHash = hashWord256s8 (drop (primitive Tappath))

  , tapEnvHash = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)
             &&& (tappathHash &&& primitive InternalKey) >>> ctx8Addn vector64 >>> ctx8Finalize

  , sigAllHash = (ctx8Init &&& ((primitive GenesisBlockHash >>> iden &&& iden) &&& (txHash &&& tapEnvHash)) >>> ctx8Addn vector128)
             &&& primitive CurrentIndex >>> ctx8Addn vector4 >>> ctx8Finalize
  }
  hashLoop256 :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term (c, Ctx8) Ctx8
  hashLoop256 = Sha256.hashLoop vector32
  hashWord256s :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term c Word256
  hashWord256s w array = iden &&& (unit >>> ctx8Init) >>> hashLoop256 w array >>> ctx8Finalize
  hashWord256s32 = hashWord256s word32
  hashWord256s8 = hashWord256s word8
  hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize
  ctx8Add4 = ctx8Addn vector4
  ctx8Add32 = ctx8Addn vector32
  ctx8Add64 = ctx8Addn vector64
  issuanceAssetAmount = issuanceAsset &&& primitive IssuanceAssetAmount
                    >>> match (injl unit) (match (injr (injl unit)) (ih &&& oh
                    >>> match (injl unit) (match (injl unit) (injr (injr (ih &&& oh))))))
  issuanceTokenAmount = issuanceToken &&& primitive IssuanceTokenAmount
                    >>> match (injl unit) (match (injr (injl unit)) (ih &&& oh
                    >>> match (injl unit) (match (injl unit) (injr (injr (ih &&& oh))))))
  issuanceAssetAmountHash = ih &&& oh
         >>> match (ih &&& (unit >>> zero word16) >>> ctx8Addn vector2)
                   (ih &&& (injr ooh &&& oih) >>> assetAmountHash)
  issuanceBlindingEntropy =
    let issuanceEntropyBody = match (injl unit) (match (injr (injl unit)) ((ih &&& oh)
                            >>> match (injl unit) (injr (match (injl unit) (injr (ih &&& oh))))))
    in primitive NewIssuanceContract &&& primitive ReissuanceBlinding &&& primitive ReissuanceEntropy
   >>> match (injl unit) (match (drop issuanceEntropyBody) (injr (injr ((unit >>> zero word256) &&& oh))))
  blindingEntropyHash = ih &&& oh
                    >>> match (drop (iden &&& (unit >>> zero word8) >>> ctx8Add1))
                              (drop (iden &&& (unit >>> one word8) >>> ctx8Add1) &&& oh >>> ctx8Add64)

-- | An instance of the SigHash 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: (Assert term, Primitive term) => Lib term
lib = mkLib Sha256.lib Sha256.libAssert Transaction.lib
