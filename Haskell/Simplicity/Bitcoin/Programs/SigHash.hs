{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Bitcoin.DataTypes".
module Simplicity.Bitcoin.Programs.SigHash
 ( Lib(Lib), mkLib
 , outputValuesHash, outputScriptsHash
 , outputsHash, outputHash
 , inputValuesHash, inputScriptsHash, inputUtxosHash, inputUtxoHash
 , inputOutpointsHash, inputSequencesHash, inputAnnexesHash, inputScriptSigsHash, inputsHash, inputHash
 , txHash
 , tapleafHash, tappathHash, tapEnvHash
 , sigAllHash
 -- * Example instances
 , lib
 ) where

import Prelude hiding (Word, all, drop, max, not, take)
import Data.String (fromString)

import Simplicity.Digest
import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.Term hiding (one)
import Simplicity.Functor
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 (Ctx8)
import qualified Simplicity.Bitcoin.Programs.Transaction as Transaction
import Simplicity.Programs.Bitcoin.Lib

data Lib term =
 Lib
  { -- | A hash of all 'Transaction.outputValue's.
    outputValuesHash :: term () Word256
    -- | A hash of all 'OutputScriptHash's.
  , outputScriptsHash :: term () Word256
    -- | A hash of
    --
    -- * 'outputValuesHash'
    -- * 'outputScriptsHash'
  , outputsHash :: term () Word256
    -- | If the given output index exists, returns a hash of
    --
    -- * The serialization of the output's value fields.
    -- * A hash of the output's scriptPubKey.
  , outputHash :: term Word32 (S Word256)
    -- | A hash of all 'Transaction.inputValue's.
  , inputValuesHash :: term () Word256
    -- | A hash of all 'InputScriptHash's.
  , inputScriptsHash :: term () Word256
    -- | A hash of
    --
    -- * 'inputValuesHash'
    -- * 'inputScriptsHash'
  , inputUtxosHash :: term () Word256
    -- | If the given input index exists, returns a hash of
    --
    -- * The serialization of the input UTXO's value field.
    -- * A hash of the input UTXO's scriptPubKey.
  , inputUtxoHash :: term Word32 (S Word256)
    -- | A hash of all 'InputPrevOutpoint's.
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
    -- * The input's serialized previous transaction id.
    -- * The input's previous transaction index in big endian format.
    -- * The input's sequence number in big endian format.
    -- * If the input has no annex, or isn't a taproot spend, then the byte 0x00.
    -- * If the input has an annex, then the byte 0x01 followed by a SHA256 hash of the annex.
  , inputHash :: term Word32 (S Word256)
    -- | A hash of
    --
    -- * 'Version'
    -- * 'LockTime'
    -- * 'inputsHash'
    -- * 'outputsHash'
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
    -- * 'txHash'
    -- * 'tapEnvHash'
    -- * 'CurrentIndex'
  , sigAllHash :: term () Word256
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { outputValuesHash = m outputValuesHash
    , outputScriptsHash = m outputScriptsHash
    , outputsHash = m outputsHash
    , outputHash = m outputHash
    , inputValuesHash = m inputValuesHash
    , inputScriptsHash = m inputScriptsHash
    , inputUtxosHash = m inputUtxosHash
    , inputUtxoHash = m inputUtxoHash
    , inputOutpointsHash = m inputOutpointsHash
    , inputSequencesHash = m inputSequencesHash
    , inputAnnexesHash = m inputAnnexesHash
    , inputsHash = m inputsHash
    , inputHash = m inputHash
    , inputScriptSigsHash = m inputScriptSigsHash
    , txHash = m txHash
    , tapleafHash = m tapleafHash
    , tappathHash = m tappathHash
    , tapEnvHash = m tapEnvHash
    , sigAllHash = m sigAllHash
    }

mkLib :: forall term. (Assert term, Primitive term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                                    -> Sha256.LibAssert term -- ^ "Simplicity.Programs.Sha256"
                                                    -> Transaction.Lib term -- ^ "Simplicity.Bitcoin.Programs.Transaction"
                                                    -> Lib term
mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib
 where
  lib@Lib{..} = Lib {
    outputValuesHash = hashWord64s (drop (primitive OutputValue))

  , outputScriptsHash = hashWord256s32 (drop (primitive OutputScriptHash))

  , outputsHash = ctx8Init &&& (outputValuesHash &&& outputScriptsHash) >>> ctx8Add64 >>> ctx8Finalize

  , outputHash = (primitive OutputValue &&& primitive OutputScriptHash)
             >>> match (injl unit)
                       (injr (((unit >>> ctx8Init) &&& oh >>> ctx8Add8)
                         &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))

  , inputValuesHash = hashWord64s (drop (primitive InputValue))

  , inputScriptsHash = hashWord256s32 (drop (primitive InputScriptHash))

  , inputUtxosHash = ctx8Init &&& (inputValuesHash &&& inputScriptsHash) >>> ctx8Addn vector64 >>> ctx8Finalize

  , inputUtxoHash = (primitive InputValue &&& primitive InputScriptHash)
             >>> match (injl unit)
                       (injr (((unit >>> ctx8Init) &&& oh >>> ctx8Add8)
                         &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))

  , inputOutpointsHash =
     let
      finalize = ctx8Finalize
      body = (take (drop (primitive InputPrevOutpoint)) &&& ih)
         >>> match (injl ih) (injr (ih &&& oh >>> outpointHash))
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

  , inputHash = (primitive InputPrevOutpoint &&& (primitive InputSequence &&& primitive InputAnnexHash))
            >>> match (injl unit)
                      (injr ((((unit >>> ctx8Init) &&& oh >>> outpointHash)
                    &&& (drop . take . assert $ iden) >>> ctx8Add4)
                    &&& (drop . drop . assert $ iden) >>> annexHash >>> ctx8Finalize))

  , txHash = ((ctx8Init &&& (primitive Version &&& primitive LockTime) >>> ctx8Addn vector8)
         &&& (inputsHash &&& outputsHash) >>> ctx8Addn vector64)
         &&& inputUtxosHash >>> ctx8Addn vector32 >>> ctx8Finalize

  , tapleafHash = ((Sha256.ctx8InitTag "TapLeaf")
              &&& (primitive TapleafVersion &&& scribe (toWord8 32)) >>> ctx8Addn vector2)
              &&& (primitive ScriptCMR) >>> ctx8Addn vector32 >>> ctx8Finalize

  , tappathHash = hashWord256s8 (drop (primitive Tappath))

  , tapEnvHash = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)
             &&& (tappathHash &&& primitive InternalKey) >>> ctx8Addn vector64 >>> ctx8Finalize

  , sigAllHash = (ctx8Init &&& (txHash &&& tapEnvHash) >>> ctx8Addn vector64)
             &&& primitive CurrentIndex >>> ctx8Addn vector4 >>> ctx8Finalize
  }
  hashLoop256 :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term (c, Ctx8) Ctx8
  hashLoop256 = Sha256.hashLoop vector32
  hashWord256s :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term c Word256
  hashWord256s w array = iden &&& (unit >>> ctx8Init) >>> hashLoop256 w array >>> ctx8Finalize
  hashWord256s32 = hashWord256s word32
  hashWord256s8 = hashWord256s word8
  hashWord64s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector8 word32 array >>> ctx8Finalize
  hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize
  ctx8Add4 = ctx8Addn vector4
  ctx8Add8 = ctx8Addn vector8
  ctx8Add32 = ctx8Addn vector32
  ctx8Add64 = ctx8Addn vector64

-- | An instance of the SigHash 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: (Assert term, Primitive term) => Lib term
lib = mkLib Sha256.lib Sha256.libAssert Transaction.lib
