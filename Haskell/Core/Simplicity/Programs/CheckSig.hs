{-# LANGUAGE RecordWildCards #-}
-- | The module builds a Simplicity expression that mimics the behavour of a @CHECKSIG@ operation for Bitcoin but with universal signature hash modes.
-- This uses Schnorr signature verification specified in "Simplicity.Programs.LibSecp256k1".
module Simplicity.Programs.CheckSig
  ( sigHash'
  , checkSigVerify, checkSigVerify'
  -- * Types
  , Hash
  ) where

import Prelude hiding (drop, take)

import Simplicity.Digest
import Simplicity.Functor
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.MerkleRoot hiding (sigHash)
import Simplicity.Programs.Generic
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.LibSecp256k1 hiding (Lib(Lib), lib, mkLib)
import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1
import Simplicity.Term.Core
import Simplicity.Ty
import Simplicity.Ty.Word

-- | A Simplicity expression that computes a "standard" Simplicity tagged signature hash from the CMR of a sighash algorithm, and the output of that sighash.
--
-- This expression should not be used directly.  Instead use 'sigHash'' to ensure that inputs are properly constructed.
sigHash :: (Core term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                       -> term (Word256, Word256) Hash
sigHash Sha256.Lib{..} = (scribe iv &&& iden >>> hb)
  &&& scribe (toWord512 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400)
  >>> hb
 where
  iv = toWord256 . integerHash256 . ivHash $ signatureTag
  hb = hashBlock

-- | Constructs a Simplicity expression for a "standard" Simplicity tagged signature hash using a given signature hash mode.
--
-- The sighash mode is `disconnected` and thus doesn't affect this expression's CMR.
sigHash' :: (Core term, Delegate term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                       -> term () Hash -- ^ signature hash mode
                                       -> term () Hash
sigHash' sha256 hashMode = disconnect iden hashMode >>> sigHash sha256


-- | A Simplicity expression that checks a "standard" Simplicity tagged signature hash given
--
-- * A pubkey
-- * A message that is intended to be the CMR of a sighash algorithm, and the output of that sighash.
-- * A signature
--
-- This expression should not be used directly.  Instead use 'checkSigVerify'' to ensure that inputs are properly constructed.
checkSigVerify :: (Assert term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> LibSecp256k1.Lib term -- ^ "Simplicity.Programs.LibSecp256k1"
                                -> term ((Word256, (Word256, Word256)), Word512) () -- ^ signature hash mode
checkSigVerify sha256 libsecp256k1 =
      take (oh &&& drop (sigHash sha256)) &&& ih >>> bip_0340_verify libsecp256k1

-- | Constructs a Simplicity program that validates a signature on a "standard" Simplicity tagged signature hash using
--
-- * a given signature hash mode
-- * a given public key
-- * a given signature
--
-- The sighash mode is `disconnected` and the signature is embedded inside a witness node.
-- Thus these two inputs do not affect this expression's CMR.
checkSigVerify' :: (Assert term, Delegate term, Witness term) => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                                              -> LibSecp256k1.Lib term -- ^ "Simplicity.Programs.LibSecp256k1"
                                                              -> term () Hash -- ^ signature hash mode
                                                              -> Schnorr.PubKey -> Schnorr.Sig -> term () ()
checkSigVerify' sha256 libsecp256k1 hashMode (Schnorr.PubKey x) ~(Schnorr.Sig r s) =
      (scribe (toWord256 . toInteger $ x) &&& disconnect iden hashMode)
  &&& (witness (toWord256 . toInteger $ r, toWord256 . toInteger $ s))
  >>> checkSigVerify sha256 libsecp256k1
