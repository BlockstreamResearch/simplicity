module Simplicity.Programs.CheckSigHashAll where

import qualified Data.ByteString.Char8 as BSC

import Simplicity.Digest
import Simplicity.MerkleRoot
import qualified Simplicity.LibSecp256k1.Types as LibSecp
import Simplicity.Primitive.Bitcoin
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Sha256
import Simplicity.Programs.LibSecp256k1
import Simplicity.Programs.Word
import Simplicity.Term
import Simplicity.Ty

sigAll :: (Core term, Primitive term) => term () (Block, Block)
sigAll = blk1 &&& blk2
 where
  blk1 = primitive InputsHash &&& primitive OutputsHash
  blk2 = (((primitive LockTime &&& primitive Version) &&& scribe (toWord64 0x8000000000000000)) &&& zero word128) &&& scribe (toWord256 (512+2*256+2*32))

sigHashAll :: (Core term, Primitive term) => term () Hash
sigHashAll = sigAll >>> (scribe iv &&& oh >>> hashBlock) &&& ih >>> hashBlock
 where
  iv = toWord256 . integerHash256 . ivHash $ signatureIv (witnessRoot sigAll)

checkSigHashAll :: (Assert term, Primitive term) => term (PubKey, Sig) ()
checkSigHashAll = (oh &&& (unit >>> sigHashAll)) &&& ih
              >>> schnorrAssert

wCheckSigHashAll :: (Assert term, Primitive term, Witness term) => LibSecp.Sig -> term PubKey ()
wCheckSigHashAll (LibSecp.Sig r s) = iden &&& (witness (toWord256 . toInteger $ r, toWord256 . toInteger $ s))
                                 >>> checkSigHashAll

pkwCheckSigHashAll :: (Assert term, Primitive term, Witness term, TyC a) => LibSecp.PubKey -> LibSecp.Sig -> term a ()
pkwCheckSigHashAll (LibSecp.PubKey y x) (LibSecp.Sig r s) =
   scribe (toBit y, toWord256 . toInteger $ x) &&& (witness (toWord256 . toInteger $ r, toWord256 . toInteger $ s))
   >>> checkSigHashAll
