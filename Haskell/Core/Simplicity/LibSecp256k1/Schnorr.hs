-- | This module specifices the types to be used to interface with bindings to a real Schnorr signature module for Secp256k1.
-- It largely acts as a placeholder at this point in time.
module Simplicity.LibSecp256k1.Schnorr
 ( PubKey(..), Sig(..)
 ) where

import Data.Serialize (Serialize, get, put)
import Data.Serialize.Get (getWord8)
import Data.Serialize.Put (putWord8)

import Simplicity.Word

-- | A public key format to be used for Schnorr signatures.
data PubKey = PubKey Bool Word256

instance Serialize PubKey where
  get = PubKey <$> (getWord8 >>= compressedY) <*> get
   where
    compressedY 2 = return False
    compressedY 3 = return True
    compressedY _ = fail "Serialize.get{Simplicity.LibSecp256k1.Types.PubKey}: bad compressed y-coordinate."
  put (PubKey y x) = putY y >> put x
   where
    putY False = putWord8 2
    putY True = putWord8 3

-- | A Schnorr signature format.
data Sig = Sig Word256 Word256

instance Serialize Sig where
  get = Sig <$> get <*> get
  put (Sig r s) = put r >> put s
