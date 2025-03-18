-- | This modules provides some functions for mashalling data to and from Simplicity types that are used for some SHA-256 operations.
module Simplicity.Ty.Sha256
 ( fromHash
 , fromCtx8, toCtx8
 , Ctx, Ctx8
 ) where

import qualified Data.ByteString as BS
import Lens.Family2 ((^..), over, review)

import Simplicity.Digest
import Simplicity.Programs.Sha256
import Simplicity.Ty.Word

fromHash :: Hash -> Hash256
fromHash = review (over be256) . fromIntegral . fromWord256

fromCtx8 :: Ctx8 -> Maybe Ctx
fromCtx8 (buffer, (count, midstate)) = ctxBuild (fromInteger . fromWord8 <$> buffer^..buffer_ buffer63)
                                               (fromWord64 count)
                                               (fromHash midstate)
toCtx8 :: Ctx -> Ctx8
toCtx8 ctx = (buffer, (count, midstate))
 where
  buffer = fst $ bufferFill buffer63 (toWord8 . fromIntegral <$> BS.unpack (ctxBuffer ctx))
  count = toWord64 . fromIntegral $ ctxCounter ctx
  midstate = toWord256 . integerHash256 . ivHash $ ctxIV ctx
