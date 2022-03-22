-- | This module defines utilities used in the processing of Bitcoin-like transaction data.
module Simplicity.Bitcoin
  ( parseLock, parseSequence
  ) where

import Data.Bits (testBit)
import Data.Word (Word32, Word16)

-- | Decodes a transaction's lock value into either @'Left' height@ or @'Right' time@.
-- Note that an "unlocked" value is decoded as a height of @0@, which is semantically equivalent to being unlocked.
parseLock :: Word32 -> Either Word32 Word32
parseLock v | v < 500000000 = Left v
            | otherwise = Right v

-- | Decodes a transaction's input's sequence number into optionally either @'Just' ('Left' distance)@ or @'Just' ('Right' duration)@.
-- If the sequence number's relative lock is disabled, 'Nothing' is returned
-- Bits without relative lock time semantics are ignored.
parseSequence :: Word32 -> Maybe (Either Word16 Word16)
parseSequence v | testBit v 31 = Nothing
                | testBit v 22 = Just (Right (fromIntegral v))
                | otherwise    = Just (Left (fromIntegral v))
