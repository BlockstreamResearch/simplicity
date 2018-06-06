-- | This modules provides a bit-stream serialization and deserialization functions for 'UntypedSimplicityDag's.
module Simplicity.Serialization.BitString
  ( getDag
  ) where

import Data.Vector (unfoldrM)
import qualified Data.Vector.Unboxed as UV
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.Elaboration
import Simplicity.Primitive
import Simplicity.Serialization

-- Decodes a single node and references for a 'UntypedSimplicityDag'.
-- 'Nothing' is returned when then end-of-stream code is encountered.
-- @abort@ is called if an invalid code is encountered.
getNode :: Monad m => m Void -> m Bool -> m (Maybe (UntypedTermF Integer))
getNode abort next = (getBody >>= traverse (traverse (\_ -> getPositive next)))
                   & ((Just . uPrim <$> getPrimBit next) & error "Simplicity.Serialization.BitString.getNode: TODO uJet.")
 where
  l & r = next >>= \b -> if b then r else l
  node = return . Just
  endOfStream = return Nothing
  getBody =
   (((node (uComp () ()) & node (uCase () ())) & (node (uPair () ()) & node (uDisconnect () ()))) &
    ((node (uInjl ()) & node (uInjr ())) & (node (uTake ()) & node (uDrop ())))) &
   (((node uIden & node uUnit) & (vacuous abort & endOfStream)) &
    ((Just . uHidden <$> get256Bits next) & (Just . uWitness . UV.fromList <$> getBitString next)))

-- | Decodes a self-delimiting bit-stream encoding of 'UntypedSimplicityDag'.
--
-- In this code, not every bit-stream prefix is valid encoding of a 'UntypedSimplicityDag'.
-- Given @'getDag' abort next@, @abort@ is called at the point an invalid prefix is encounted, meaning that the stream is not a valid code for an 'UntypedSimplicityDag'.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getDag' has the type of a binary branching tree with leaves either containing 'UntypedSimplicityDag' values or no value.
getDag :: Monad m => m Void -> m Bool -> m UntypedSimplicityDag
getDag abort next = unfoldrM (\_ -> fmap noState <$> getNode abort next) ()
 where
  noState x = (x, ())
