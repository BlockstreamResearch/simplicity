-- | This modules provides a bit-stream serialization and deserialization functions for 'UntypedSimplicityDag's.
module Simplicity.Serialization.BitString
  ( getDag, putDag
  ) where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.Elaboration
import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Ty

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
getDag abort next = V.toList <$> V.unfoldrM (\_ -> fmap noState <$> getNode abort next) ()
 where
  noState x = (x, ())

putNode :: UntypedTermF Integer -> DList Bool
putNode node | Just (x,y) <- isUComp node             = ([o,o,o,o,o]++) . putPositive x . putPositive y
             | Just (x,y) <- isUCase node             = ([o,o,o,o,i]++) . putPositive x . putPositive y
             | Just (x,y) <- isUPair node             = ([o,o,o,i,o]++) . putPositive x . putPositive y
             | Just (x,y) <- isUDisconnect node       = ([o,o,o,i,i]++) . putPositive x . putPositive y
             | Just x <- isUInjl node                 = ([o,o,i,o,o]++) . putPositive x
             | Just x <- isUInjr node                 = ([o,o,i,o,i]++) . putPositive x
             | Just x <- isUTake node                 = ([o,o,i,i,o]++) . putPositive x
             | Just x <- isUDrop node                 = ([o,o,i,i,i]++) . putPositive x
             | Just _ <- isUIden node                 = ([o,i,o,o,o]++)
             | Just _ <- isUUnit node                 = ([o,i,o,o,i]++)
             | Just h <- isUHidden node               = ([o,i,i,o]++) . put256Bits h
             | Just w <- isUWitness node              = ([o,i,i,i]++) . putBitString (UV.toList w)
             | Just (SomeArrow p _ _) <- isUPrim node = ([i,o]++) . putPrimBit p
 where
  (o,i) = (False,True)

-- | Encodes an 'UntypedSimplicityDag' as a self-delimiting bit-stream encoding.
--
-- @
--    evalStreamWithError getDag . putDag = Right
-- @
putDag :: UntypedSimplicityDag -> [Bool]
putDag v = foldr putNode [o,i,o,i,i] v
 where
  (o,i) = (False,True)
