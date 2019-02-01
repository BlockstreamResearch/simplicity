-- | This modules provides a bit-stream serialization and deserialization functions for 'SimplicityDag's.
module Simplicity.Serialization.BitString
  ( getDag, putDag
  ) where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.Inference
import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Ty

-- Decodes a single node and references for a 'UntypedSimplicityDag'.
-- 'Nothing' is returned when then end-of-stream code is encountered.
-- @abort@ is invoked if an invalid code is encountered.
getNode :: Monad m => m Void -> m Bool -> m (Maybe (TermF () Integer))
getNode abort next = (getBody >>= traverse (traverse (\_ -> getPositive next)))
                   & ((Just . Prim <$> getPrimBit next) & error "Simplicity.Serialization.BitString.getNode: TODO uJet.")
 where
  l & r = next >>= \b -> if b then r else l
  node = return . Just
  endOfStream = return Nothing
  getBody =
   (((node (uComp () ()) & node (uCase () ())) & (node (uPair () ()) & node (uDisconnect () ()))) &
    ((node (uInjl ()) & node (uInjr ())) & (node (uTake ()) & node (uDrop ())))) &
   (((node uIden & node uUnit) & (vacuous abort & endOfStream)) &
    ((Just . uHidden <$> get256Bits next) & (Just . uWitness . WitnessData . UV.fromList <$> getBitString next)))

-- | Decodes a self-delimiting bit-stream encoding of 'SimplicityDag'.
--
-- In this encoding, not every bit-stream prefix is valid encoding of a 'SimplicityDag'.
-- Given parameters @'getDag' abort next@, @abort@ is invoked at the point an invalid prefix is encounted, meaning that the stream is not a valid code for a 'SimplicityDag'.
--
-- Type annotations are not part of the encoding.  After deserialization you will want to run type inference from "Simplicity.Inference".
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getDag' has the type of a binary branching tree with leaves either containing 'SimplicityDag' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getDag :: Monad m => m Void -> m Bool -> m (SimplicityDag V.Vector ())
getDag abort next = V.unfoldrM (\_ -> fmap noState <$> getNode abort next) ()
 where
  noState x = (x, ())

putNode :: TermF Ty Integer -> Maybe (DList Bool)
putNode = go
 where
  go (Comp _ _ _ x y)         = Just $ ([o,o,o,o,o]++) . putPositive x . putPositive y
  go (Case _ _ _ _ x y)       = Just $ ([o,o,o,o,i]++) . putPositive x . putPositive y
  go (Pair _ _ _ x y)         = Just $ ([o,o,o,i,o]++) . putPositive x . putPositive y
  go (Disconnect _ _ _ _ x y) = Just $ ([o,o,o,i,i]++) . putPositive x . putPositive y
  go (Injl _ _ _ x)           = Just $ ([o,o,i,o,o]++) . putPositive x
  go (Injr _ _ _ x)           = Just $ ([o,o,i,o,i]++) . putPositive x
  go (Take _ _ _ x)           = Just $ ([o,o,i,i,o]++) . putPositive x
  go (Drop _ _ _ x)           = Just $ ([o,o,i,i,i]++) . putPositive x
  go (Iden _)                 = Just $ ([o,i,o,o,o]++)
  go (Unit _)                 = Just $ ([o,i,o,o,i]++)
  go (Hidden h)               = Just $ ([o,i,i,o]++) . put256Bits h
  go (Witness _ b w)          = case reflect b of
                                 SomeTy rb -> (([o,i,i,i]++) .) . putBitString . putValueR rb <$> getWitnessData w
  go (Prim (SomeArrow p)) = Just $ ([i,o]++) . putPrimBit p
  (o,i) = (False,True)

-- Caution: Maybe [Bool] is a type that might cause space leaks.  Investiagte alternatives.
-- | Encodes an 'SimplicityDag' as a self-delimiting bit-stream encoding.
--
-- Encoding of witness values require that its type annotation be the value's principle type.
-- 'putDag' requires a type annotated 'SimplicityDag' in order to pursuade the user to run 'typeInference' first.
-- This function may return 'Nothing' if witness values cannot be encoded using the witnesses' type annoation.
putDag :: Foldable f => SimplicityDag f Ty -> Maybe [Bool]
putDag v = foldr (\x y -> putNode x <*> y) (Just [o,i,o,i,i]) v
 where
  (o,i) = (False,True)
