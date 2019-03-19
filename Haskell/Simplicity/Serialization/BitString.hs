{-# LANGUAGE ScopedTypeVariables #-}
-- | This modules provides a bit-stream serialization and deserialization functions for 'SimplicityDag's and Simplicity expressions.
module Simplicity.Serialization.BitString
  ( getDagNoWitness, getWitnessData, getTerm
  , putDag, putTerm
  ) where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Void (Void, vacuous)

import Simplicity.Dag
import Simplicity.Digest
import Simplicity.Inference
import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Term
import Simplicity.Ty

{- Consider replacing @UV.Vector Bool@ with @Vector Bit@ from https://github.com/mokus0/bitvec when issues are resolved.
   see https://github.com/mokus0/bitvec/issues/3 & https://github.com/mokus0/bitvec/issues/4. -}
-- Decodes a single node and references for a 'UntypedSimplicityDag'.
-- 'Nothing' is returned when then end-of-stream code is encountered.
-- @abort@ is invoked if an invalid code is encountered.
getNode :: Monad m => m Void -> m Bool -> m (Maybe (TermF () () Integer))
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
    ((Just . uHidden <$> get256Bits next) & (node (uWitness ()))))

-- | Decodes a self-delimiting bit-stream encoding of 'SimplicityDag' without witness data.
--
-- In this encoding, not every bit-stream prefix is valid encoding of a 'SimplicityDag'.
-- Given parameters @'getDagNoWitness' abort next@, @abort@ is invoked at the point an invalid prefix is encounted, meaning that the stream is not a valid code for a 'SimplicityDag'.
--
-- Type annotations are not part of the encoding.  After deserialization you will want to run type inference from "Simplicity.Inference".
-- Type Inference needs to be completed before the witness data, which appears after the 'SimplicityDag' in the bit-stream, can be added to the DAG.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getDagNoWitness' has the type of a binary branching tree with leaves either containing 'SimplicityDag' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getDagNoWitness :: Monad m => m Void -> m Bool -> m (SimplicityDag V.Vector () ())
getDagNoWitness abort next = V.unfoldrM (\_ -> fmap noState <$> getNode abort next) ()
 where
  noState x = (x, ())

-- | Given a type-annotated 'SimplicityDag', decode a bit-stream encoding of the DAG's witness data as 'UntypedValue's.
--
-- In this encoding, not every bit-stream prefix is valid encoding of the witness data.
-- Given parameters @'getWintessData' abort next@, @abort@ is invoked if the encoded value of the witness length does not match the actual length of the witness data consumed by the DAG.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getWitnessData' returns the type of a binary branching tree with leaves either containing 'SimplicityDag' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getWitnessData :: (Traversable f, Monad m) => SimplicityDag f Ty w -> m Void -> m Bool -> m (SimplicityDag f Ty UntypedValue)
getWitnessData dag abort next = do
  witnessBlob <- UV.fromList <$> getBitString next
  maybe (vacuous abort) return $ evalExactVector (\next -> traverse (witnessData (witnessDecoder next)) dag) witnessBlob
 where
  witnessDecoder next ty _ = case reflect ty of
                              (SomeTy b) -> untypedValue <$> getValueR b next

-- | Decodes a self-delimiting bit-stream encoding of a Simplicity Expression.
--
-- This function combines, 'getDagNoWitness', 'typeInference', 'getWitnessData', and 'typeCheck' to decode a Simplicity DAG and witness data and runs type Inference.
--
-- Given parameters @'getTerm' abort next@, @abort@ is invoked if any decoding or type checking error occurs.
--
-- Note: The one calling 'getTerm' determines the input and output Simplicity types of the resulting Simplicity expression.
-- They are __not__ inferered from the DAG input.
-- Instead the types @a@ and @b@ are used as constraints during type inference.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getTerm' returns the type of a binary branching tree with leaves either containing 'term a b' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getTerm :: forall m term a b. (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTerm abort next = do
  dag <- getDagNoWitness abort next
  tyDag <- either (\err -> vacuous abort) return $ typeInference proxy dag
  wTyDag <- getWitnessData tyDag abort next
  either (\err -> vacuous abort) return $ typeCheck wTyDag
 where
  proxy :: term a b
  proxy = undefined

-- Encodes a single node from as a self-delimiting bit-stream encoding as a difference list.
-- Witness data is not encoded.
putNode :: TermF Ty w Integer -> DList Bool
putNode = go
 where
  go (Comp _ _ _ x y)         = ([o,o,o,o,o]++) . putPositive x . putPositive y
  go (Case _ _ _ _ x y)       = ([o,o,o,o,i]++) . putPositive x . putPositive y
  go (Pair _ _ _ x y)         = ([o,o,o,i,o]++) . putPositive x . putPositive y
  go (Disconnect _ _ _ _ x y) = ([o,o,o,i,i]++) . putPositive x . putPositive y
  go (Injl _ _ _ x)           = ([o,o,i,o,o]++) . putPositive x
  go (Injr _ _ _ x)           = ([o,o,i,o,i]++) . putPositive x
  go (Take _ _ _ x)           = ([o,o,i,i,o]++) . putPositive x
  go (Drop _ _ _ x)           = ([o,o,i,i,i]++) . putPositive x
  go (Iden _)                 = ([o,i,o,o,o]++)
  go (Unit _)                 = ([o,i,o,o,i]++)
  go (Hidden h)               = ([o,i,i,o]++) . put256Bits h
  go (Witness _ _ _)          = ([o,i,i,i]++)
  go (Prim (SomeArrow p))     = ([i,o]++) . putPrimBit p
  (o,i) = (False,True)

-- Caution: Maybe [Bool] is a type that might cause space leaks.  Investiagte alternatives.
-- | Encodes an 'SimplicityDag' as a self-delimiting bit-stream encoding, including witness data.
--
-- Encoding of witness data require that its type annotation be the value's principle type.
-- This function may return 'Nothing' if witness data cannot be encoded using the witnesses' type annoation.
putDag :: Foldable f => SimplicityDag f Ty UntypedValue -> Maybe [Bool]
putDag v = do
  wd <- foldr (\x y -> encodeWitnessDatum x <*> y) (Just []) v
  return $ foldr putNode ([o,i,o,i,i] ++ putBitString wd []) v
 where
  encodeWitnessDatum (Witness _ b w) = case reflect b of
                                         SomeTy rb -> ((++) . putValueR rb) <$> castUntypedValue w
  encodeWitnessDatum _ = Just id
  (o,i) = (False,True)

-- | Encodes a Simplicity expression as a self-delimiting bit-stream encoding.
putTerm :: (TyC a, TyC b) => Dag a b -> [Bool]
putTerm dag = result
 where
  {- sortDag ought not to ever produce a value where putDag fails. -}
  Just result = putDag (sortDag dag)
