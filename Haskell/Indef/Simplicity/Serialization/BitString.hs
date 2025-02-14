{-# LANGUAGE ScopedTypeVariables #-}
-- | This modules provides a bit-stream serialization and deserialization functions for 'SimplicityDag's and Simplicity expressions for both stop-code and length-code based formats.
module Simplicity.Serialization.BitString
  ( getDagNoWitnessLengthCode
  , getWitnessData
  , getTermLengthCode
  , putDagNoWitnessLengthCode
  , putWitnessData
  , putTermLengthCode
  ) where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Void (Void, vacuous)
import Lens.Family2 ((&), (%~))

import Simplicity.Dag
import Simplicity.Digest
import Simplicity.Inference
import Simplicity.JetType
import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Term
import Simplicity.Ty

-- Decodes a single node and references for a 'UntypedSimplicityDag'.
-- @abort@ is invoked if an invalid code is encountered.
getNode :: (Monad m, JetType jt) => m Void -> m Bool -> m (TermF () (SomeArrow jt) () Integer)
getNode abort next = (getBody >>= traverse (\_ -> getPositive next))
                   & (Jet <$> getJetBit abort next)
 where
  l & r = next >>= \b -> if b then r else l
  node = return
  getBody =
   (((node (uComp () ()) & node (uCase () ())) & (node (uPair () ()) & node (uDisconnect () ()))) &
    ((node (uInjl ()) & node (uInjr ())) & (node (uTake ()) & node (uDrop ())))) &
   (((node uIden & node uUnit) & vacuous abort) &
    ((uHidden <$> get256Bits next) & (node (uWitness ()))))

-- | Decodes a length-code based self-delimiting bit-stream encoding of 'SimplicityDag' without witness data.
--
-- @abort@ is invoked at the point an invalid prefix is encountered, meaning that the stream is not a valid code for a 'SimplicityDag'.
--
-- Type annotations are not part of the encoding.  After deserialization you will want to run type inference from "Simplicity.Inference".
-- Type Inference needs to be completed before the witness data, which appears after the 'SimplicityDag' in the bit-stream, can be added to the DAG.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getDagNoWitnessLengthCode' has the type of a binary branching tree with leaves either containing 'SimplicityDag' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getDagNoWitnessLengthCode :: (Monad m, JetType jt)
                          => m Void -- ^ @abort@
                          -> m Bool -- ^ @next@
                          -> m (SimplicityDag V.Vector () (SomeArrow jt) ())
getDagNoWitnessLengthCode abort next = do
  len <- getPositive next
  V.replicateM (fromInteger len) $ do
    getNode abort next

-- | Given a type-annotated 'SimplicityDag', decode a bit-stream encoding of the DAG's witness data as 'UntypedValue's.
--
-- @abort@ is invoked if the encoded value of the witness length does not match the actual length of the witness data consumed by the DAG.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, @'getWitnessData' dag@ has the type of a binary branching tree with leaves either containing 'SimplicityDag' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getWitnessData :: (Traversable f, Monad m) => SimplicityDag f Ty jt w
               -> m Bool -- ^ @next@
               -> m (SimplicityDag f Ty jt UntypedValue)
getWitnessData dag next = do
  traverse (witnessData (witnessDecoder next)) dag
 where
  witnessDecoder next ty _ = case reflect ty of
                              (SomeTy b) -> untypedValue <$> getValueR b next

-- | Decodes a length-code based self-delimiting bit-stream encoding of a Simplicity expression.
--
-- This function combines, 'getDagNoWitnessLengthCode', 'typeInference', 'getWitnessData', and 'typeCheck' to decode a Simplicity DAG and witness data and runs type inference.
--
-- @abort@ is invoked if any decoding or type checking error occurs.
--
-- The @proxy ('SomeArrow' jt)@ argument is used to specify the 'JetType' used for decoding known jets.
--
-- Note: The one calling 'getTermLengthCode' determines the input and output Simplicity types of the resulting Simplicity expression.
-- They are __not__ inferered from the DAG input.
-- Instead the types @a@ and @b@ are used as constraints during type inference.
--
-- Note that the type @forall m. Monad m => m Void -> m Bool -> m a@ is isomorphic to the free monad over the @X² + 1@ functor at @a@.
-- In other words, 'getTermLengthCode' has the type of a binary branching tree with leaves either containing 'term a b' values or no value.
-- See "Simplicity.Serialization" for functions to execute this free monad.
getTermLengthCode :: forall proxy jt m term a b. (JetType jt, Monad m, Simplicity term, TyC a, TyC b)
                  => proxy (SomeArrow jt)
                  -> m Void -- ^ @abort@
                  -> m Bool -- ^ @next@
                  -> m (term a b)
getTermLengthCode _ abort next = do
  dag <- getDagNoWitnessLengthCode abort next :: m (SimplicityDag V.Vector () (SomeArrow jt) ())
  tyDag <- either (\err -> vacuous abort) return $ typeInference proxy dag
  wTyDag <- getWitnessData tyDag next
  either (\err -> vacuous abort) return $ typeCheck wTyDag
 where
  proxy :: term a b
  proxy = undefined

-- Encodes a single node from as a self-delimiting bit-stream encoding as a difference list.
-- Witness data is not encoded.
putNode :: JetType jt => TermF Ty (SomeArrow jt) w Integer -> DList Bool
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
  go (Jet (SomeArrow j))      = ([i]++) . putJetBit j
  (o,i) = (False,True)

-- Caution: Maybe [Bool] is a type that might cause space leaks.  Investiagte alternatives.
-- | Encodes an 'SimplicityDag' as a self-delimiting, length-code based bit-stream encoding, including witness data.
--
-- Encoding of witness data requires that its type annotation be the value's principle type.
-- This function may return 'Nothing' if witness data cannot be encoded using the witnesses' type annotation.
putDagNoWitnessLengthCode :: (Foldable f, JetType jt) => SimplicityDag f Ty (SomeArrow jt) UntypedValue -> [Bool]
putDagNoWitnessLengthCode v = putPositive len $ foldr putNode [] v
 where
  len = toInteger $ length v

putWitnessData :: (Foldable f, JetType jt) => SimplicityDag f Ty (SomeArrow jt) UntypedValue -> Maybe [Bool]
putWitnessData v = foldr (\x y -> encodeWitnessDatum x <*> y) (Just []) v
 where
  encodeWitnessDatum (Witness _ b w) = case reflect b of
                                         SomeTy rb -> ((++) . putValueR rb) <$> castUntypedValue w
  encodeWitnessDatum _ = Just id

-- | Encodes a Simplicity expression as a self-delimiting, length-code based, bit-stream encoding.
--
-- Subexpressions matching @'JetType' jt@ are replaced and encoded as jets.
putTermLengthCode :: (JetType jt, TyC a, TyC b) => JetDag jt a b -> ([Bool],[Bool])
putTermLengthCode dag = (prog, witness)
 where
  jd = jetDag dag
  prog = putDagNoWitnessLengthCode jd
  {- jetDag ought not to ever produce a value where putDag fails. -}
  Just witness = putWitnessData jd
