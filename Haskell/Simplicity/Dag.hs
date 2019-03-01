{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides the 'sortDag' function for converting a Simplicity expression into an topologically sorted, DAG representation.
module Simplicity.Dag
  ( Dag
  , sortDag
  -- * Type annoated, open recursive Simplicity terms.
  , TermF(..), SimplicityDag
  ) where

import Prelude hiding (fail, drop, take)

import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad.Trans.Writer (Writer, execWriter, tell)
import Data.Foldable (toList)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Lens.Family2.State (use)
import Lens.Family2.Stock (at)

import Simplicity.Digest
import Simplicity.Inference
import Simplicity.MerkleRoot
import Simplicity.Term

-- A monad used in the implementation of linearizeDag.
type LinearM a = StateT (Map.Map Hash256 Integer) (Writer (SimplicityDag [] ())) a

execLinearM :: LinearM a -> SimplicityDag [] ()
execLinearM m = execWriter (evalStateT m Map.empty)

-- Emit a new node and add insert it into the state's map.
tellNode :: Hash256 -> TermF () Integer -> LinearM Integer
tellNode h iterm = StateT go
 where
  go map = do
    tell $ [f <$> iterm]
    return (sz, Map.insert h sz map)
   where
    sz = toInteger (Map.size map)
    f i = sz - i -- transform indexes to offsets

-- | A 'Simplicity' instance used with 'sortDag'.
-- This instance merges identical typed Simplicity sub-expressions to create a DAG (directed acyclic graph) structure that represents the expression.
data Dag a b = Dag { dagRoot :: WitnessRoot a b
                   , dagMap :: Map.Map Hash256 (TermF () Hash256)
                   }

-- Topologically sort the 'Dag'.
-- The type annotations are also stripped in order to ensure the result isn't accidentally serialized before inference of principle type annotations.
-- All sharing of subexpressions remains monomorphic to ensure that types can be infered in (quasi-)linear time.
linearizeDag :: Dag a b -> SimplicityDag [] ()
linearizeDag dag = execLinearM . go . witnessRoot . dagRoot $ dag
 where
  dmap = dagMap dag
  go h = do
    mi <- use (at h)
    case mi of
     Just i -> return i
     Nothing -> traverse go uterm >>= tellNode h
   where
    uterm = dmap ! h

-- | Given a Simplicity expression, return a type annotated 'SimplicityDag', with shared subexpressions, that is suitable for serialization by 'Simplicity.Serialization.BitString.putDag'.
--
-- This function invokes type inference to ensure that the type annotations are principle types (with type variables instantiated at unit types).
-- Therefore the 'WitnessRoot' of the result may not match the 'WitnessRoot' of the input.
sortDag :: forall a b. (TyC a, TyC b) => Dag a b -> SimplicityDag [] Ty
sortDag t = toList pass2
 where
  pass1 :: Dag a b
  -- The patterns should never fail as we are running type inference on terms that are already known to be well typed.
  -- A failure of a pattern match here suggests there is an error in the type inference engine.
  pass1 = case typeCheck (linearizeDag t) of
            Right pass -> pass
            Left e -> error $ "sortDag.pass1: " ++ e
  pass2 = case typeInference (linearizeDag pass1) of
            Right pass -> pass
            Left e -> error $ "sortDag.pass2: " ++ e

mkLeaf comb uComb = Dag { dagRoot = root
                        , dagMap = Map.singleton (witnessRoot root) uComb
                        }
  where
   root = comb

mkUnary comb uComb t = Dag { dagRoot = root
                           , dagMap = Map.insert (witnessRoot root) (uComb (witnessRoot (dagRoot t))) (dagMap t)
                           }
  where
   root = comb (dagRoot t)

mkBinary comb uComb s t = Dag { dagRoot = root
                              , dagMap = Map.insert (witnessRoot root) (uComb (witnessRoot (dagRoot s)) (witnessRoot (dagRoot t))) union
                              }
  where
   root = comb (dagRoot s) (dagRoot t)
   union = Map.union (dagMap s) (dagMap t)

instance Core Dag where
  iden = mkLeaf iden uIden
  comp = mkBinary comp uComp
  unit = mkLeaf unit uUnit
  injl = mkUnary injl uInjl
  injr = mkUnary injr uInjr
  match = mkBinary match uCase
  pair = mkBinary pair uPair
  take = mkUnary take uTake
  drop = mkUnary drop uDrop

instance Assert Dag where
  assertl s h = Dag { dagRoot = root
                    , dagMap = Map.insert (witnessRoot root) (uCase (witnessRoot (dagRoot s)) hRoot)
                             . Map.insert hRoot (uHidden h)
                             $ dagMap s
                    }
   where
    hRoot = hiddenRoot h
    root = assertl (dagRoot s) h
  assertr h t = Dag { dagRoot = root
                    , dagMap = Map.insert (witnessRoot root) (uCase hRoot (witnessRoot (dagRoot t)))
                             . Map.insert hRoot (uHidden h)
                             $ dagMap t
                    }
   where
    hRoot = hiddenRoot h
    root = assertr h (dagRoot t)
  fail b = mkLeaf (fail b) (uFail b)

instance Witness Dag where
  witness v = mkLeaf (witness v) (uWitness (WitnessValue (untypedValue v)))

instance Delegate Dag where
  disconnect = mkBinary disconnect uDisconnect

instance Primitive Dag where
  primitive p = mkLeaf (primitive p) (Prim (SomeArrow p))

instance Jet Dag where
  jet t = error ":TODO: serialization of jet nodes not yet implemented"

instance Simplicity Dag where
