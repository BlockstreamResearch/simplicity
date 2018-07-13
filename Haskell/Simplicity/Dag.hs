-- | This module provides the 'linearizeDag' function for converting a Simplicity expression into an untyped, topologically sorted, DAG representation.
module Simplicity.Dag
  ( Dag
  , linearizeDag
  -- * Untyped Simplicity
  , UntypedSimplicityDag, UntypedTermF
  -- ** Match expressions for untyped Simplicity
  , isUIden, isUUnit, isUInjl, isUInjr
  , isUTake, isUDrop, isUComp, isUCase, isUPair, isUDisconnect
  , isUHidden, isUWitness, isUPrim
  ) where

import Prelude hiding (fail, drop, take)

import Control.Monad.Trans.State (StateT(..), evalStateT, get)
import Control.Monad.Trans.Writer (Writer, execWriter, tell)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map

import Simplicity.Digest
import Simplicity.Elaboration
import Simplicity.MerkleRoot
import Simplicity.Term

-- A monad used in the implementation of linearizeDag.
type LinearM a = StateT (Map.Map Hash256 Integer) (Writer UntypedSimplicityDag) a

execLinearM :: LinearM a -> UntypedSimplicityDag
execLinearM m = execWriter (evalStateT m Map.empty)

lookupHash :: Hash256 -> LinearM (Maybe Integer)
lookupHash h = Map.lookup h <$> get

-- Emit a new node and add insert it into the state's map.
tellNode :: Hash256 -> UntypedTermF Integer -> LinearM Integer
tellNode h iterm = StateT go
 where
  go map = do
    tell $ [f <$> iterm]
    return (sz, Map.insert h sz map)
   where
    sz = toInteger (Map.size map)
    f i = sz - i -- transform indexes to offsets

-- | A 'Simplicity' instance used for 'linearizeDag'.
-- This instance merges identical typed Simplicity sub-expressions to create a DAG (directed acyclic graph) structure that represents the expression.
data Dag a b = Dag { dagRoot :: WitnessRoot a b
                   , dagMap :: Map.Map Hash256 (UntypedTermF Hash256)
                   }

-- | Given a 'Dag' for a Simplicity expression, run a topological sort to create a list representation of the DAG where nodes only refer back to nodes earlier in the list.
--
-- The type annotations are stripped.
-- However, all sharing of subexpressions remains monomorphic to ensure that types can be infered in (quasi-)linear time.
--
-- The result is suitable for serializatoin by 'Simplicity.Serialization.BitString.putDag' or for type inference by 'Simplicity.Elaboration.typeCheckDag'.
linearizeDag :: Dag a b -> UntypedSimplicityDag
linearizeDag dag = execLinearM . go . witnessRoot . dagRoot $ dag
 where
  dmap = dagMap dag
  go h = do
    mi <- lookupHash h
    case mi of
     Just i -> return i
     Nothing -> traverse go uterm >>= tellNode h
   where
    uterm = dmap ! h

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
  witness v = mkLeaf (witness v) (uWitness (witnessData v))

instance Delegate Dag where
  disconnect = mkBinary disconnect uDisconnect

instance Primitive Dag where
  primitive p = mkLeaf (primitive p) (uPrim (someArrow p))

instance Jet Dag where
  jet t = error ":TODO: serialization of jet nodes not yet implemented"

instance Simplicity Dag where
