{-# LANGUAGE ConstraintKinds, GADTs, RankNTypes, ScopedTypeVariables #-}
-- | This module provides the 'sortDag' function for converting a Simplicity expression into an topologically sorted, DAG representation.
module Simplicity.Dag
  ( jetDag, jetSubst
  , JetDag, NoJetDag
  , pruneSubst
  -- * Type annoated, open recursive Simplicity terms
  , TermF(..), SimplicityDag
  -- * Wrapped Simplicity
  , WrappedSimplicity, unwrap
  ) where

import Prelude hiding (fail, drop, take)

import Control.Arrow ((+++))
import Control.Applicative (empty)
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad.Trans.Writer (Writer, execWriter, tell)
import Data.Either (isLeft)
import Data.Foldable (toList)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Sequence (Seq)
import Lens.Family2 ((&), (%~), (.~))
import Lens.Family2.State (use)
import Lens.Family2.Stock (at, some_)

import Simplicity.Digest
import Simplicity.Delegator
import Simplicity.Inference
import Simplicity.JetType
import Simplicity.MerkleRoot
import Simplicity.Semantics
import Simplicity.Tensor
import Simplicity.Term

-- A monad used in the implementation of linearizeDag.
type LinearM j w a = StateT (Map.Map Hash256 Integer) (Writer (SimplicityDag [] () j w)) a

execLinearM :: LinearM j w a -> SimplicityDag [] () j w
execLinearM m = execWriter (evalStateT m Map.empty)

-- Emit a new node and add insert it into the state's map.
tellNode :: Hash256 -> TermF () j w Integer -> LinearM j w Integer
tellNode h iterm = StateT go
 where
  go map = do
    tell $ [f <$> iterm]
    return (sz, Map.insert h sz map)
   where
    sz = toInteger (Map.size map)
    f i = sz - i -- transform indexes to offsets

-- MapSet is a commutative, idempotent monoid.
newtype MapSet a b = MapSet { getMapSet :: Map.Map a (Set.Set b) }

singleton :: a -> b -> MapSet a b
singleton a b = MapSet $ Map.singleton a (Set.singleton b)

instance (Ord a, Ord b) => Semigroup (MapSet a b) where
  (MapSet ms1) <> (MapSet ms2) = MapSet $ Map.unionWith Set.union ms1 ms2

instance (Ord a, Ord b) => Monoid (MapSet a b) where
  mempty = MapSet Map.empty

-- | A 'Simplicity' instance used with 'jetDag'.
-- This instance merges identical typed Simplicity sub-expressions to create a DAG (directed acyclic graph) structure that represents the expression.
--
-- A log of branches taken during evaluation is available to facilitate pruning.
--
-- @'JetDag' jt@ is used to create DAGs containing jets of @'JetType' jt@ by finding subexpressions that match the jet specifications of @jt@.
data JetDag jt a b = Dag { dagRoot :: IdentityRoot a b
                         , dagMap :: Map.Map Hash256 (DagMapContents jt)
                         -- During evaluation we log a map from the IMR of Case branches taken to the CMR of the untaken branch.
                         -- A value of 'Right hash' is the CMR of the Right branch and it is logged when the Left branch is taken.
                         -- A value of 'Left hash' is the CMR of the Left branch and it is logged when the Right branch is taken.
                         , dagEval :: FastEvalLog (MapSet Hash256 (Either Hash256 Hash256)) jt a b
                         }

-- Each entry in the 'dagMap' contains an untyped term with references to the map index of its subexpressions, and the 'MatcherInfo' of some 'JetType'.
data DagMapContents jt = DMC { dmcTerm :: UntypedTermF (SomeArrow jt) UntypedValue Hash256, dmcMatcher :: Maybe (SomeArrow (MatcherInfo jt)) }

-- | A 'JetDag' instance that matches 'NoJets'.
type NoJetDag a b = JetDag NoJets a b

dmcTerm_ f dmc = (\x -> dmc {dmcTerm = x}) <$> f (dmcTerm dmc)

rightCase_ f (Case a b c d l r) = Case a b c d l <$> f r
rightCase_ f x = pure x

leftCase_ f (Case a b c d l r) = (\x -> Case a b c d x r) <$> f l
leftCase_ f x = pure x

just_ f = some_ f

pruneMap :: JetDag jt a b -> PrimEnv -> a -> Maybe (Map.Map Hash256 (DagMapContents jt))
pruneMap t env a = Map.foldrWithKey f (dagMap t) . getMapSet <$> fastEvalLog (dagEval t) env a
 where
   f key logs | Set.null rights = let [Left cmr] = Set.elems lefts
                                      hRoot = hiddenRoot cmr
                               in Map.insert hRoot (DMC (uHidden cmr) Nothing)
                                . ((at key.just_.dmcTerm_.leftCase_).~hRoot)
              | Set.null lefts  = let [Right cmr] = Set.elems rights
                                      hRoot = hiddenRoot cmr
                               in Map.insert hRoot (DMC (uHidden cmr) Nothing)
                                . ((at key.just_.dmcTerm_.rightCase_).~hRoot)
                   | otherwise  = id
    where
     (lefts, rights) = Set.partition isLeft logs

-- Topologically sort the 'Dag' into a list.
-- Any jets found are condensed into 'uJet' nodes.
linearizeDag :: (JetType jt, TyC a, TyC b) => IdentityRoot a b -> Map.Map Hash256 (DagMapContents jt) -> SimplicityDag [] () (SomeArrow jt) UntypedValue
linearizeDag dagRoot dagMap = execLinearM . go . identityHash $ dagRoot
 where
  someArrowMatcher (SomeArrow jm) = SomeArrow <$> matcher jm
  go h = do
    mi <- use (at h)
    case mi of
     Just i -> return i
     Nothing -> case someArrowMatcher =<< dmcMatcher contents of
                  Just jt -> tellNode h (uJet jt)
                  Nothing -> traverse go (dmcTerm contents) >>= tellNode h
   where
    contents = dagMap ! h

-- | A type isomorphic to @forall term. Simplicity term => term a b@ accessed by 'unwap'.
-- Because the type @forall term. Simplicity term => term a b@ is polymorphic, it is very difficult to memoize computations that produce such a type.
-- Internally `WrappedTerm` implements a co-yoneda transformation to provide a concrete hook for memoizing values.
type WrappedSimplicity = WrappedTerm Simplicity

data WrappedTerm simplicity a b where
  (:@:) :: (forall term. simplicity term => x -> term a b) -> x -> WrappedTerm simplicity a b

-- | Transform a @WrappedTerm simplicity@ to a @forall term. simplicity term => term a b@.
unwrap :: simplicity term => WrappedTerm simplicity a b -> term a b
unwrap (f :@: x) = f x

-- Not for export.
-- Input DAG must be well typed.
wrapWellTypedCheck :: (JetType jt, TyC a, TyC b) => SimplicityDag Seq Ty (SomeArrow jt) UntypedValue -> WrappedSimplicity a b
wrapWellTypedCheck dag = k :@: dag
 where
  k x = case typeCheck x of
          Right pass -> pass
          Left e -> error $ "wrapWellTypedCheck: " ++ e

-- | Find all the expressions in a term that can be replaced with jets of type @jt@.
-- Because discounted jets are not transparent, this replacement will change the CMR of the term.
-- In particular the CMR values passed to 'disconnect' may be different, and thus the result of
-- evaluation could change in the presence of 'disconnect'.
jetSubst :: forall k jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> WrappedSimplicity a b
jetSubst t = wrapWellTypedCheck pass1
 where
  -- The patterns should never fail as we are running type inference on terms that are already known to be well typed.
  -- A failure of a pattern match here suggests there is an error in the type inference engine.
  -- The first pass matches jets and wraps them in a uJet combinator to ensure their types are not simplified by the type inference pass, which could possibly destroy the structure of the jets.
  pass1 = case typeInference t (linearizeDag (dagRoot t) (dagMap t)) of
            Right pass -> pass
            Left e -> error $ "jetSubst.pass1: " ++ e

-- | Performs 'jetSubst' and then evaluates the expression in the given environment and input to prune unused case branches,
-- which transforms some case expressions into assertions.
-- The resulting expression should always have the same CMR as the expression that 'jetSubst' would return.
pruneSubst :: forall jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> PrimEnv -> a -> Maybe (WrappedSimplicity a b)
pruneSubst t env a = wrapWellTypedCheck . pass2 <$> pruneMap pass1 env a
 where
  -- The first pass substutes jets so we can execute them using fastEval.
  pass1 :: JetDag jt a b
  pass1 = unwrap (jetSubst t)
  pass2 pMap = case typeInference t (linearizeDag (dagRoot pass1) pMap) of
                         Right pass -> pass
                         Left e -> error $ "jetDag.pass2: " ++ e

-- | Given a Simplicity expression, return a type annotated 'SimplicityDag', with shared subexpressions and @'JetType' jt@ jets, that is suitable for serialization using "Simplicity.Serialization.BitString".
--
-- Any discounted jets marked in the original expression are discarded and replaced with their specification.
-- After the discounted jets are replaced, the Simplicity expression is scanned for jets matching the 'JetType' @jt@, which will introduce a new set of jets.
-- If a different set of jets are introduced, then the 'CommitmentRoot' of the result might also not match the 'CommitmentRoot' of the input.
-- This function invokes type inference to ensure that the type annotations are principle types (with type variables instantiated at unit types)
-- in order to ensure maximum sharing of expressions with identical 'identityHash's.
jetDag :: forall jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> SimplicityDag Seq Ty (SomeArrow jt) UntypedValue
jetDag t = case typeInference t (linearizeDag (dagRoot pass1) (dagMap pass1)) of
             Right pass -> pass
             Left e -> error $ "jetDag.pass2: " ++ e
 where
  -- The first pass inferes principle types, so that witness values are properly truncated.
  pass1 :: JetDag jt a b
  pass1 = unwrap (jetSubst t)

-- Add an entry mapping the identity root of a case combinator to the commitment root of either the left or right branch of that case expression.
logRoot :: (TyC x, TyC a, TyC b, TyC c, TyC d) => (IdentityRoot (Either a b, c) d) -> (Either (CommitmentRoot (a, c) d) (CommitmentRoot (b, c) d)) -> JetDag jt (x, c) d -> JetDag jt (x, c) d
logRoot ir cr ~(Dag dr dm de) = Dag dr dm (fastEvalTell (singleton (identityHash ir) (commitmentRoot +++ commitmentRoot $ cr)) de)

-- These combinators are used in to assist making 'Dag' instances.
mkLeaf idComb eComb uComb =
   Dag { dagRoot = root
       , dagMap = Map.singleton (identityHash root) (DMC uComb (SomeArrow <$> jm))
       , dagEval = eval
       }
  where
   root = idComb
   eval = eComb
   jm = fastEvalMatcher eval

mkUnary idComb eComb uComb t =
   Dag { dagRoot = root
       , dagMap = Map.insert (identityHash root) (DMC (uComb (identityHash (dagRoot t))) (SomeArrow <$> jm))
                $ dagMap t
       , dagEval = eval
       }
  where
   root = idComb (dagRoot t)
   eval = eComb (dagEval t)
   jm = fastEvalMatcher eval

mkBinary idComb eComb uComb s t =
   Dag { dagRoot = root
       , dagMap = Map.insert (identityHash root) (DMC (uComb (identityHash (dagRoot s)) (identityHash (dagRoot t))) (SomeArrow <$> jm))
                $ union
       , dagEval = eval
       }
  where
   root = idComb (dagRoot s) (dagRoot t)
   eval = eComb (dagEval s) (dagEval t)
   jm = fastEvalMatcher eval
   union = Map.union (dagMap s) (dagMap t)

-- 'Dag' instances for Simplicity expressions.
instance JetType jt => Core (JetDag jt) where
  iden = mkLeaf iden iden uIden
  comp = mkBinary comp comp uComp
  unit = mkLeaf unit unit uUnit
  injl = mkUnary injl injl uInjl
  injr = mkUnary injr injr uInjr
  -- Log the branches taken by case during evaluation for pruning purposes.
  -- A value of 'Right hash' logs the CMR of the Right branch when the Left branch is taken.
  -- A value of 'Left hash' logs the CMR of the Left branch when the Right branch is taken.
  match s t = result
   where
    result = mkBinary match match uCase (logRoot (dagRoot result) (Right . delegatorRoot . fastEvalSem $ dagEval t) s)
                                        (logRoot (dagRoot result) (Left  . delegatorRoot . fastEvalSem $ dagEval s) t)
  pair = mkBinary pair pair uPair
  take = mkUnary take take uTake
  drop = mkUnary drop drop uDrop

instance JetType jt => Assert (JetDag jt) where
  assertl s h = Dag { dagRoot = root
                    , dagMap = Map.insert (identityHash root) (DMC (uCase (identityHash (dagRoot s)) hRoot) (SomeArrow <$> jm))
                             . Map.insert hRoot (DMC (uHidden h) Nothing)
                             $ dagMap s
                    , dagEval = eval
                    }
   where
    hRoot = hiddenRoot h
    root = assertl (dagRoot s) h
    eval = assertl (dagEval s) h
    jm = fastEvalMatcher eval
  assertr h t = Dag { dagRoot = root
                    , dagMap = Map.insert (identityHash root) (DMC (uCase hRoot (identityHash (dagRoot t))) (SomeArrow <$> jm))
                             . Map.insert hRoot (DMC (uHidden h) Nothing)
                             $ dagMap t
                    , dagEval = eval
                    }
   where
    hRoot = hiddenRoot h
    root = assertr h (dagRoot t)
    eval = assertr h (dagEval t)
    jm = fastEvalMatcher eval
  fail b = mkLeaf (fail b) (fail b) (uFail b)

instance Witness (JetDag jt) where
  witness v = mkLeaf (witness v) (witness v) (uWitness (untypedValue v))

instance JetType jt => Delegate (JetDag jt) where
  disconnect = mkBinary disconnect disconnect uDisconnect

instance JetType jt => Primitive (JetDag jt)  where
  primitive p = mkLeaf (primitive p) (primitive p) (error "Primitives cannot be directly serialized.  They can only be part of jet specifications.")

-- Exisiting jets are discarded when coverting to a dag.  They are reconstructed using a jet matcher.
instance JetType jt => Jet (JetDag jt) where
  jet w t = Dag { dagRoot = root
                -- We make this identityHash point to the same subexpression as the root of t.
                -- This lets the jet matcher match on nodes marked as jets, but otherwise the JetDag ignores marked jets.
                , dagMap = Map.insert (identityHash root) (DMC (dmcTerm (map ! identityHash (dagRoot dag))) (SomeArrow <$> jm))
                         $ map
                , dagEval = eval
                }
   where
    dag = t
    root = jet w t
    eval = jet w t
    jm = fastEvalMatcher eval
    map = dagMap dag

instance JetType jt => Simplicity (JetDag jt) where
