-- | This module provides the functional semantics of the full 'Simplicity' language.
-- The 'Semantics' arrow is an instance of the 'Simplicity' class and 'sem' evaluates terms of the full Simplicity langauge.
module Simplicity.Semantics
 ( Semantics, sem
 , FastEval, fastEval
 , PrimEnv
 ) where

import Prelude hiding (drop, take, fail)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))

import Simplicity.Digest
import Simplicity.JetType
import Simplicity.MerkleRoot
import Simplicity.Primitive
import Simplicity.Programs.Generic
import Simplicity.Term
import Simplicity.Ty.Word

-- Note: 'Delegator' differs from 'Simplicity.Tensor.Product CommitmentRoot' due to a different 'Delegate' instance.
-- | @'Delegator' p@ is a helper data type for creating a 'Delegate' instance.
-- @p@ is typically at least an instance of 'Core'.
data Delegator p a b = Delegator { delegatorRoot :: CommitmentRoot a b
                                 , runDelegator :: p a b -- ^ Extract the @p a b@ arrow from the 'Delegator'
                                 }

-- | The functional semantics of the full Simplicity language consists of
--
-- * Partial effect via the 'Maybe' effect.
--
-- * Environment effects via the 'Control.Monad.Reader.Reader' effect for primitives to access the 'PrimEnv'.
--
-- * Delegation via the 'Delegator' helper.
type Semantics a b = Delegator (Kleisli (ReaderT PrimEnv Maybe)) a b

-- | @
-- sem :: (forall term. Simplicity term => term a b) -> PrimEnv -> a -> Maybe b
-- @
--
-- Execute the fuctional semantics of the full Simplicity language with delegation.
sem :: Semantics a b -> PrimEnv -> a -> Maybe b
sem = flip . (runReaderT .) . runKleisli . runDelegator

instance Core p => Core (Delegator p) where
  iden = Delegator iden iden
  comp ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (comp rs rt) (comp fs ft)
  unit = Delegator unit unit
  injl ~(Delegator rt ft) = Delegator (injl rt) (injl ft)
  injr ~(Delegator rt ft) = Delegator (injr rt) (injr ft)
  match ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (match rs rt) (match fs ft)
  pair ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (pair rs rt) (pair fs ft)
  take ~(Delegator rt ft) = Delegator (take rt) (take ft)
  drop ~(Delegator rt ft) = Delegator (drop rt) (drop ft)

instance Assert p => Assert (Delegator p) where
  assertl ~(Delegator rs fs) t = Delegator (assertl rs t) (assertl fs t)
  assertr s ~(Delegator rt ft) = Delegator (assertr s rt) (assertr s ft)
  fail b = Delegator (fail b) (fail b)

instance Primitive p => Primitive (Delegator p) where
  primitive p = Delegator (primitive p) (primitive p)

instance Jet p => Jet (Delegator p) where
  jet t = Delegator (jet t) (jet t)

instance Witness p => Witness (Delegator p) where
  witness b = Delegator (witness b) (witness b)

instance Core p => Delegate (Delegator p) where
  disconnect ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (disconnect rs rt) f
   where
    root256 = toWord256 . integerHash256 $ commitmentRoot rt
    f = iden &&& scribe root256 >>> fs >>> take iden &&& drop ft

instance (Jet p, Witness p) => Simplicity (Delegator p) where

fastEval = sem . fastEvalSem

data FastEval jt a b = FastEval { fastEvalSem :: Semantics a b
                                  , fastEvalMatcher :: Maybe (MatcherInfo jt a b)
                                  }

proxyImplementation :: (JetType jt, TyC a, TyC b) => proxy jt a b -> jt a b -> PrimEnv -> a -> Maybe b
proxyImplementation _proxy = implementation

withJets :: (JetType jt, TyC a, TyC b) => FastEval jt a b -> FastEval jt a b
withJets ~fe@(FastEval ~(Delegator rs fs) jm) | Just jt <- matcher =<< jm =
  FastEval { fastEvalSem = Delegator rs . Kleisli $ ReaderT . flip (proxyImplementation fe jt)
            , fastEvalMatcher = fastEvalMatcher fe
            }
withJets fe | otherwise = fe

mkLeaf sComb jmComb = withJets $
  FastEval { fastEvalSem = sComb
           , fastEvalMatcher = jmComb
           }

mkUnary sComb jmComb t = withJets $
  FastEval { fastEvalSem = sComb (fastEvalSem t)
           , fastEvalMatcher = jmComb <*> fastEvalMatcher t
           }
mkBinary sComb jmComb s t = withJets $
  FastEval { fastEvalSem = sComb (fastEvalSem s) (fastEvalSem t)
           , fastEvalMatcher = jmComb <*> fastEvalMatcher s <*> fastEvalMatcher t
           }

instance JetType jt => Core (FastEval jt) where
  iden = mkLeaf iden (pure iden)
  comp = mkBinary comp (pure comp)
  unit = mkLeaf unit (pure unit)
  injl = mkUnary injl (pure injl)
  injr = mkUnary injr (pure injr)
  match = mkBinary match (pure match)
  pair = mkBinary pair (pure pair)
  take = mkUnary take (pure take)
  drop = mkUnary drop (pure drop)

instance JetType jt => Assert (FastEval jt) where
  assertl s h = mkUnary (flip assertl h) (pure (flip assertl h)) s
  assertr h t = mkUnary (assertr h) (pure (assertr h)) t
  fail b = mkLeaf (fail b) (pure (fail b))

instance Witness (FastEval jt) where
  witness v =
    FastEval { fastEvalSem = witness v
             , fastEvalMatcher = Nothing
             }

instance JetType jt => Delegate (FastEval jt) where
  disconnect = mkBinary disconnect Nothing

instance JetType jt => Primitive (FastEval jt)  where
  primitive p = mkLeaf (primitive p) (pure (primitive p))

instance JetType jt => Jet (FastEval jt) where
  jet t = result
   where
    result = FastEval { fastEvalSem = Delegator (jet t) fs
                      , fastEvalMatcher = jm
                      }
    FastEval (Delegator _ fs) jm = t `asTypeOf` result

instance JetType jt => Simplicity (FastEval jt) where
