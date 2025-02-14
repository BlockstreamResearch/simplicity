-- | This module provides the functional semantics of the full 'Simplicity' language.
-- The 'Semantics' arrow is an instance of the 'Simplicity' class and 'sem' evaluates terms of the full Simplicity language.
-- The 'fastEval' implements the evaluation using the jets from the specified 'JetType'.
module Simplicity.Semantics
 ( Semantics, sem
 , FastEval, fastEval
 , FastEvalLog(..), fastEvalLog, fastEvalTell
 , PrimEnv
 ) where

import Prelude hiding (drop, take, fail)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer (WriterT(..), tell)

import Simplicity.Delegator.Impl
import Simplicity.JetType
import Simplicity.Primitive
import Simplicity.Term

-- | Adds logging to the 'Semantics' for Simplicity.
--
-- The @log@ ought to be a commutative and idempontent monoid.
--
-- Currently logging is used to implement pruning.
type SemanticsLog log a b = Delegator (Kleisli (WriterT log (ReaderT PrimEnv Maybe))) a b

-- | Execute the functional semantics of the full Simplicity language with delegation.
-- If successful, return the log in addition to the output value.
semLog :: SemanticsLog log a b -> PrimEnv -> a -> Maybe (b, log)
semLog = flip . ((runReaderT . runWriterT) .) . runKleisli . runDelegator

-- | Add data to the 'SemanticsLog' of a Simplicity expression.
--
-- The @log@ ought to be a commutative and idempontent monoid.
semTell :: Monoid log => log -> SemanticsLog log a b -> SemanticsLog log a b
semTell msg ~(Delegator rs (Kleisli fs)) = Delegator rs (Kleisli $ \a -> tell msg >> fs a)

-- | The functional semantics of the full Simplicity language consists of
--
-- * Partial effect via the 'Maybe' effect.
--
-- * Environment effects via the 'Control.Monad.Reader.Reader' effect for primitives to access the 'PrimEnv'.
--
-- * Delegation via the 'Delegator' helper.
type Semantics a b = SemanticsLog () a b

-- | @
-- sem :: (forall term. Simplicity term => term a b) -> PrimEnv -> a -> Maybe b
-- @
--
-- Execute the functional semantics of the full Simplicity language with delegation.
sem :: SemanticsLog () a b -> PrimEnv -> a -> Maybe b
sem = flip . ((runReaderT . fmap fst . runWriterT) .) . runKleisli . runDelegator

instance Primitive p => Primitive (Delegator p) where
  primitive p = Delegator (primitive p) (primitive p)

instance Jet p => Jet (Delegator p) where
  jet w t = Delegator (jet w t) (jet w t)

instance (Jet p, Witness p) => Simplicity (Delegator p) where

-- | A Simplicity instance for 'fastEval'
type FastEval jt a b = FastEvalLog () jt a b

-- | 'fastEval' optimizes Simplicity evaluation using jets.
-- Unlike using 'Simplicity.Dag.jetSubst', 'fastEval' will not modify the commitment roots and therefore will always return the same
-- result as 'sem' in the presence of 'disconnect'.
--
-- @
-- 'fastEval' t === 'sem' t
-- @
fastEval :: FastEval jt a b -> PrimEnv -> a -> Maybe b
fastEval = sem . fastEvalSem

-- | A Simplicity instance for 'fastEval'
data FastEvalLog log jt a b = FastEvalLog { fastEvalSem :: SemanticsLog log a b
                                          , fastEvalMatcher :: Maybe (MatcherInfo jt a b)
                                          }

-- | Add data to the 'FastEvalLog' of a Simplicity expression.
--
-- The @log@ ought to be a commutative and idempontent monoid.
fastEvalTell :: (Monoid log) => log -> FastEvalLog log jt a b -> FastEvalLog log jt a b
fastEvalTell msg (FastEvalLog fs fm) = FastEvalLog (semTell msg fs) fm

-- | If evaluation is successful, return the total of all 'fastEvalTell' data that was logged.
fastEvalLog :: FastEvalLog log jt a b -> PrimEnv -> a -> Maybe log
fastEvalLog prog env a = snd <$> semLog (fastEvalSem prog) env a

proxyImplementation :: (JetType jt, TyC a, TyC b) => proxy jt a b -> jt a b -> PrimEnv -> a -> Maybe b
proxyImplementation _proxy = implementation

withJets :: (Monoid log, JetType jt, TyC a, TyC b) => FastEvalLog log jt a b -> FastEvalLog log jt a b
withJets ~fe@(FastEvalLog ~(Delegator rs (Kleisli fs)) jm) =
  -- 'withJets' does not adjust the commitment root.
  FastEvalLog { fastEvalSem = Delegator rs (Kleisli optfs)
              , fastEvalMatcher = jm
              }
 where
  optfs a | Just jt <- matcher =<< jm = lift . ReaderT $ flip (proxyImplementation fe jt) a
          | otherwise = fs a

mkLeaf sComb jmComb = withJets $
  FastEvalLog { fastEvalSem = sComb
              , fastEvalMatcher = jmComb
              }

mkUnary sComb jmComb t = withJets $
  FastEvalLog { fastEvalSem = sComb (fastEvalSem t)
              , fastEvalMatcher = jmComb <*> fastEvalMatcher t
              }
mkBinary sComb jmComb s t = withJets $
  FastEvalLog { fastEvalSem = sComb (fastEvalSem s) (fastEvalSem t)
              , fastEvalMatcher = jmComb <*> fastEvalMatcher s <*> fastEvalMatcher t
              }

instance (Monoid log, JetType jt) => Core (FastEvalLog log jt) where
  iden = mkLeaf iden (pure iden)
  comp = mkBinary comp (pure comp)
  unit = mkLeaf unit (pure unit)
  injl = mkUnary injl (pure injl)
  injr = mkUnary injr (pure injr)
  match = mkBinary match (pure match)
  pair = mkBinary pair (pure pair)
  take = mkUnary take (pure take)
  drop = mkUnary drop (pure drop)

instance (Monoid log, JetType jt) => Assert (FastEvalLog log jt) where
  assertl s h = mkUnary (flip assertl h) (pure (flip assertl h)) s
  assertr h t = mkUnary (assertr h) (pure (assertr h)) t
  fail b = mkLeaf (fail b) (pure (fail b))

instance Monoid log => Witness (FastEvalLog log jt) where
  witness v =
    FastEvalLog { fastEvalSem = witness v
                , fastEvalMatcher = Nothing
                }

instance (Monoid log, JetType jt) => Delegate (FastEvalLog log jt) where
  disconnect = mkBinary disconnect Nothing

instance (Monoid log, JetType jt) => Primitive (FastEvalLog log jt)  where
  primitive p = mkLeaf (primitive p) (pure (primitive p))

instance (Monoid log, JetType jt) => Jet (FastEvalLog log jt) where
  jet w t = result
   where
    result = FastEvalLog { fastEvalSem = Delegator (jet w t) fs
                         , fastEvalMatcher = jm
                         }
    FastEvalLog (Delegator _ fs) jm = t `asTypeOf` result

instance (Monoid log, JetType jt) => Simplicity (FastEvalLog log jt) where
