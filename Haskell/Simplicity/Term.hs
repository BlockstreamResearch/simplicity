{-# LANGUAGE UndecidableInstances, RankNTypes #-}
module Simplicity.Term
 ( module Simplicity.Term.Core
 , Primitive(..)
 , Jet(..)
 , Delegate(..)
 , Simplicity(..)
 ) where

import Control.Arrow (Kleisli(..))
import Control.Monad.Reader.Class (MonadReader(..))
import qualified Control.Monad.Fail as Fail

import Simplicity.Digest
import Simplicity.Term.Core
import Simplicity.Primitive

class Primitive term where
  primitive :: Prim a b -> term a b

instance (MonadReader PrimEnv m, Fail.MonadFail m) => Primitive (Kleisli m) where
  primitive p = Kleisli $ \a -> do
   env <- ask
   let err = fail $ "Simplicity.Term.primitive in Primitive (Kleisli m) instance: " ++ primName p ++ " failed."
   maybe err return $ primSem env p a

class (Assert term, Primitive term) => Jet term where
  jet :: (TyC a, TyC b) => (forall term0. (Assert term0, Primitive term0) => term0 a b) -> term a b

instance (MonadReader PrimEnv m, Fail.MonadFail m) => Jet (Kleisli m) where
  jet t = t

class Delegate term where
  disconnect :: (TyC a, TyC b, TyC c, TyC d) => term (a, Hash256) (b, d) -> term b c -> term a (c, d)

class (Jet term, Witness term, Delegate term) => Simplicity term where
