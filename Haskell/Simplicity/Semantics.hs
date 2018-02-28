module Simplicity.Semantics 
 ( Semantics, sem
 ) where

import Prelude hiding (drop, take)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))

import Simplicity.Digest
import Simplicity.MerkleRoot
import Simplicity.Primitive
import Simplicity.Term
import Simplicity.Ty.Word

data Semantics a b = Semantics (CommitmentRoot a b) (Kleisli (ReaderT PrimEnv Maybe) a b)

sem :: Semantics a b -> a -> ReaderT PrimEnv Maybe b
sem (Semantics _ (Kleisli f)) = f

instance Core Semantics where
  iden = Semantics iden iden
  comp (Semantics rs fs) (Semantics rt ft) = Semantics (comp rs rt) (comp fs ft)
  unit = Semantics unit unit
  injl (Semantics rt ft) = Semantics (injl rt) (injl ft)
  injr (Semantics rt ft) = Semantics (injr rt) (injr ft)
  match (Semantics rs fs) (Semantics rt ft) = Semantics (match rs rt) (match fs ft)
  pair (Semantics rs fs) (Semantics rt ft) = Semantics (pair rs rt) (pair fs ft)
  take (Semantics rt ft) = Semantics (take rt) (take ft)
  drop (Semantics rt ft) = Semantics (drop rt) (drop ft)

instance Assert Semantics where
  assertl (Semantics rs fs) t = Semantics (assertl rs t) (assertl fs t)
  assertr s (Semantics rt ft) = Semantics (assertr s rt) (assertr s ft)

instance Primitive Semantics where
  primitive p = Semantics (primitive p) (primitive p)

instance Jet Semantics where
  jet t = Semantics (jet t) (jet t)

instance Witness Semantics where
  witness b = Semantics (witness b) (witness b)

instance Delegate Semantics where
  disconnect (Semantics rs fs) (Semantics rt ft) = Semantics (disconnect rs rt) (Kleisli f)
   where
    f a = runKleisli fs (a, commitmentRoot rt) >>= runKleisli (first ft)

instance Simplicity Semantics where
