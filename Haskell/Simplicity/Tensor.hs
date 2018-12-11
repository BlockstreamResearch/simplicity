-- | This module provides a product for computing multiple interpretations of Simplicity simutaneously.
-- Other tensors can be added when they are needed.
module Simplicity.Tensor
  ( Product(..)
  ) where

import Prelude hiding (fail, drop, take)

import Simplicity.Term

data Product p q a b = Product { fstProduct :: p a b
                               , sndProduct :: q a b
                               }
                       deriving Show

instance (Core p, Core q) => Core (Product p q) where
  iden = Product iden iden
  comp ~(Product rs fs) ~(Product rt ft) = Product (comp rs rt) (comp fs ft)
  unit = Product unit unit
  injl ~(Product rt ft) = Product (injl rt) (injl ft)
  injr ~(Product rt ft) = Product (injr rt) (injr ft)
  match ~(Product rs fs) ~(Product rt ft) = Product (match rs rt) (match fs ft)
  pair ~(Product rs fs) ~(Product rt ft) = Product (pair rs rt) (pair fs ft)
  take ~(Product rt ft) = Product (take rt) (take ft)
  drop ~(Product rt ft) = Product (drop rt) (drop ft)

instance (Assert p, Assert q) => Assert (Product p q) where
  assertl ~(Product rs fs) t = Product (assertl rs t) (assertl fs t)
  assertr s ~(Product rt ft) = Product (assertr s rt) (assertr s ft)
  fail b = Product (fail b) (fail b)

instance (Primitive p, Primitive q) => Primitive (Product p q) where
  primitive p = Product (primitive p) (primitive p)

instance (Jet p, Jet q) => Jet (Product p q) where
  jet t = Product (jet t) (jet t)

instance (Witness p, Witness q) => Witness (Product p q) where
  witness b = Product (witness b) (witness b)

instance (Delegate p, Delegate q) => Delegate (Product p q) where
  disconnect ~(Product rs fs) ~(Product rt ft) = Product (disconnect rs rt) (disconnect fs ft)

instance (Simplicity p, Simplicity q) => Simplicity (Product p q) where
