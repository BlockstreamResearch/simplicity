{-# LANGUAGE NoMonomorphismRestriction #-}
module Simplicity.Term
 ( module Simplicity.Ty
 , Core, iden, comp, unit, injl, injr, match, pair, take, drop
 , (>>>), (&&&)
 , oh, ih, ooh, oih, ioh, iih, oooh, iooh, ooih, ioih, oioh, iioh, oiih, iiih
 ) where

import Prelude hiding (take, drop)

import Simplicity.Ty

class Core term where
  iden :: TyC a => term a a
  comp :: (TyC a, TyC b, TyC c) => term a b -> term b c -> term a c
  unit :: TyC a => term a ()
  injl :: (TyC a, TyC b, TyC c) => term a b -> term a (Either b c)
  injr :: (TyC a, TyC b, TyC c) => term a c -> term a (Either b c)
  match :: (TyC a, TyC b, TyC c, TyC d) => term (a, c) d -> term (b, c) d -> term (Either a b, c) d
  pair :: (TyC a, TyC b, TyC c) => term a b -> term a c -> term a (b, c)
  take :: (TyC a, TyC b, TyC c) => term a c -> term (a, b) c
  drop :: (TyC a, TyC b, TyC c) => term b c -> term (a, b) c

-- same precidence as in Control.Category.
infixr 1 >>>

(>>>) = comp

-- same precidence as in Control.Arrow.
infixr 3 &&&

(&&&) = pair
oh = take iden
ih = drop iden
ooh = take oh
ioh = drop oh
oih = take ih
iih = drop ih
oooh = take ooh
iooh = drop ooh
oioh = take ioh
iioh = drop ioh
ooih = take oih
ioih = drop oih
oiih = take iih
iiih = drop iih

instance Core (->) where
  iden = id
  comp t s = s . t
  unit = const ()
  injl t a = Left (t a)
  injr t a = Right (t a)
  match s _ (Left a, c)  = s (a, c)
  match _ t (Right b, c) = t (b, c)
  pair s t a = (s a, t a)
  take t (a, _) = t a
  drop t (_, b) = t b
