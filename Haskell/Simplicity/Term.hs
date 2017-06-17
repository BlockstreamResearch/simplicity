{-# LANGUAGE NoMonomorphismRestriction #-}
module Simplicity.Term
 ( Category, iden, comp, (>>>)
 , Core, unit, injl, injr, match, pair, take, drop
 , (&&&)
 , oh, ih, ooh, oih, ioh, iih, oooh, iooh, ooih, ioih, oioh, iioh, oiih, iiih
 ) where

import Control.Category (Category, (>>>))
import qualified Control.Category as Cat
import Prelude hiding (take, drop)

-- same precidence as in Control.Arrow.
infixr 3 &&&

iden :: Category term => term a a
iden = Cat.id

comp :: Category term => term a b -> term b c -> term a c
comp = (>>>)

class Category term => Core term where
  unit :: term a ()
  injl :: term a b -> term a (Either b c)
  injr :: term a c -> term a (Either b c)
  match :: term (a, c) d -> term (b, c) d -> term (Either a b, c) d
  pair :: term a b -> term a c -> term a (b, c)
  take :: term a c -> term (a, b) c
  drop :: term b c -> term (a, b) c

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
  unit = const ()
  injl t a = Left (t a)
  injr t a = Right (t a)
  match s _ (Left a, c)  = s (a, c)
  match _ t (Right b, c) = t (b, c)
  pair s t a = (s a, t a)
  take t (a, _) = t a
  drop t (_, b) = t b
