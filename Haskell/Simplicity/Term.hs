{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module defines the term language for Simplicity using tagless-final style.
module Simplicity.Term
 ( module Simplicity.Ty
 , Core(..)
 -- * Notation for terms
 , (>>>), (&&&)
 -- | The following expressions are for short sequences of 'take' and 'drop', with 'iden' that is used to access components of Simplicity inputs.
 --
 -- * @o@ means 'take'
 -- * @i@ means 'drop'
 -- * @h@ means 'iden'
 --
 -- For example, @'oih' = 'take' ('drop' 'iden')@.
 --
 -- The string of @i@'s and @o@'s is meant to resemble a binary number that denotes an index to the leaves of a perfect binary tree.
 , oh, ih, ooh, oih, ioh, iih, oooh, ooih, oioh, oiih, iooh, ioih, iioh, iiih
 ) where

import Prelude hiding (take, drop)

import Simplicity.Ty

-- | Values of type @forall term. 'Core' term => term a b@ are well-typed terms of the core Simplicity language represented in tagless-final style.
--
-- Functions that consume terms in this style are defined by creating instances of the 'Core' class.
-- These instances are called /Simplicity Algebras/.
class Core term where
  iden :: TyC a => term a a
  comp :: (TyC a, TyC b, TyC c) => term a b -> term b c -> term a c
  unit :: TyC a => term a ()
  injl :: (TyC a, TyC b, TyC c) => term a b -> term a (Either b c)
  injr :: (TyC a, TyC b, TyC c) => term a c -> term a (Either b c)
  -- | Because @case@ is a reserved word in Haskell, we will be calling Simplicity's @case@ combinator 'match' instead.
  match :: (TyC a, TyC b, TyC c, TyC d) => term (a, c) d -> term (b, c) d -> term (Either a b, c) d
  pair :: (TyC a, TyC b, TyC c) => term a b -> term a c -> term a (b, c)
  take :: (TyC a, TyC b, TyC c) => term a c -> term (a, b) c
  drop :: (TyC a, TyC b, TyC c) => term b c -> term (a, b) c

-- same precidence as in Control.Category.
infixr 1 >>>

-- | @s '>>>' t = 'comp' s t@
(>>>) :: (Core term, TyC a, TyC b, TyC c) => term a b -> term b c -> term a c
(>>>) = comp

-- same precidence as in Control.Arrow.
infixr 3 &&&

-- | @s '&&&' t = 'pair' s t@
(&&&) :: (Core term, TyC a, TyC b, TyC c) => term a b -> term a c -> term a (b, c)
(&&&) = pair

oh :: (Core term, TyC x, TyC b) => term (x, b) x
oh = take iden

ih :: (Core term, TyC a, TyC x) => term (a, x) x
ih = drop iden

ooh :: (Core term, TyC x, TyC b, TyC c) => term ((x, b), c) x
ooh = take oh

oih :: (Core term, TyC a, TyC x, TyC c) => term ((a, x), c) x
oih = take ih

ioh :: (Core term, TyC a, TyC x, TyC c) => term (a, (x, c)) x
ioh = drop oh

iih :: (Core term, TyC a, TyC b, TyC x) => term (a, (b, x)) x
iih = drop ih

oooh :: (Core term, TyC x, TyC b, TyC c, TyC d) => term (((x, b), c), d) x
oooh = take ooh

ooih :: (Core term, TyC a, TyC x, TyC c, TyC d) => term (((a, x), c), d) x
ooih = take oih

oioh :: (Core term, TyC a, TyC x, TyC c, TyC d) => term ((a, (x, c)), d) x
oioh = take ioh

oiih :: (Core term, TyC a, TyC b, TyC x, TyC d) => term ((a, (b, x)), d) x
oiih = take iih

iooh :: (Core term, TyC a, TyC x, TyC c, TyC d) => term (a, ((x, c), d)) x
iooh = drop ooh

ioih :: (Core term, TyC a, TyC b, TyC x, TyC d) => term (a, ((b, x), d)) x
ioih = drop oih

iioh :: (Core term, TyC a, TyC b, TyC x, TyC d) => term (a, (b, (x, d))) x
iioh = drop ioh

iiih :: (Core term, TyC a, TyC b, TyC c, TyC x) => term (a, (b, (c, x))) x
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
