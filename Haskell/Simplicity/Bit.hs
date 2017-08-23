module Simplicity.Bit 
 ( Bit, fromBit
 , false, true, cond, not, and, or
 ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.Term

type Bit = Either () ()

fromBit :: Bit -> Bool
fromBit (Left ()) = False
fromBit (Right ()) = True

false :: (TyC a, Core term) => term a Bit
false = injl unit

true :: (TyC a, Core term) => term a Bit
true = injr unit

cond :: (TyC a, TyC b, Core term) => term a b -> term a b -> term (Bit, a) b
cond thn els = match (drop els) (drop thn)

not :: (TyC a, Core term) => term a Bit -> term a Bit
not t = t &&& unit >>> cond false true

and :: (TyC a, Core term) => term a Bit -> term a Bit -> term a Bit
and s t = s &&& iden >>> cond t false

or :: (TyC a, Core term) => term a Bit -> term a Bit -> term a Bit
or s t = s &&& iden >>> cond true t
