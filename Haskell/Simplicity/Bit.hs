module Simplicity.Bit 
 ( Bit, false, true, cond, not, and, or
 ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.Term

type Bit = Either () ()

false :: Core term => term a Bit
false = injl unit

true :: Core term => term a Bit
true = injr unit

cond :: Core term => term a b -> term a b -> term (Bit, a) b
cond thn els = match (drop els) (drop thn)

not :: Core term => term a Bit -> term a Bit
not t = pair t unit >>> cond false true

and :: Core term => term a Bit -> term a Bit -> term a Bit
and s t = pair s iden >>> cond t false

or :: Core term => term a Bit -> term a Bit -> term a Bit
or s t = pair s iden >>> cond true t
