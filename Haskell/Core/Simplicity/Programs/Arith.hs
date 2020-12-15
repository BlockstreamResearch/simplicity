{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.Arith
  ( module Simplicity.Ty.Word
  , zero
  , one
  , add, full_add, increment, full_increment
  , subtract, full_subtract, negate, decrement, full_decrement
  , multiply, full_multiply
  , is_zero, is_one
  , le, lt
  , min, max, median
  , div2n1n, div_mod, divide, modulo, divides
  , eea, bezout, cofactors, gcd, lcm
  , msb, lsb
  , absolute_value, sign
  ) where

import Prelude hiding ( Word, drop, take, not, and, or, last
                      , subtract, negate, min, max, gcd, lcm
                      )
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Bit
import Simplicity.Programs.MultiBit
import Simplicity.Term.Core hiding (one)
import Simplicity.Ty.Word

-- | Simplicity expression for the constant function that returns the representation of 0.
--
-- @
-- 'fromWord' w ('zero' w _) = 0
-- @
zero :: Core term => Word a -> term () a
zero = low

one :: (Core term, TyC a) => Word a -> term () a
one w = true >>> left_pad_low word1 w

-- | Simplicity expression for computing the sum of two words and a carry input bit, including the carry output bit.
--
-- @
-- 'fromWord1' cout * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y + 'fromWord1' cin
--  where
--   (cout, z) = 'fullAdder' w ((x, y), cin)
-- @
full_add :: Core term => Word a -> term (Bit, (a, a)) (Bit, a)
full_add SingleV = maj &&& xor3
full_add (DoubleV w) = drop (ooh &&& ioh) &&& (oh &&& drop (oih &&& iih) >>> rec)
                   >>> iih &&& (ioh &&& oh >>> rec)
                   >>> ioh &&& (iih &&& oh)
 where
  rec = full_add w

-- | Simplicity expression for computing the sum of two words, including the carry bit.
--
-- @
-- 'fromWord1' c * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y
--  where
--   (c, z) = 'adder' w (x, y)
-- @
add :: (Core term, TyC a) => Word a -> term (a, a) (Bit, a)
add w = false &&& iden >>> full_add w

full_increment :: (Core term, TyC a) => Word a -> term (Bit, a) (Bit, a)
full_increment w = oh &&& (ih &&& (unit >>> zero w)) >>> full_add w

increment :: (Core term, TyC a) => Word a -> term a (Bit, a)
increment w = true &&& iden >>> full_increment w

-- | Simplicity expression for computing the difference of two words and a borrow input bit, also returning the borrow output bit.
--
-- @
-- 'fromWord' w z = 'fromWord1' bout * 2 ^ 'wordSize' + 'fromWord' w x - 'fromWord' w y - 'fromWord1' bin
--  where
--   (bout, z) = 'fullSubtractor' w (bin, (x, y))
-- @
full_subtract :: (Core term, TyC a) => Word a -> term (Bit, (a, a)) (Bit, a)
full_subtract w = not oh &&& drop (oh &&& (ih >>> complement w))
              >>> full_add w
              >>> not oh &&& ih

-- | Simplicity expression for computing the difference of two words, also returning the borrow bit.
--
-- @
-- 'fromWord' w z = 'fromWord1' b * 2 ^ 'wordSize' + 'fromWord' w x - 'fromWord' w y
--  where
--   (b, z) = 'subtractor' w (x, y)
-- @
subtract :: (Core term, TyC a) => Word a -> term (a, a) (Bit, a)
subtract w = false &&& iden >>> full_subtract w

negate :: (Core term, TyC a) => Word a -> term a (Bit, a)
negate w = (unit >>> zero w) &&& iden >>> subtract w

full_decrement :: (Core term, TyC a) => Word a -> term (Bit, a) (Bit, a)
full_decrement w = oh &&& (ih &&& (unit >>> zero w)) >>> full_subtract w

decrement :: (Core term, TyC a) => Word a -> term a (Bit, a)
decrement w = true &&& iden >>> full_decrement w

-- | 'fullMultiplier' is a Simplicity expression that helps compute products of larger word sizes from smaller word sizes.
--
-- @
-- 'fromWord' ('DoubleV' w) ('fullMultiplier' w ((a, b), (c, d))) = 'fromWord' w a * 'fromWord' w b  + 'fromWord' w c + 'fromWord' w d
-- @
full_multiply :: (Core term, TyC a) => Word a -> term ((a, a), (a, a)) (a, a)
full_multiply SingleV = take (cond iden false) &&& ih
                    >>> full_add SingleV
full_multiply (DoubleV w) = take (ooh &&& (ioh &&& oih))
                        &&& ((take (ooh &&& iih) &&& drop (ooh &&& ioh) >>> rec)
                        &&& (take (oih &&& iih) &&& drop (oih &&& iih) >>> rec))
                        >>> take (oh &&& ioh)
                        &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> rec))
                        >>> (oh &&& drop (ioh &&& ooh) >>> rec) &&& drop (iih &&& oih)
 where
  rec = full_multiply w

-- | Simplicity expression for computing the product of two words, returning a doubled size word.
--
-- @
-- 'fromWord' ('DoubleV' w) ('multiplier' w (x, y)) = 'fromWord' w x * 'fromWord' w y
-- @
multiply :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w

is_zero :: (Core term, TyC a) => Word a -> term a Bit
is_zero w = not (some w)

is_one :: (Core term, TyC a) => Word a -> term a Bit
is_one w = decrement w >>> drop (is_zero w)

lt :: (Core term, TyC a) => Word a -> term (a,a) Bit
lt w = subtract w >>> oh

le :: (Core term, TyC a) => Word a -> term (a,a) Bit
le w = not (ih &&& oh >>> lt w)

min :: (Core term, TyC a) => Word a -> term (a,a) a
min w = le w &&& iden >>> cond oh ih

max :: (Core term, TyC a) => Word a -> term (a,a) a
max w = le w &&& iden >>> cond ih oh

median :: (Core term, TyC a) => Word a -> term (a, (a,a)) a
median w = ((oh &&& ioh >>> min w) &&& (oh &&& iih >>> min w) >>> max w)
           &&& drop (min w) >>> max w

msb :: (Core term, TyC a) => Word a -> term a Bit
msb w = leftmost w

lsb :: (Core term, TyC a) => Word a -> term a Bit
lsb w = rightmost w

-- div3n2n (((a1,a2),a3), (b1,b2))
-- precondition
-- * [a1,a2,a3] < [b1,b2,0]
-- * 1000... <= [b1,b2]
-- postcondtion:
-- * div3n2n (((a1,a2),a3), (b1,b2)) = ([a1,a2,a3]/[b1,b2], [a1,a2,a3]%[b1,b2])
div3n2n :: (Core term, TyC a) => Word a -> term (((a, a), a), (a, a)) (a, (a, a))
div3n2n w = (ooh &&& ioh >>> approxDiv) &&& (oih &&& ih)
        >>> body
 where
  approxDiv = (ooh &&& ih >>> lt w) &&& iden >>> cond lt_case eq_case
  lt_case = false &&& div2n1n w
  eq_case = oih &&& ih >>> add w >>> oh &&& ((unit >>> high w) &&& ih)
  body = ooh &&& (((oiih &&& ioh) &&& (oioh &&& iiih >>> multiply w) >>> subtract (DoubleV w)) &&& (oioh &&& iih))
      >>> cond overflow loop0
  overflow = ioh &&& oih
  loop0 = ooh &&& (oih &&& ih) >>> cond loop1 (ioh &&& oh)
  loop1 = (oh &&& iih >>> add2w) &&& drop ((take (dec >>> ih)) &&& ih)
       >>> ooh &&& (oih &&& ih)
       >>> cond (ioh &&& oh) loop2
  loop2 = drop (take (dec >>> ih)) &&& (oh &&& iih >>> add2w >>> ih)
  dec = decrement w
  add2w = add (DoubleV w)

-- div2n1n ((a1,a2), b)
-- precondition
-- * [a1,a2] < [b,0]
-- * 1000... <= b
-- postcondtion:
-- * div2n1n ((a1,a2), b) = ([a1,a2]/b, [a1,a2]%b)
-- When precondition is false, then return all one bits.
div2n1n :: (Core term, TyC a) => Word a -> term ((a, a), a) (a, a)
div2n1n SingleV = oih &&& or ooh (not ih) >>> or oh ih &&& ih
div2n1n (DoubleV w) = conditions &&& iden >>> cond body (unit >>> high (DoubleV (DoubleV w)))
 where
  body = ((ooh &&& oioh) &&& ih >>> rec) &&& (oiih &&& ih)
     >>> ooh &&& ((oih &&& ioh) &&& iih >>> rec)
     >>> (oh &&& ioh) &&& iih
  rec = div3n2n w
  conditions = and (drop (msb (DoubleV w))) (ooh &&& ih >>> lt (DoubleV w))

divPreShift :: (Core term, TyC a) => Word b -> Vector b a -> term ((a, a), a) ((a, a), a)
divPreShift SingleV _ = iden
divPreShift (DoubleV w) v = drop (leftmost v' >>> is_zero w) &&& iden >>> cond shift iden >>> divPreShift w v'
 where
  v' = vectorComp vector2 v
  shift = (oh &&& zv >>> full_shift (DoubleV (vectorComp w v')) w >>> ih)
      &&& (ih &&& zv >>> full_shift (vectorComp w v') w >>> ih)
  zv = unit >>> zero w

divPostShift :: (Core term, TyC a) => Word b -> Vector b a -> term (a, a) (a, a)
divPostShift SingleV _ = iden
divPostShift (DoubleV w) v = drop (leftmost v' >>> is_zero w) &&& iden >>> cond shift iden >>> divPostShift w v'
 where
  v' = vectorComp vector2 v
  shift = (zv &&& oh >>> full_shift w (vectorComp w v') >>> oh)
      &&& (ih &&& zv >>> full_shift (vectorComp w v') w >>> ih)
  zv = unit >>> zero w

div_mod :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
div_mod w = (drop (is_zero w)) &&& iden
        >>> cond zero_case div_case
 where
  zero_case = ih &&& oh
  div_case = (((unit >>> zero w) &&& oh) &&& ih >>> divPreShift w SingleV >>> div2n1n w) &&& ih
         >>> ooh &&& (oih &&& ih >>> divPostShift w SingleV >>> oh)

divide :: (Core term, TyC a) => Word a -> term (a, a) a
divide w = div_mod w >>> oh

modulo :: (Core term, TyC a) => Word a -> term (a, a) a
modulo w = div_mod w >>> ih

divides :: (Core term, TyC a) => Word a -> term (a, a) Bit
divides w = ih &&& oh >>> modulo w >>> is_zero w

eeastep :: (Core term, TyC a) => Word a -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
eeastep w = (iih &&& oih >>> lt w) &&& iden
        >>> cond (step &&& ih) (oh &&& (ih &&& oh >>> step))
 where
  step = (oih &&& iih >>> div_mod w) &&& (ooh &&& ioh)
     >>> (((ooh &&& iioh) &&& (iooh &&& (unit >>> zero w)) >>> full_multiply w >>> ih)
      &&& ((ooh &&& iiih) &&& (ioih &&& (unit >>> zero w)) >>> full_multiply w >>> ih))
     &&& oih

eeastep_iterate :: forall term a b. (Core term, TyC a) => Word a -> Word b -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
eeastep_iterate w = go
 where
  go :: forall b. Word b -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
  go SingleV = base >>> base
   where
    base = eeastep w
  go (DoubleV d) = rec >>> rec
   where
    rec = go d

eea :: (Core term, TyC a) => Word a -> term (a, a) ((Either (a, a) (a, a), (a, a)), a)
eea w = pre >>> eeastep_iterate w w >>> post
 where
  o = (unit >>> one w)
  z = (unit >>> zero w)
  pre = ((o &&& z) &&& oh) &&& ((z &&& o) &&& ih)
  post = drop (drop (is_zero w)) &&& iden
     >>> cond ((injl ooh &&& ioh) &&& oih)
              ((injr ioh &&& ooh) &&& iih)

bezout :: (Core term, TyC a) => Word a -> term (a, a) (Either (a, a) (a, a))
bezout w = eea w >>> ooh

cofactors :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
cofactors w = eea w >>> take (drop (ih &&& oh))

gcd :: (Core term, TyC a) => Word a -> term (a, a) a
gcd w = eea w >>> ih

lcm :: (Core term, TyC a) => Word a -> term (a, a) (a,a)
lcm w = (cofactors w >>> oh) &&& ih >>> multiply w

absolute_value :: (Core term, TyC a) => Word a -> term a a
absolute_value w = msb w &&& iden
               >>> cond (negate w >>> ih) iden

sign :: (Core term, TyC a) => Word a -> term a Word2
sign w = msb w &&& some w
