{-# LANGUAGE ScopedTypeVariables #-}
module Simplicity.Programs.Secp256k1 where

import Prelude hiding (drop, take, and, or, not, sqrt)

import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import Simplicity.Programs.Sha256
import Simplicity.Ty
import Simplicity.Term

feOrder :: Integer
feOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

scalarOrder :: Integer
scalarOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

scribe8 :: forall term a. (Core term, TyC a) => Integer -> term a Word8
scribe8 = scribe . toWord8

add32 :: forall term. Core term => term (Word32, Word32) Word32
add32 = adder word32 >>> ih

sub32 :: forall term. Core term => term (Word32, Word32) Word32
sub32 = subtractor word32 >>> ih

mul32 :: forall term. Core term => term (Word32, Word32) Word32
mul32 = multiplier word32 >>> ih

scribe32 :: forall term a. (Core term, TyC a) => Integer -> term a Word32
scribe32 = scribe . toWord32

add64 :: forall term. Core term => term (Word64, Word64) Word64
add64 = adder word64 >>> ih

mul64 :: forall term. Core term => term (Word64, Word64) Word64
mul64 = multiplier word64 >>> ih

scribe64 :: forall term a. (Core term, TyC a) => Integer -> term a Word64
scribe64 = scribe . toWord64

wideMul32 :: forall term. Core term => term (Word32, Word32) Word64
wideMul32 = multiplier word32

sub256 :: forall term. Core term => term (Word256, Word256) Word256
sub256 = subtractor word256 >>> ih

mod26 :: forall term. Core term => term Word32 Word32
mod26 = take ((zero word4 &&& (zero word2 &&& oiih)) &&& ih) &&& ih

mod22 :: forall term. Core term => term Word32 Word32
mod22 = (zero word8 &&& take (drop ((zero word2 &&& oih) &&& ih))) &&& ih

shift26 :: forall term. Core term => term Word32 Word32
shift26 = shift word32 26

shift22 :: forall term. Core term => term Word32 Word32
shift22 = shift word32 22

type X9 x = (x, (x, (x, (x, (x, (x, (x, (x, x))))))))
type X10 x = (x, X9 x)
type FE = X10 Word32

at :: forall term x a. (Core term, TyC x, TyC a) => term x a -> Integer -> term (X10 x) a
at k 0 = take k
at k 1 = drop . take $ k
at k 2 = drop . drop . take $ k
at k 3 = drop . drop . drop . take $ k
at k 4 = drop . drop . drop . drop . take $ k
at k 5 = drop . drop . drop . drop . drop . take $ k
at k 6 = drop . drop . drop . drop . drop . drop . take $ k
at k 7 = drop . drop . drop . drop . drop . drop . drop . take $ k
at k 8 = drop . drop . drop . drop . drop . drop . drop . drop . take $ k
at k 9 = drop . drop . drop . drop . drop . drop . drop . drop . drop $ k

reduce :: forall term. Core term => term (Word32, FE) FE
reduce = ((ioh &&& ((oh &&& scribe32 0x3D1) >>> mul32) >>> add32)
     &&& ((iioh &&& (take (shift word32 (-6))) >>> add32)
     &&& iiih))
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
     >>> ((take mod26) &&& ((drop mod22) &&& (take shift26) >>> add32))
         ))))))))))))))))

normalizeWeak :: forall term. Core term => term FE FE
normalizeWeak = (shift22 `at` 9) &&& iden >>> reduce

normalize :: forall term. Core term => term FE FE
normalize = normalizeWeak >>> more &&& iden
        >>> cond (scribe32 1 &&& iden >>> reduce >>> modAt9) iden
 where
  more = or (bit22 `at` 9)
      (and (scribe32 0x3FFFFFF &&& (scribe32 0x40 &&& (ioh &&& (scribe32 0x3D1 &&& oh >>> add32 >>> shift26) >>> add32) >>> add32) >>> subtractor word32 >>> oh)
           (drop (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                 (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                            (scribe32 0x03FFFFF &&& ih >>> eq)))))))))))))))))
  bit22 = take (drop ooih)
  modAt9 =       oh &&& drop (oh &&& drop (oh &&& drop (oh &&& drop (oh
       &&& drop (oh &&& drop (oh &&& drop (oh &&& drop (oh &&& drop mod22))))))))

fePack :: forall term. Core term => term FE Word256
fePack = drop (drop (drop (drop (drop (drop (drop (drop w7 &&& w6))) &&& (drop (drop w5) &&& w4)))))
     &&& (drop (drop (drop w3 &&& w2)) &&& (drop w1 &&& w0))
 where
  w0 = ((drop (take (drop (drop (oih &&& ioh)))) &&& (drop (take (drop iiih)) &&& take (take oiih))) &&& ooih) &&& oih
  w1 = (drop (take (drop (oih &&& ioh))) &&& (drop (take iiih) &&& take (take (oiih &&& iooh)))) &&& take ((take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh) ) &&& drop (take (oih &&& ioh) &&& (oiih &&& iooh)))
  w2 = drop (take (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& (((drop (take (drop iiih)) &&& take (take oiih)) &&& take oioh) &&& take (oiih &&& iooh))
  w3 = drop (take (oih &&& ioh)) &&& (drop (take iih) &&& take (take ((oiih &&& iooh) &&& drop (oih &&& ioh))))
  w4 = drop ((drop (take iiih) &&& take (take (oiih &&& iooh))) &&& take (take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh))) &&& (drop (take (drop (take (oih &&& ioh) &&& (oiih &&& iooh)))) &&& (drop (take (drop (drop (oih &&& ioh)))) &&& (drop (take (drop iiih)) &&& take (take oiih))))
  w5 = (drop (take (drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& ((drop (take (drop iiih)) &&& take (take oiih)) &&& take oioh)) &&& take ((oiih &&& iooh) &&& drop (oih &&& ioh))
  w6 = drop (take ih) &&& take (take ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))))
  w7 = drop ((take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh)) &&& drop (take (oih &&& ioh) &&& (oiih &&& iooh))) &&& ((drop (drop (drop (oih &&& ioh))) &&& (drop (drop iiih) &&& take (take oiih))) &&& take oih)

feUnpack :: forall term. Core term => term Word256 FE
feUnpack = drop (drop (drop (take ((zero word4 &&& (zero word2 &&& oiih)) &&& ih) &&& ih)))
       &&& drop (drop (take ((zero word4 &&& (zero word2 &&& take (drop ioh))) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))) &&& (take (drop ((oiih &&& iooh) &&& drop (oih &&& ioh))) &&& ((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))))))
       &&& drop (take (drop (drop ((zero word4 &&& (zero word2 &&& ooih)) &&& (oih &&& ioh)))) &&& ((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))))
       &&& drop (take (((zero word4 &&& (zero word2 &&& take (drop iooh))) &&& (take (drop (drop (oih &&& ioh))) &&& (take (drop iiih) &&& drop (take oooh)))) &&& drop ((take (take (oih &&& ioh) &&& (oiih &&& iooh))) &&& (take (ioih &&& iioh) &&& (take iiih &&& drop oooh)))))
       &&& (((zero word4 &&& (zero word2 &&& take (drop (drop (drop iiih))))) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh))))
       &&& take ((drop (drop (take ((zero word4 &&& (zero word2 &&& oioh)) &&& ((oiih &&& iooh) &&& drop (oih &&& ioh))) &&& (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh))))))
        &&& drop (take ((zero word4 &&& (zero word2 &&& take ioih)) &&& (oiih &&& iooh)) &&& (take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh)))
        &&& (take (drop (drop ((zero word4 &&& (zero word2 &&& oooh)) &&& (take (oih &&& ioh) &&& (oiih &&& iooh))))) &&& ((take (drop (drop (drop (oih &&& ioh)))) &&& (take (drop (drop iiih)) &&& drop (take (take oooh)))) &&& drop (take (take (take (oih &&& ioh) &&& (oiih &&& iooh))))))
        &&& take ((((zero word4 &&& (zero word2 &&& take (drop oiih))) &&& oiih) &&& ioh)
         &&& take (take (take (zero word8 &&& ((zero word2 &&& ooh) &&& (oih &&& ioh)))) &&& (take ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))))))

feZero :: forall term a. (Core term, TyC a) => term a FE
feZero = z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z
 where
  z = zero word32

feOne :: forall term a. (Core term, TyC a) => term a FE
feOne = scribe32 1 &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z
 where
  z = zero word32

feSeven :: forall term a. (Core term, TyC a) => term a FE
feSeven = scribe32 7 &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z
 where
  z = zero word32

bigZero :: forall term. Core term => term FE FE
bigZero = scribe32 0x3FFFC2F
      &&& scribe32 0x3FFFFBF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe3FFFFFF
      &&& scribe32 0x03FFFFF
 where
  scribe3FFFFFF = scribe32 0x3FFFFFF

feIsZero :: forall term. Core term => term FE Bit
feIsZero = normalizeWeak >>> or (feZero &&& iden >>> eq) (bigZero &&& iden >>> eq)

pointWise :: forall term. Core term => term (Word32, Word32) Word32 -> term (FE,FE) FE
pointWise k = ((take (iden `at` 0) &&& drop (iden `at` 0)) >>> k)
          &&& ((take (iden `at` 1) &&& drop (iden `at` 1)) >>> k)
          &&& ((take (iden `at` 2) &&& drop (iden `at` 2)) >>> k)
          &&& ((take (iden `at` 3) &&& drop (iden `at` 3)) >>> k)
          &&& ((take (iden `at` 4) &&& drop (iden `at` 4)) >>> k)
          &&& ((take (iden `at` 5) &&& drop (iden `at` 5)) >>> k)
          &&& ((take (iden `at` 6) &&& drop (iden `at` 6)) >>> k)
          &&& ((take (iden `at` 7) &&& drop (iden `at` 7)) >>> k)
          &&& ((take (iden `at` 8) &&& drop (iden `at` 8)) >>> k)
          &&& ((take (iden `at` 9) &&& drop (iden `at` 9)) >>> k)

add :: forall term. Core term => term (FE,FE) FE
add = pointWise add32

mulInt :: forall term. Core term => Integer -> term FE FE
mulInt x = take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop
         ( take scale &&& drop scale
         ))))))))
 where
  scale = iden &&& scribe32 x >>> mul32

neg :: forall term. Core term => Integer -> term FE FE
neg x = (bigZero >>> mulInt (2*(x+1))) &&& iden >>> pointWise sub32

sum19 :: forall term. Core term => term (X9 Word64, X10 Word64) FE
sum19 = (oh &&& iih) &&& (drop (take (shift26' &&& mod26')))
    >>> take (oih &&& iih) &&& (((oioh &&& ioh >>> add64) &&& oooh >>> circut) &&& iih)
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& (drop oiih &&& iih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
    >>> ((oih &&& iooh >>> add64) &&& (ooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih)
    >>> take (take (shift word64 (-14))) &&& ((((scribe64 0x3D10 &&& ooh >>> mul64) &&& (oioh &&& (zero word32 &&& iih) >>> add64) >>> add64) >>> (shift word64 22 &&& drop mod22)) &&& (oiih &&& ioh))
    >>> (oh &&& iooh >>> add64) &&& (ioih &&& iih)
    >>> ((zero word32 &&& drop (iden `at` 9)) &&& (oh &&& scribe64 0x3D1 >>> mul64) >>> add64) &&& iden
    >>> take mod26' &&& ((take shift26' &&& (drop ((zero word32 &&& drop (iden `at` 8)) &&& (take (shift word64 (-6))) >>> add64)) >>> add64) &&& iih
                    >>> (take mod26' &&& (((take shift26' >>> ih) &&& drop (iden `at` 7) >>> add32) &&& drop rest)))
 where
  shift26' = shift word64 26
  mod26' = drop mod26
  circut = take shift26' &&& (take mod26' &&& ih >>> (oh &&& (ih &&& (scribe32 0x3D10 &&& oh >>> wideMul32) >>> add64)) >>> ((take shiftk1 &&& drop shift26' >>> add64) &&& drop mod26'))
  shiftk1 = (zero word32 &&& iden >>> shift word64 (-10))
  rest = iden `at` 6 &&& iden `at` 5 &&& iden `at` 4 &&& iden `at` 3 &&& iden `at` 2 &&& iden `at` 1 &&& iden `at` 0

mul :: forall term. Core term => term (FE,FE) FE
mul = (convlo 0 &&& convlo 1 &&& convlo 2 &&& convlo 3 &&& convlo 4 &&& convlo 5 &&& convlo 6 &&& convlo 7 &&& convlo 8)
  &&& (convhi 9 &&& convhi 10 &&& convhi 11 &&& convhi 12 &&& convhi 13 &&& convhi 14 &&& convhi 15 &&& convhi 16 &&& convhi 17 &&& convhi 18)
  >>> sum19
 where
  convlo i = mksum [larg j &&& rarg (i-j) >>> wideMul32|j<-[0..i]]
  convhi i = mksum [larg j &&& rarg (i-j) >>> wideMul32|j<-[i-9..9]]
  larg i = take (iden `at` i)
  rarg i = drop (iden `at` i)
  mksum = foldr1 (\t1 t2 -> t1 &&& t2 >>> add64)

sqr :: forall term. Core term => term FE FE
sqr = (convlo 0 &&& convlo 1 &&& convlo 2 &&& convlo 3 &&& convlo 4 &&& convlo 5 &&& convlo 6 &&& convlo 7 &&& convlo 8)
  &&& (convhi 9 &&& convhi 10 &&& convhi 11 &&& convhi 12 &&& convhi 13 &&& convhi 14 &&& convhi 15 &&& convhi 16 &&& convhi 17 &&& convhi 18)
  >>> sum19
 where
  convlo i = mksum $ [shift word32 (-1) `at` j &&& iden `at` (i-j) >>> wideMul32|j<-[0..(i-1) `div` 2]] ++ [iden `at` (i `div` 2) >>> iden &&& iden >>> wideMul32 | even i]
  convhi i = mksum $ [iden `at` j &&& shift word32 (-1) `at` (i-j) >>> wideMul32|j<-[(i+2) `div` 2..9]] ++ [iden `at` (i `div` 2) >>> iden &&& iden >>> wideMul32 | even i]
  mksum = foldr1 (\t1 t2 -> t1 &&& t2 >>> add64)

tower :: forall term. Core term => term FE (FE, FE)
tower = iden &&& (iden &&& sqr >>> mul)
    >>> ih &&& (oh &&& drop sqr >>> mul)
    >>> oh &&& ((ih &&& (oh &&& (drop (iden &&& (iden &&& (sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr >>> sqr) >>> mul) >>> sqr >>> sqr) >>> mul -- (x2,(x3,x11))
                      >>> iden &&& foldr1 (>>>) (replicate 11 sqr) >>> mul))                      -- (x2,(x3,x22))
             >>> ih &&& (oh &&& drop (iden &&& foldr1 (>>>) (replicate 22 sqr) >>> mul            -- (x2,(x22,(x3,x44)))
                                 >>> (iden &&& (iden &&& foldr1 (>>>) (replicate 44 sqr) >>> mul  -- (x2,(x22,(x3,(x44,x88))))
                                             >>> iden &&& foldr1 (>>>) (replicate 88 sqr) >>> mul -- (x2,(x22,(x3,(x44,x176))))
                                       >>> foldr1 (>>>) (replicate 44 sqr)) >>> mul)              -- (x2,(x22,(x3,x220)))
                                >>> sqr >>> sqr >>> sqr) >>> mul                                  -- (x2,(x22,x223))
                       >>> foldr1 (>>>) (replicate 23 sqr)) >>> mul                               -- (x2,t1)
             >>> foldr1 (>>>) (replicate 5 sqr))

inv :: forall term. Core term => term FE FE
inv = iden &&& tower
  >>> oh &&& (ioh &&& (oh &&& iih >>> mul >>> sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr) >>> mul

sqrt :: forall term. Core term => term FE (Either () FE)
sqrt = iden &&& tower
   >>> oh &&& drop ((oh &&& drop sqr >>> mul) >>> sqr >>> sqr)
   >>> (oh &&& drop (sqr >>> neg 1) >>> add >>> feIsZero) &&& ih
   >>> cond (injr iden) (injl unit)

isQuad :: forall term. Core term => term FE Bit
isQuad = sqrt &&& unit >>> match false true

type GE = (FE, FE)
type GEJ = (GE, FE)

inf :: forall term a. (Core term, TyC a) => term a GEJ
inf = (one &&& one) &&& feZero
 where
  one = feOne

isInf :: forall term. Core term => term GEJ Bit
isInf = drop feIsZero

double :: forall term. Core term => term GEJ GEJ
double = isInf &&& iden >>> cond inf body
 where
  body = (take (oh &&& (take sqr >>> mulInt 3) &&& (drop sqr >>> mulInt 2))
      >>> (((drop (take sqr)) &&& (iih &&& oh >>> mul)) &&& drop (oh &&& (drop sqr >>> mulInt 2)))
      >>> take (oh &&& (drop (mulInt 4) >>> neg 4) >>> add) &&& (drop (drop (neg 2)) &&& (ioh &&& take (take (neg 1) &&& drop (mulInt 6) >>> add) >>> mul) >>> add))
     &&& (oih &&& ih >>> mul >>> mulInt 2)

offsetPoint :: forall term. Core term => term (GEJ, GE) (FE, GEJ)
offsetPoint = take isInf &&& iden >>> cond (feZero &&& (drop (iden &&& feOne))) body
 where
  body = take (iden &&& take (take normalizeWeak &&& drop normalizeWeak)) &&& (ih &&& take (drop sqr))                                                           -- ((a,(u1,s1)),(b,z12))
     >>> ((take (drop (take (neg 1))) &&& drop (ooh &&& ih >>> mul) >>> add) &&& oioh)
     &&& ((take (drop (drop (neg 1))) &&& (ooih &&& drop (oih &&& ih >>> mul) >>> mul) >>> add) &&& take (iih &&& oh))                                           -- ((h,u1),(i,(s1,a)))
     >>> take (take feIsZero) &&& iden >>> cond (drop zeroH) nonZeroH
  zeroH = take feIsZero &&& ih >>> cond (take (mulInt 2) &&& drop double) (feZero &&& inf)
  nonZeroH = (ooh &&& (ooh &&& drop iiih >>> mul)) &&& ((take (take sqr) &&& oih) &&& (ioh &&& iioh))                                                            -- ((h,z),((h2,u1),(i s1)))
         >>> oh &&& (((ooh &&& iooh >>> mul) &&& drop (take mul)) &&& iih)                                                                                       -- ((h,z),((h3,t),(i,s1)))
         >>> oh &&& drop (((take (oh &&& drop (mulInt 2) >>> add >>> neg 3) &&& drop (take sqr) >>> add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> mul >>> neg 1))) -- ((h,z),((x,t),(i,(-h3*s1))))
         >>> ooh &&& (drop (ooh &&& (iih &&& (ioh &&& (oih &&& take (take (neg 5)) >>> add) >>> mul) >>> add)) &&& oih)                                          -- (h,((x,y),z))

offsetPointZinv :: forall term. Core term => term (GEJ, (GE, FE)) GEJ
offsetPointZinv = take isInf &&& iden >>> cond (drop (infCase &&& feOne)) body
 where
  infCase = iden &&& drop sqr
        >>> (oooh &&& ih >>> mul) &&& (ooih &&& (oih &&& ih >>> mul) >>> mul)
  body = take (iden &&& take (take normalizeWeak &&& drop normalizeWeak)) &&& (ioh &&& (iih &&& oih >>> mul >>> iden &&& sqr))                                   -- ((a,(u1,s1)),(b,(az,z12)))
     >>> ((take (drop (take (neg 1))) &&& drop (ooh &&& iih >>> mul) >>> add) &&& oioh)
     &&& ((take (drop (drop (neg 1))) &&& drop (ioh &&& (oih &&& iih >>> mul) >>> mul) >>> add) &&& take (iih &&& oh))                                           -- ((h,u1),(i,(s1,a)))
     >>> take (take feIsZero) &&& iden >>> cond (drop zeroH) nonZeroH
  zeroH = take feIsZero &&& ih >>> cond (drop double) inf
  nonZeroH = (ooh &&& (ooh &&& drop iiih >>> mul)) &&& ((take (take sqr) &&& oih) &&& (ioh &&& iioh))                                                            -- ((h,z),((h2,u1),(i s1)))
         >>> oih &&& (((ooh &&& iooh >>> mul) &&& drop (take mul)) &&& iih)                                                                                      -- (z,((h3,t),(i,s1)))
         >>> oh &&& drop (((take (oh &&& drop (mulInt 2) >>> add >>> neg 3) &&& drop (take sqr) >>> add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> mul >>> neg 1))) -- (z,((x,t),(i,(-h3*s1))))
         >>> drop (ooh &&& (iih &&& (ioh &&& (oih &&& take (take (neg 5)) >>> add) >>> mul) >>> add)) &&& oh                                                     -- ((x,y),z)

geNegate :: forall term. Core term => term GE GE
geNegate = oh &&& drop (normalizeWeak >>> neg 1)

normalizePoint :: forall term. Core term => term GEJ GE
normalizePoint = oh &&& (ih >>> inv >>> (sqr &&& iden))
             >>> (ooh &&& ioh >>> mul >>> normalize) &&& (oih &&& (ioh &&& iih >>> mul) >>> mul >>> normalize)

eqXCoord :: forall term. Core term => term (FE, GEJ) Bit
eqXCoord = drop (take (take normalizeWeak)) &&& (drop (drop sqr) &&& oh >>> mul >>> neg 1)
       >>> add >>> feIsZero

hasQuadY :: forall term. Core term => term GEJ Bit
hasQuadY = and (not isInf) (oih &&& ih >>> mul >>> isQuad)

type Vector2 x = (x,x)
type Vector4 x = Vector2 (Vector2 x)
type Vector8 x = Vector2 (Vector4 x)
type Vector16 x = Vector2 (Vector8 x)
type Vector32 x = Vector2 (Vector16 x)
type Vector256 x = Vector8 (Vector32 x)

scalarTable5 :: forall term. Core term => term GEJ (FE, Vector8 GE)
scalarTable5 = iden &&& double
           >>> iih &&& (((ooh &&& iih >>> scaleZ) &&& oih) &&& ioh) -- (dz, (a', (dx,dy)))
           >>> oh &&& drop pass1
           >>> (oh &&& drop oiih >>> mul) &&& drop (pass2
               >>> (drop (drop (drop (drop (drop (drop (ih &&& oh)) &&& (ioh &&& oh)))))) &&&
                   ((drop (drop (ioh &&& oh))) &&& (ioh &&& oh)))
 where
  scaleZ = oh &&& (ih &&& (ih >>> sqr) >>> ih &&& mul) >>> (ooh &&& ioh >>> mul) &&& (oih &&& iih >>> mul)
  pass1 = (offsetPoint &&& oh) &&& ih
      >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
      >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
      >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
      >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
      >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
      >>> (ooih &&& ih >>> offsetPoint) &&& oh
  pass2 = (ooh &&& oioh) &&& ih >>> (oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
      >>> oh &&& drop (oih &&& (ioh &&& ooh >>> scaleZ)))))))

lookupTable5 :: forall term. Core term => term (Word4, Vector8 GE) GE
lookupTable5 = oooh &&& ooih &&& oih &&& ih
           >>> cond neg pos
 where
  pos = ioih &&& (iooh &&& (oh &&& iih >>> cond ih oh) >>> cond ih oh) >>> cond ih oh
  neg = ioih &&& (iooh &&& (oh &&& iih >>> cond oh ih) >>> cond oh ih) >>> cond (take geNegate) (drop geNegate)

type Wnaf5State = (Either Word2 (), Bit) -- state consists of a counter for skiping upto for places and a bit indicating the current carry bit.
type Wnaf5Env b = (b, Vector4 b) -- the environment consists of the current bit in the scalar being considered and the following 4 bits afterwards (zero padded).

wnaf5step16 :: forall term. Core term => term (Wnaf5State, Wnaf5Env Word16) (Wnaf5State, Vector16 (Either () Word4))
wnaf5step16 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step8) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
          >>> oih &&& (ooh &&& ih >>> wnaf5step8)
          >>> ioh &&& (oh &&& iih)
 where
  wnaf5step = ooh &&& (oih &&& ih)
          >>> match (count &&& injl unit) (drop body)
   where
    count = ooh &&& (oih &&& ioh)
        >>> cond (cond (injl (true  &&& false) &&& iden) (injl (false &&& true) &&& iden))
                 (cond (injl (false &&& false) &&& iden) (injr unit             &&& iden))
    body = ((oh &&& ioh >>> eq) &&& (oh &&& iih))
       >>> cond ((injr unit &&& oh) &&& injl unit)
                ((injl (true &&& true) &&& iooh) &&& (injr ih))
  wnaf5step2 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
           >>> oih &&& (ooh &&& ih >>> wnaf5step)
           >>> ioh &&& (oh &&& iih)
  wnaf5step4 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step2) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
           >>> oih &&& (ooh &&& ih >>> wnaf5step2)
           >>> ioh &&& (oh &&& iih)
  wnaf5step8 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step4) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
           >>> oih &&& (ooh &&& ih >>> wnaf5step4)
           >>> ioh &&& (oh &&& iih)

-- TODO: share code between wnaf5, wnaf5Short and wnaf16?
wnaf5 :: forall term. Core term => term Word256 (Vector256 (Either () Word4))
wnaf5 = (take . take . take . take . take $ oooh) &&& iden
    >>> cond (true &&& (scribe (toWord256 scalarOrder) &&& iden >>> sub256) >>> go)
             (false &&& iden >>> go)
 where
  -- a variant of shift that pulls in leading ones could be useful here instead of using bitwiseNot.
  go = (injr unit &&& oh) &&& (oh &&& drop (iden &&& ((shift word256 4 &&& shift word256 3) &&& (shift word256 2 &&& shift word256 1)))
                           >>> cond (take (bitwiseNot word256) &&& drop (bitwiseNot (DoubleW (DoubleW word256)))) iden)
   >>> wnaf5step256 >>> ih
  wnaf5step32 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step16) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
            >>> oih &&& (ooh &&& ih >>> wnaf5step16)
            >>> ioh &&& (oh &&& iih)
  wnaf5step64 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step32) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
            >>> oih &&& (ooh &&& ih >>> wnaf5step32)
            >>> ioh &&& (oh &&& iih)
  wnaf5step128 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step64) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
             >>> oih &&& (ooh &&& ih >>> wnaf5step64)
             >>> ioh &&& (oh &&& iih)
  wnaf5step256 = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> wnaf5step128) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
             >>> oih &&& (ooh &&& ih >>> wnaf5step128)
             >>> ioh &&& (oh &&& iih)

wnaf5Short :: forall term. Core term => term Word16 (Vector16 (Either () Word4))
wnaf5Short = false &&& iden >>> go
 where
  go = (injr unit &&& oh) &&& (oh &&& drop (iden &&& ((shift word16 4 &&& shift word16 3) &&& (shift word16 2 &&& shift word16 1)))
                           >>> cond (take (bitwiseNot word16) &&& drop (bitwiseNot (DoubleW (DoubleW word16)))) iden)
   >>> wnaf5step16 >>> ih

wnaf16 :: forall term. Core term => term Word256 (Vector256 (Either () Word16))
wnaf16 = (take . take . take . take . take $ oooh) &&& iden
    >>> cond (true &&& (scribe (toWord256 scalarOrder) &&& iden >>> sub256) >>> go)
             (false &&& iden >>> go)
 where
  -- a variant of shift that pulls in leading ones could be useful here instead of using bitwiseNot.
  go = (injr unit &&& oh) &&& (oh &&& drop shifts
                           >>> cond (bitwiseNot (DoubleW (DoubleW (DoubleW (DoubleW word256))))) iden)
   >>> wnaf16step256 >>> ih
  shifts = (((shift word256 15 &&& shift word256 14) &&& (shift word256 13 &&& shift word256 12)) &&& ((shift word256 11 &&& shift word256 10) &&& (shift word256 9 &&& shift word256 8)))
       &&& (((shift word256 7 &&& shift word256 6) &&& (shift word256 5 &&& shift word256 4)) &&& ((shift word256 3 &&& shift word256 2) &&& (shift word256 1 &&& iden)))
  wnaf16step = ooh &&& (oih &&& ih)
           >>> match (count &&& injl unit) (drop body)
   where
    count = (zero word4 &&& oh >>> eq) &&& (oh &&& ioh)
        >>> cond (injr unit &&& ih) (injl ((oh &&& zero word4) &&& true >>> fullSubtractor word4 >>> ih) &&& ih)
    body = ((oh &&& drop (drop iiih) >>> eq) &&& iden)
       >>> cond ((injr unit &&& oh) &&& injl unit)
                ((injl (scribe (toWord word4 14)) &&& drop (take oooh)) &&& (injr (drop setLowBit)))
    setLowBit = oh &&& drop (oh &&& drop (oh &&& drop (oh &&& true)))
  wnaf16step2 = (oh &&& drop dropV16 >>> wnaf16step) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step4 = (oh &&& drop dropV16 >>> wnaf16step2) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step2)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step8 = (oh &&& drop dropV16 >>> wnaf16step4) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step4)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step16 = (oh &&& drop dropV16 >>> wnaf16step8) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step8)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step32 = (oh &&& drop dropV16 >>> wnaf16step16) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step16)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step64 = (oh &&& drop dropV16 >>> wnaf16step32) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step32)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step128 = (oh &&& drop dropV16 >>> wnaf16step64) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step64)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8
  wnaf16step256 = (oh &&& drop dropV16 >>> wnaf16step128) &&& drop takeV16
            >>> oih &&& (ooh &&& ih >>> wnaf16step128)
            >>> ioh &&& (oh &&& iih)
   where
    takeV2 = ooh &&& ioh
    takeV4 = take takeV2 &&& drop takeV2
    takeV8 = take takeV4 &&& drop takeV4
    takeV16 = take takeV8 &&& drop takeV8
    dropV2 = oih &&& iih
    dropV4 = take dropV2 &&& drop dropV2
    dropV8 = take dropV4 &&& drop dropV4
    dropV16 = take dropV8 &&& drop dropV8

generatorSmall :: forall term. Core term => term Word16 GE
generatorSmall = signAbs
         >>> oh &&& drop (wnaf5Short &&& (scribe g >>> scalarTable5) -- TODO directly scribe the scalarTable5 for g.
                      >>> ioh &&& (oh &&& inf &&& iih >>> step16)
                      >>> ioh &&& (oh &&& iih >>> mul)
                      >>> normalizePoint)
         >>> cond (oh &&& drop (neg 1)) iden
 where
  signAbs = take oooh &&& iden
        >>> cond (true &&& negator) (false &&& iden)
  g = (((toWord32 49813400, (toWord32 10507973, (toWord32 42833311, (toWord32 57456440, (toWord32 50502652
        ,(toWord32 60932801, (toWord32 33958236, (toWord32 49197398, (toWord32 41875932, toWord32 1994649)))))))))
       ,(toWord32 51434680, (toWord32 32777214, (toWord32 21076420, (toWord32 19044885, (toWord32 16586676
        ,(toWord32 58999338, (toWord32 38780864, (toWord32 51484022, (toWord32 41363107, toWord32 1183414))))))))))
      ,(toWord32 1, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, toWord32 0))))))))))
  step = match (drop (take double))
               (drop (take double) &&& (oh &&& iih >>> lookupTable5) >>> offsetPoint >>> ih)
  step2 = ooh &&& (oih &&& ih >>> step) &&& iih >>> step
  step4 = ooh &&& (oih &&& ih >>> step2) &&& iih >>> step2
  step8 = ooh &&& (oih &&& ih >>> step4) &&& iih >>> step4
  step16 = ooh &&& (oih &&& ih >>> step8) &&& iih >>> step8
  negator = zero word16 &&& iden >>> subtractor word16 >>> ih

generator :: forall term. Core term => term Word256 GEJ
generator = wnaf16 &&& inf >>> step256
 where
  step = match (drop double) (drop double &&& take generatorSmall &&& feOne >>> offsetPointZinv)
  step2 = ooh &&& (oih &&& ih >>> step) >>> step
  step4 = ooh &&& (oih &&& ih >>> step2) >>> step2
  step8 = ooh &&& (oih &&& ih >>> step4) >>> step4
  step16 = ooh &&& (oih &&& ih >>> step8) >>> step8
  step32 = ooh &&& (oih &&& ih >>> step16) >>> step16
  step64 = ooh &&& (oih &&& ih >>> step32) >>> step32
  step128 = ooh &&& (oih &&& ih >>> step64) >>> step64
  step256 = ooh &&& (oih &&& ih >>> step128) >>> step128

ecMult :: forall term. Core term => term ((GEJ, Word256), Word256) GEJ
ecMult = (scribe (toWord256 0) &&& oih >>> eq) &&& iden
     >>> cond (drop (feOne &&& generator)) body
     >>> ioh &&& (oh &&& iih >>> mul)
 where
  body = inf &&& (ooh >>> scalarTable5) &&& (oih >>> wnaf5) &&& (ih >>> wnaf16)
         >>> iooh &&& step256
  step = iiih &&& (iioh &&& take double &&& ioih >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5) >>> offsetPoint >>> ih)) &&& iooh
     >>> match ioh (ioh &&& take generatorSmall &&& iih >>> offsetPointZinv)
  step2 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step) &&& drop (oh &&& iooh &&& iioh) >>> step
  step4 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step2) &&& drop (oh &&& iooh &&& iioh) >>> step2
  step8 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step4) &&& drop (oh &&& iooh &&& iioh) >>> step4
  step16 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step8) &&& drop (oh &&& iooh &&& iioh) >>> step8
  step32 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step16) &&& drop (oh &&& iooh &&& iioh) >>> step16
  step64 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step32) &&& drop (oh &&& iooh &&& iioh) >>> step32
  step128 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step64) &&& drop (oh &&& iooh &&& iioh) >>> step64
  step256 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step128) &&& drop (oh &&& iooh &&& iioh) >>> step128

type PubKey = (Bit, Word256)
type Sig = (Word256, Word256)

pkPoint :: forall term. Core term => term PubKey (Either () GEJ)
pkPoint = (ih &&& scribe (toWord256 feOrder) >>> lt) &&& (drop feUnpack &&& oh)
      >>> cond k1 (injl unit)
 where
  k1 = take (feSeven &&& (iden &&& sqr >>> mul) >>> add >>> sqrt) &&& iden
   >>> match (injl unit) (injr k2)
  k2 = (ioh &&& (take normalize &&& iih >>> (take (take (drop (drop iiih))) &&& ih >>> eq) &&& oh >>> cond iden (neg 1))) &&& feOne
  lt = subtractor word256 >>> oh

sigUnpack :: forall term. Core term => term Sig (Either () (FE, Word256))
sigUnpack = and (oh &&& scribe (toWord256 feOrder) >>> lt)
                (ih &&& scribe (toWord256 scalarOrder) >>> lt)
        &&& (take feUnpack &&& ih)
        >>> cond (injr iden) (injl unit)
 where
  lt = subtractor word256 >>> oh

scalarUnrepr :: forall term. Core term => term Word256 Word256
scalarUnrepr = (iden &&& scribe (toWord256 scalarOrder) >>> subtractor word256) &&& iden
           >>> ooh &&& (oih &&& ih)
           >>> cond ih oh

schnorrVerify :: forall term. Core term => term ((PubKey, Word256), Sig) Bit
schnorrVerify = drop sigUnpack &&& (take (take pkPoint) &&& nege)
      >>> match false k1
 where
  k1 = ioh &&& (iih &&& oh)
   >>> match false k2
  k2 = iioh &&& ((oh &&& ioh) &&& iiih >>> ecMult)
   >>> and eqXCoord (drop hasQuadY)
  nege = (scribe (toWord256 scalarOrder) &&& (h >>> scalarUnrepr) >>> sub256)
  h = m >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock
  m = (ioh
     &&& take (take (((((y &&& drop (take (take oooh))) &&& drop (take (take (take (oih &&& ioh))))) &&& drop (take (take ((oiih &&& iooh) &&& drop (oih &&& ioh))))) &&& drop (take (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh))))) &&& drop ((((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))) &&& drop (take ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& drop (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))))))
    &&& take ((((((take (drop (drop (drop iiih))) &&& drop (take (take oooh))) &&& drop (take (take (take (oih &&& ioh))))) &&& drop (take (take ((oiih &&& iooh) &&& drop (oih &&& ioh))))) &&& drop (take (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh))))) &&& drop ((((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))) &&& drop (take ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& drop (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))))
    &&& (((((drop (drop (drop iiih)) &&& scribe8 0x80) &&& zero word16) &&& zero word32) &&& zero word64) &&& scribe (toWord128 (256+8+256+256))))
  y = cond (scribe8 3) (scribe8 2)

schnorrAssert :: forall term. Assert term => term ((PubKey, Word256), Sig) ()
schnorrAssert = assert schnorrVerify
