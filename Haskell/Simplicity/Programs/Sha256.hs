{-# LANGUAGE ScopedTypeVariables #-}
module Simplicity.Programs.Sha256
 ( Block, Hash
 , iv, hashBlock
 ) where

import Prelude hiding (Word, drop, not, take)

import Simplicity.Arith
import Simplicity.Bit
import Simplicity.Generic
import Simplicity.Term

type Block = (Word256, Word256)
type Hash = Word256

iv :: (Core term, TyC a) => term a Hash
iv = scribe . toWord256 $ 0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19

hashBlock :: forall term. Core term => term (Hash, Block) Hash
hashBlock = oh &&& compression >>>
            ((collate oooh &&& collate ooih)
        &&&  (collate oioh &&& collate oiih))
        &&& ((collate iooh &&& collate ioih)
        &&&  (collate iioh &&& collate iiih))
 where
  collate x = take x &&& drop x >>> add32
  compression = scribe32 k0 &&& iden >>> foldr (\k rec -> scribe32 k &&& step >>> rec) round ks
  k0:ks = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
          ,0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
          ,0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
          ,0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
          ,0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
          ,0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
          ,0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
          ,0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
  step = round &&& (drop (drop schedule))
  scribe32 :: TyC a => Integer -> term a Word32
  scribe32 = scribe . toWord32
  -- TODO: hand optimize round by lifting drops and takes.
  round = part1 >>> part2
   where
    part1 = ((t1 &&& io oooh) &&& (io ooih &&& io oioh))
        &&& ((io oiih &&& io iooh) &&& (io ioih &&& io iioh))
    part2 = ((t12 &&& ooih) &&& (oioh &&& oiih))
        &&& ((t1d &&& ioih) &&& (iioh &&& iiih))
    t1 = (oh &&& iio oooh >>> add32) &&& (io iiih &&& ((io iooh >>> bigSigma1) &&& (io iooh &&& io ioih &&& io iioh >>> chWord32) >>> add32) >>> add32) >>> add32
    t12 = oooh &&& ((ooih >>> bigSigma0) &&& (ooih &&& oioh &&& oiih >>> majWord32) >>> add32) >>> add32
    t1d = oooh &&& iooh >>> add32
    bigSigma0 = rotate word32 (-2) &&& rotate word32 (-13) &&& rotate word32 (-22) >>> xor3Word32
    bigSigma1 = rotate word32 (-6) &&& rotate word32 (-11) &&& rotate word32 (-25) >>> xor3Word32
    chWord32 = bitwiseTri ch word32
    majWord32 = bitwiseTri maj word32
  schedule = (take part1 &&& (take idiag &&& (take iiih &&& drop oooh)))
         &&& (drop part1 &&& (drop idiag &&& (drop iiih &&& smallSigma)))
   where
    part1 = take diag &&& (oiih &&& iooh)
    smallSigma = (take (oooh &&& (ooih >>> smallSigma0)) >>> add32) &&& (drop (ooih &&& (iioh >>> smallSigma1)) >>> add32) >>> add32
    smallSigma0 = rotate word32 (-7)  &&& rotate word32 (-18) &&& shift word32 (-3)  >>> xor3Word32
    smallSigma1 = rotate word32 (-17) &&& rotate word32 (-19) &&& shift word32 (-10) >>> xor3Word32
  io x = drop (take x)
  iio x = drop (io x)
  diag = oih &&& ioh
  idiag = drop diag
  add32 = adder word32 >>> ih
  xor3Word32 = bitwiseTri xor3 word32
