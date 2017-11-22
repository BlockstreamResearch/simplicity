module Simplicity.BitMachine.Translate.TCO
 ( Translation
 , compile
 ) where

import Data.Proxy (Proxy(..))

import Simplicity.BitMachine
import Simplicity.BitMachine.Ty
import Simplicity.Term

data Translation a b = Translation { tcoOn :: MachineCodeK
                                   , tcoOff :: MachineCodeK
                                   }

compile :: Translation a b -> MachineCode
compile trans = tcoOff trans end

instance Core Translation where
  iden = result
   where
    a = reifyProxy result
    result = Translation
           { tcoOn  = copy (bitSizeR a)
                    . dropFrame
           , tcoOff = copy (bitSizeR a)
           }

  comp s t = Translation
    { tcoOn  = newFrame (bitSizeR b)
             . tcoOn s
             . moveFrame
             . tcoOn t
    , tcoOff = newFrame (bitSizeR b)
             . tcoOff s
             . moveFrame
             . tcoOn t
    }
   where
    b = reifyProxy s

  unit = Translation
       { tcoOn = dropFrame
       , tcoOff = nop
       }

  injl t = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padLR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           { tcoOn  = write False
                    . skip pad
                    . tcoOn t
           , tcoOff = write False
                    . skip pad
                    . tcoOff t
           }


  injr t = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padRR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           { tcoOn  = write True
                    . skip pad
                    . tcoOn t
           , tcoOff = write True
                    . skip pad
                    . tcoOff t
           }

  match s t = Translation
            { tcoOn  = (fwd padl . tcoOn s) ||| (fwd padr . tcoOn t)
            , tcoOff = bump padl (tcoOff s) ||| bump padr (tcoOff t)
            }
   where
    proxy :: arr (a,b) d -> Proxy b
    proxy _ = Proxy
    b = reifyProxy (proxy s)
    c = reifyProxy (proxy t)
    padl = 1 + padLR b c
    padr = 1 + padRR b c

  pair s t = Translation
           { tcoOn  = tcoOff s
                    . tcoOn t
           , tcoOff = tcoOff s
                    . tcoOff t
           }

  take t = Translation
         { tcoOn  = tcoOn t
         , tcoOff = tcoOff t
         }

  drop t = result
   where
    proxyA :: arr (a, b) c -> Proxy a
    proxyA _ = Proxy
    bs = bitSizeR (reifyProxy (proxyA result))
    result = Translation
           { tcoOn  = fwd bs
                    . tcoOn t
           , tcoOff = bump bs (tcoOff t)
           }
