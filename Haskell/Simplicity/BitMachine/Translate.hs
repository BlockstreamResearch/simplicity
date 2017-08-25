module Simplicity.BitMachine.Translate
 ( Translation
 , compile
 ) where

import Prelude hiding (read)
import Data.Proxy (Proxy(..))

import Simplicity.BitMachine
import Simplicity.BitMachine.Ty
import Simplicity.Term

newtype Translation a b = Translation (MachineCode -> MachineCode)

compile :: Translation a b -> MachineCode
compile (Translation f) = f end

instance Core Translation where
  iden = result
   where
    a = reifyProxy result
    result = Translation
           $ copy (bitSizeR a)

  comp arrS@(Translation s) (Translation t) =
    Translation
    $ newFrame (bitSizeR b)
    . s
    . moveFrame
    . t
    . dropFrame
   where
    b = reifyProxy arrS

  unit = Translation id

  injl (Translation t) = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padLR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           $ write False
           . skip pad
           . t

  injr (Translation t) = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padRR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           $ write True
           . skip pad
           . t

  match arrS@(Translation s) arrT@(Translation t) =
    Translation $ \k ->
      read (bump padl s k) (bump padr t k)
   where
    proxy :: arr (a,b) d -> Proxy b
    proxy _ = Proxy
    b = reifyProxy (proxy arrS)
    c = reifyProxy (proxy arrT)
    padl = 1 + padLR b c
    padr = 1 + padRR b c

  pair (Translation s) (Translation t) =
   Translation $ s . t

  take (Translation t) = Translation t

  drop (Translation t) = result
   where
    proxyA :: arr (a, b) c -> Proxy a
    proxyA _ = Proxy
    bs = bitSizeR (reifyProxy (proxyA result))
    result = Translation
           $ bump bs t
