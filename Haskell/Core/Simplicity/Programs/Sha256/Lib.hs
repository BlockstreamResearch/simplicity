{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Sha256.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Sha256.lib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.Sha256.Lib
 (
 -- * Operations
   Sha256.Block, Sha256.Hash, Sha256.Ctx8
 , iv, hashBlock
 , ctx8Init
 , ctx8Add1
 , ctx8Addn
 , ctx8AddBuffer
 , ctx8Add2
 , ctx8Add4
 , ctx8Add8
 , ctx8Add16
 , ctx8Add32
 , ctx8Add64
 , ctx8Add128
 , ctx8Add256
 , ctx8Add512
 , ctx8AddBuffer511
 , ctx8Finalize
 ) where

import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Ty.Word

iv = Sha256.iv Sha256.lib
hashBlock = Sha256.hashBlock Sha256.lib
ctx8Init = Sha256.ctx8Init Sha256.lib
ctx8Add1 = Sha256.ctx8Add1 Sha256.libAssert
ctx8Addn = Sha256.ctx8Addn Sha256.libAssert
ctx8AddBuffer = Sha256.ctx8AddBuffer Sha256.libAssert
ctx8Add2 = ctx8Addn vector2
ctx8Add4 = ctx8Addn vector4
ctx8Add8 = ctx8Addn vector8
ctx8Add16 = ctx8Addn vector16
ctx8Add32 = ctx8Addn vector32
ctx8Add64 = ctx8Addn vector64
ctx8Add128 = ctx8Addn vector128
ctx8Add256 = ctx8Addn vector256
ctx8Add512 = ctx8Addn vector512
ctx8AddBuffer511 = ctx8AddBuffer buffer511
ctx8Finalize = Sha256.ctx8Finalize Sha256.libAssert
