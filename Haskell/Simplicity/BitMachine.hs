{-# LANGUAGE DeriveTraversable #-}
module Simplicity.BitMachine
 ( Cell
 , MachineCodeF(..), MachineCode
 , end, crash, write, copy, skip, fwd, bwd, newFrame, moveFrame, dropFrame, read
 , bump, nop
 ) where

import Prelude hiding (read)
import Data.Functor.Fixedpoint (Fix(..), cata)

import Simplicity.Ty

type Cell = Maybe Bool

data MachineCodeF a = End
                    | Crash
                    | Write Bool a
                    | Copy Int a
                    | Skip Int a
                    | Fwd Int a
                    | Bwd Int a
                    | NewFrame Int a
                    | MoveFrame a
                    | DropFrame a
                    | Read a a
                    deriving (Functor, Show)

type MachineCode = Fix MachineCodeF

end = Fix End
crash = Fix Crash
write b x = Fix (Write b x)
copy i x = Fix (Copy i x)
skip i x = Fix (Skip i x)
fwd i x = Fix (Fwd i x)
bwd i x = Fix (Bwd i x)
newFrame i x = Fix (NewFrame i x)
moveFrame x = Fix (MoveFrame x)
dropFrame x = Fix (DropFrame x)
read x y = Fix (Read x y)

bump i f = fwd i . f . bwd i

nop :: MachineCode -> MachineCode
nop x = x
