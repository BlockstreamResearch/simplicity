module Simplicity.BitMachine.Authentic
 ( State, StateTrans
 , runMachine
 , Stats(..)
 , instrumentMachine
 ) where

import Control.Monad ((>=>), guard, unless)
import Control.Monad.Fail (MonadFail)
import Control.Monad.Trans.Writer (WriterT, tell)
import Data.Functor.Fixedpoint (cata)
import Data.Vector ((//), (!?))
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import Lens.Family2 ((^.), to)

import Simplicity.BitMachine (Cell, MachineCodeF(..), MachineCode, Interpreter)

data Frame = Frame { fData :: !(V.Vector Cell)
                   , fOffset :: !Int
                   }

fInit cells = Frame (V.fromList cells) 0

fNew n | 0 <= n = Frame (V.replicate n Nothing) 0

fReset fm = unless (fOffset fm == length (fData fm)) (fail "fReset: offset not at end of frame")
         >> return (fm {fOffset = 0})

fRead fr = maybe (fail "fRead: offset out of range") return (fData fr !? fOffset fr)

fSlice n = to go
 where
  go (Frame dt os) | os + n <= V.length dt = return $ V.slice os n dt
                   | otherwise = fail "fSlice: slice too large"

fWrite v (Frame dt os) | os < V.length dt = return $ Frame dt' os'
                       | otherwise = fail "fWrite: data too large"
 where
  dt' = dt // [(os, v)]
  os' = os+1

fFill v (Frame dt os) | os + n <= V.length dt = return $ Frame dt' os'
 where
  n = V.length v
  dt' = V.modify go dt
   where
    go mv = V.copy (VM.slice os n mv) v
  os' = os + n

fMove n (Frame dt os) | 0 <= os' && os' <= length dt = return $ Frame dt os'
                      | otherwise = fail "fMove: index out of range"
 where
  os' = os+n

fSize (Frame dt _) = V.length dt

data Active = Active { activeReadFrame :: !Frame
                     , activeWriteFrame :: !Frame
                     }

rf f x = (\y -> x { activeReadFrame = y }) <$> f (activeReadFrame x)
wf f x = (\y -> x { activeWriteFrame = y }) <$> f (activeWriteFrame x)

data State = State { inactiveReadFrames :: [Frame]
                   , activeFrames :: !Active
                   , inactiveWriteFrames :: [Frame]
                   }
act f x = (\y -> x { activeFrames = y }) <$> f (activeFrames x)

type StateTrans m = State -> m State

crash :: MonadFail m => StateTrans m
crash = fail "explicit crash"

copy :: MonadFail m => Int -> StateTrans m
copy n st = do
  v <- st^.act.rf.fSlice n
  (act.wf) (fFill v) st

newFrame :: MonadFail m => Int -> StateTrans m
newFrame n (State irf (Active rf wf) iwf) = do
  unless (0 <= n) (fail "newFrame: negative size")
  return $ State irf (Active rf (fNew n)) (wf:iwf)

moveFrame :: MonadFail m => StateTrans m
moveFrame (State irf (Active rf wf) (iwf0:iwf)) = do
  nrf <- fReset wf
  return $ State (rf:irf) (Active nrf iwf0) iwf
moveFrame _ = fail "moveFrame: empty write frame stack"

dropFrame (State (irf0:irf) (Active _ wf) iwf) =
  return $ State irf (Active irf0 wf) iwf
dropFrame _ = fail "dropFrame: empty read frame stack"

runMachineF :: MonadFail m => MachineCodeF (StateTrans m) -> StateTrans m
runMachineF End = return
runMachineF Crash = crash
runMachineF (Write b k) = (act.wf) (fWrite (Just b)) >=> k
runMachineF (Copy n k) | 0 <= n = copy n >=> k
                       | otherwise = fail "runMachineF Copy: negative index"
runMachineF (Skip n k) | 0 <= n = (act.wf) (fMove n) >=> k
                       | otherwise = fail "runMachineF Skip: negative index"
runMachineF (Fwd n k) | 0 <= n = (act.rf) (fMove n) >=> k
                      | otherwise = fail "runMachineF Fwd: negative index"
runMachineF (Bwd n k) | 0 <= n = (act.rf) (fMove (-n)) >=> k
                      | otherwise = fail "runMachineF Bwd: negative index"
runMachineF (NewFrame n k) = newFrame n >=> k
runMachineF (MoveFrame k) = moveFrame >=> k
runMachineF (DropFrame k) = dropFrame >=> k
runMachineF (Read k0 k1) = \st -> do
  v <- fRead (st^.act.rf)
  b <- maybe (fail "runMachine Read: cell value undefined") return v
  if b then k1 st else k0 st

initialState :: [Cell] -> Int -> State
initialState input outLength = State [] (Active (fInit input) (fNew outLength)) []

finalState :: MonadFail m => State -> m [Cell]
finalState (State [] (Active _ output) []) = return $ V.toList (fData output)
finalState _ = fail "finalState: invalid final state"

runMachine :: MonadFail m => MachineCode -> Interpreter m
runMachine code input outputSize = cata runMachineF code (initialState input outputSize)
                               >>= finalState

actReadFrameSize :: State -> Int
actReadFrameSize st = fSize (st^.act.rf)

actWriteFrameSize :: State -> Int
actWriteFrameSize st = fSize (st^.act.wf)

inactReadFrameSizes :: State -> [Int]
inactReadFrameSizes st = fSize <$> inactiveReadFrames st

inactWriteFrameSizes :: State -> [Int]
inactWriteFrameSizes st = fSize <$> inactiveWriteFrames st

data Stats = Stats { memSize :: !Int
                   , stackSize :: !Int
                   } deriving Show

instance Monoid Stats where
  mempty = Stats { memSize = 0
                 , stackSize = 0
                 }
  a `mappend` b = Stats { memSize = max (memSize a) (memSize b)
                        , stackSize = max (stackSize a) (stackSize b)
                        }

profile :: State -> Stats
profile st = Stats { memSize = sum readStackStats + sum writeStackStats + actReadFrameSize st + actWriteFrameSize st
                   , stackSize = length readStackStats + length writeStackStats
                   }
 where
  readStackStats = inactReadFrameSizes st
  writeStackStats = inactWriteFrameSizes st

instrument st = tell (profile st) >> return st

instrumentMachine :: MonadFail m => MachineCode -> Interpreter (WriterT Stats m)
instrumentMachine code input outputSize = interpreter (initialState input outputSize)
                                      >>= finalState
 where
  interpreter = cata instrumentMachineF code >=> instrument
  instrumentMachineF f = instrument >=> runMachineF f
