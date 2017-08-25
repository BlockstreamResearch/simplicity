module Simplicity.BitMachine.Authentic
 ( State, StateTrans
 , runMachine
 ) where

import Control.Monad ((>=>), guard, join)
import Data.Functor.Fixedpoint (cata)
import Data.Vector ((//), (!?))
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import Lens.Family2 ((^.), to)

import Simplicity.BitMachine (Cell, MachineCodeF(..), MachineCode)

data Frame = Frame { fData :: !(V.Vector Cell)
                   , fOffset :: !Int
                   }

fInit cells = Frame (V.fromList cells) 0

fNew n | 0 <= n = Frame (V.replicate n Nothing) 0

fReset fm = guard (fOffset fm == length (fData fm))
         >> return (fm {fOffset = 0})

fRead = to (\fr -> fData fr !? fOffset fr)

fSlice n = to go
 where
  go (Frame dt os) | os + n <= V.length dt = Just (V.slice os n dt)
                   | otherwise = Nothing

fWrite v (Frame dt os) | os < V.length dt = Just $ Frame dt' os'
                       | otherwise = Nothing
 where
  dt' = dt // [(os, v)]
  os' = os+1

fFill v (Frame dt os) | os + n <= V.length dt = Just $ Frame dt' os'
 where
  n = V.length v
  dt' = V.modify go dt
   where
    go mv = V.copy (VM.slice os n mv) v
  os' = os + n

fMove n (Frame dt os) | 0 <= os' && os' <= length dt = Just $ Frame dt os'
                      | otherwise = Nothing
 where
  os' = os+n

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

type StateTrans = State -> Maybe State

crash :: StateTrans
crash = const Nothing

copy :: Int -> StateTrans
copy n st = do
  v <- st^.act.rf.fSlice n
  (act.wf) (fFill v) st

newFrame :: Int -> StateTrans
newFrame n (State irf (Active rf wf) iwf) = do
  guard $ 0 <= n
  return $ State irf (Active rf (fNew n)) (wf:iwf)

moveFrame :: StateTrans
moveFrame (State irf (Active rf wf) (iwf0:iwf)) = do
  nrf <- fReset wf
  return $ State (rf:irf) (Active nrf iwf0) iwf
moveFrame _ = Nothing

dropFrame (State (irf0:irf) (Active _ wf) iwf) =
  return $ State irf (Active irf0 wf) iwf
dropFrame _ = Nothing

runMachineF :: MachineCodeF StateTrans -> StateTrans
runMachineF End = return
runMachineF Crash = crash
runMachineF (Write b k) = (act.wf) (fWrite (Just b)) >=> k
runMachineF (Copy n k) | 0 <= n = copy n >=> k
                       | otherwise = crash
runMachineF (Skip n k) | 0 <= n = (act.wf) (fMove n) >=> k
                       | otherwise = crash
runMachineF (Fwd n k) | 0 <= n = (act.rf) (fMove n) >=> k
                      | otherwise = crash
runMachineF (Bwd n k) | 0 <= n = (act.rf) (fMove (-n)) >=> k
                      | otherwise = crash
runMachineF (NewFrame n k) = newFrame n >=> k
runMachineF (MoveFrame k) = moveFrame >=> k
runMachineF (DropFrame k) = dropFrame >=> k
runMachineF (Read k0 k1) = \st -> do
  b <- join (st^.act.rf.fRead)
  if b then k1 st else k0 st

initialState :: [Cell] -> Int -> State
initialState input outLength = State [] (Active (fInit input) (fNew outLength)) []

finalState :: State -> Maybe [Cell]
finalState (State [] (Active _ output) []) = Just (V.toList (fData output))
finalState _ = Nothing

runMachine :: MachineCode -> [Cell] -> Int -> Maybe [Cell]
runMachine code input outputSize = cata runMachineF code (initialState input outputSize)
                               >>= finalState
