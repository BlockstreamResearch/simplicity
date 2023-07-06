module Simplicity.StaticAnalysis.Cost
  ( module Cost
  ) where

import Simplicity.BitMachine.StaticAnalysis.Cost as Cost
import Simplicity.Term

instance Jet TermWeight where
  jet w _t = TermWeight w

instance Simplicity TermWeight where
