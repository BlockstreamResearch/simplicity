{-# LANGUAGE EmptyCase, EmptyDataDecls, EmptyDataDeriving, FlexibleContexts, TypeFamilies #-}
-- | This modules defines the 'JetType' class, and provides the trivial empty instance of this class, 'NoJets'.
module Simplicity.JetType
  ( JetType(..)
  , NoJets(..)
  ) where

import Simplicity.Tensor
import Simplicity.Term

-- | A 'JetType' is a data structure that represets a set of known jets.
-- Every known jet has a 'specification' which is defined by some Simplicity expression (see 'Jet').
--
-- Each 'JetType' has an associated 'MatcherInfo' type that interprets Simplicity with jet expressions to
-- summerise a set of data needed to determine what jet, if any, a particular expression is.
-- Typically the 'MatcherInfo' consists of a 'Simplicity.MerkleRoot.WitnessRoot' value.
-- The 'matcher' function uses this interpretation to decide which known jet, a given Simplicity expression is, if any.
--
-- We require that given an expression @e :: forall term. 'Jet' term => term a b@,
--
-- if
--
-- @
--     'matcher' e === Just j
-- @
--
-- then
--
-- @
--     'Simplicity.Semantics.sem' ('specification' j) === 'Simplicity.Semantics.sem' e
-- @
class Jet (MatcherInfo jt) => JetType jt where
  type MatcherInfo jt :: * -> * -> *
  specification :: (TyC a, TyC b, Assert term, Primitive term) => jt a b -> term a b
  matcher :: (TyC a, TyC b) => MatcherInfo jt a b -> Maybe (jt a b)

-- | 'NoJets' is an empty type that is an instance of 'JetType'.
-- It allows one not to match any jets at all.
data NoJets a b deriving (Eq, Show)

instance JetType NoJets where
  type MatcherInfo NoJets = Unit
  specification noJets = case noJets of {}
  matcher _ = Nothing
