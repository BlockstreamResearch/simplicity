-- | This module provides functions for computing commitment Merkle roots and witness Merkle roots of Simplicity expressions and Merkle roots of Simplicity types.
-- It also provides some other functions for other hashing schemes that will avoid collisions with the aforementioned Merkle roots.
module Simplicity.MerkleRoot
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  , hiddenRoot
  , signatureIv
  , cmrFail0
  ) where

import Simplicity.Digest
import Simplicity.MerkleRoot.Core
import Simplicity.Primitive
import Simplicity.Term


primTag :: String -> IV
primTag x = tag $ primitivePrefix ++ [x]
 where
  primitivePrefix = prefix ++ ["Primitive", primPrefix]

jetTag :: IV
jetTag = tag (prefix ++ ["Jet"])

instance Primitive CommitmentRoot where
  primitive = commit . primTag . primName

-- Jets commit to their types, so we use WitnessRoot here.
instance Jet CommitmentRoot where
  jet t = commit $ compressHalf jetTag (witnessRoot t)

instance Simplicity CommitmentRoot where

instance Primitive WitnessRoot where
  primitive = observe . primTag . primName

instance Jet WitnessRoot where
  jet t = observe $ compressHalf jetTag (witnessRoot t)
  -- Idea for alternative WitnessRoot instance:
  --     jet t = t
  -- Trasparent jet witnesses would mean we could define the jet class as
  --     jet :: (TyC a, TyC b) => (forall term0. (Assert term0, Primitive term0, Jet term0) => term0 a b) -> term a b
  -- And then jets could contain jets such that their Sementics, WitnessRoots, and hence CommitmentRoots would all be transparent to jet sub-experssions.
  -- Need to think carefully what this would mean for concensus, but I think it is okay.

instance Simplicity WitnessRoot where
