module Simplicity.Tags
  ( typeTag
  , commitmentTag
  , identityHashTag, identityTag
  , annotatedTag
  , primTag
  , jetTag
  , hiddenTag
  , signatureTag, sigHash
  ) where

import Data.List (intercalate)
import Data.Serialize (encode)

import Simplicity.Digest

tag :: [String] -> IV
tag = tagIv . intercalate "\US"

prefix = ["Simplicity"]
typePrefix = prefix ++ ["Type"]
commitmentPrefix = prefix ++ ["Commitment"]
identityPrefix = prefix ++ ["Identity"]
annotatedPrefix = prefix ++ ["Annotated"]
primitivePrefix primPrefix = prefix ++ ["Primitive", primPrefix]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

commitmentTag :: String -> IV
commitmentTag x = tag $ commitmentPrefix ++ [x]

identityHashTag :: IV
identityHashTag = tag identityPrefix

identityTag :: String -> IV
identityTag x = tag $ identityPrefix ++ [x]

annotatedTag :: String -> IV
annotatedTag x = tag $ annotatedPrefix ++ [x]

primTag :: String -> String -> IV
primTag primPrefix x = tag $ primitivePrefix primPrefix ++ [x]

jetTag :: IV
jetTag = tag $ prefix ++ ["Jet"]

hiddenTag :: IV
hiddenTag = tag $ prefix ++ ["Hidden"]

-- | The midstate after the "standard" Simplicity signed message tag.
signatureTag :: IV
signatureTag = tag $ prefix ++ ["Signature"]

-- | Create a "standard" Simplicity signed message from an 'CommitmentRoot' of a sighash expresson, and that expression's output.
sigHash :: Hash256 -- ^ @'CommitmentRoot' () Word256@
        -> Hash256 -- ^ Output if sighash
        -> Hash256
sigHash h1 h2 = taggedHash tag $ encode h1 <> encode h2
 where
  tag = intercalate "\US" $ prefix ++ ["Signature"]
