module Simplicity.MerkleRoot
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  , hiddenRoot
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy.Char8 as BSC
import Data.List (intercalate)
import Data.Proxy (Proxy(..))

import Simplicity.Digest
import Simplicity.Primitive
import Simplicity.Term
import Simplicity.Ty.Word

tag :: [String] -> IV
tag ws | length str < 56 = bsIv . BSC.pack $ str
       | otherwise = error $ "Simplicity.MerkleRoot.Tag.tag: tag is too long: " ++ show ws
 where
  str = intercalate "\US" ws

prefix = ["Simplicity"]
typePrefix = prefix ++ ["Type"]
commitmentPrefix = prefix ++ ["Commitment"]
witnessPrefix = prefix ++ ["Witness"]
primitivePrefix = prefix ++ ["Primitive", primPrefix]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

commitmentTag :: String -> IV
commitmentTag x = tag $ commitmentPrefix ++ [x]

witnessTag :: String -> IV
witnessTag x = tag $ witnessPrefix ++ [x]

primTag :: String -> IV
primTag x = tag $ primitivePrefix ++ [x]

jetTag :: IV
jetTag = tag (prefix ++ ["Jet"])

hiddenTag :: IV
hiddenTag = tag $ (prefix ++ ["Hidden"])

-- | This function hashes a hash such that it will not collide with any 'typeRoot', 'commitmentRoot' or 'witnessRoot'.
--
-- This function is mainly designed for internal use within this Simplicity library.
hiddenRoot :: Hash256 -> Hash256
hiddenRoot = ivHash . compressHalf hiddenTag

-- | Computes a hash committing to a Simplicity type.
-- This function is memoized.
typeRoot :: Ty -> Hash256
typeRoot = memoCataTy typeRootF
 where
  typeRootF :: TyF Hash256 -> Hash256
  typeRootF One        = ivHash $ typeTag "unit"
  typeRootF (Sum a b)  = ivHash $ compress (typeTag "sum") (a, b)
  typeRootF (Prod a b) = ivHash $ compress (typeTag "prod") (a, b)

-- | A variant of 'typeRoot' for @'TyReflect' a@ values.
--
-- @
-- typeRootR = typeRoot . unreflect
-- @
typeRootR :: TyReflect a -> Hash256
typeRootR = typeRoot . unreflect

newtype CommitmentRoot a b = CommitmentRoot {
-- | Interpret a Simplicity expression as a commitment hash.
-- This commitment exclude 'witness' values and the 'disconnect'ed expression.
-- It also exclude typing information (with the exception of jets).
    commitmentRoot :: Hash256
  } deriving Eq

commit = CommitmentRoot . ivHash

instance Core CommitmentRoot where
  iden                                        = commit $ commitmentTag "iden"
  comp (CommitmentRoot s) (CommitmentRoot t)  = commit $ compress (commitmentTag "comp") (s, t)
  unit                                        = commit $ commitmentTag "unit"
  injl (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "injl") t
  injr (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "injr") t
  match (CommitmentRoot s) (CommitmentRoot t) = commit $ compress (commitmentTag "case") (s, t)
  pair (CommitmentRoot s) (CommitmentRoot t)  = commit $ compress (commitmentTag "pair") (s, t)
  take (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "take") t
  drop (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "drop") t

instance Assert CommitmentRoot where
  assertl (CommitmentRoot s) t = commit $ compress (commitmentTag "case") (s, t)
  assertr s (CommitmentRoot t) = commit $ compress (commitmentTag "case") (s, t)
  fail b = commit $ compress (commitmentTag "fail") b

instance Primitive CommitmentRoot where
  primitive = commit . primTag . primName

-- Jets commit to their types, so we use WitnessRoot here.
instance Jet CommitmentRoot where
  jet (WitnessRoot t) = commit $ compressHalf jetTag t

instance Witness CommitmentRoot where
  witness _ = commit $ commitmentTag "witness"

instance Delegate CommitmentRoot where
  disconnect (CommitmentRoot s) _ = commit $ compressHalf (commitmentTag "disconnect") s

instance Simplicity CommitmentRoot where

newtype WitnessRoot a b = WitnessRoot {
-- | Interpret a Simplicity expression as a witness hash.
-- This hash includes 'witness' values and the 'disconnect'ed expression.
-- It also includes all typing decorations.
    witnessRoot :: Hash256
  } deriving Eq

observe = WitnessRoot . ivHash

instance Core WitnessRoot where
  iden = result
   where
    result = observe $ compressHalf (witnessTag "iden") (typeRootR (reifyProxy result))

  comp ws@(WitnessRoot s) wt@(WitnessRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (witnessTag "comp") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a b -> proxy b c -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy ws wt

  unit = result
   where
    result = observe $ compressHalf (witnessTag "unit") (typeRootR (fst (reifyArrow result)))

  injl (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  injr (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  match (WitnessRoot s) (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compress (witnessTag "case") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  pair (WitnessRoot s) (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (witnessTag "pair") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a (b,c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  take (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "take") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  drop (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "drop") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

instance Assert WitnessRoot where
  assertl (WitnessRoot s) t = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  assertr s (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result
  -- This should never be called in practice, but we add it for completeness.
  fail b = observe $ compress (witnessTag "fail") b

instance Primitive WitnessRoot where
  primitive = observe . primTag . primName

instance Jet WitnessRoot where
  jet (WitnessRoot t) = observe $ compressHalf jetTag t
  -- Idea for alternative WitnessRoot instance:
  --     jet t = t
  -- Trasparent jet witnesses would mean we could define the jet class as
  --     jet :: (TyC a, TyC b) => (forall term0. (Assert term0, Primitive term0, Jet term0) => term0 a b) -> term a b
  -- And then jets could contain jets such that their Sementics, WitnessRoots, and hence CommitmentRoots would all be transparent to jet sub-experssions.
  -- Need to think carefully what this would mean for concensus, but I think it is okay.

instance Witness WitnessRoot where
  witness v = result
   where
    result = observe $ compress (compressHalf (witnessTag "witness") (typeRootR ra)) (typeRootR rb, bitStringHash (putValue v))
    (ra, rb) = reifyArrow result

instance Delegate WitnessRoot where
  disconnect ws@(WitnessRoot s) wt@(WitnessRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (witnessTag "disconnect") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy (a, w) (b, c) -> proxy c d -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy ws wt

instance Simplicity WitnessRoot where
