{-# LANGUAGE TypeOperators, TypeFamilies #-}
module Simplicity.MerkleRoot
  ( CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  ) where

import Prelude hiding (sum)

import Data.ByteString.Lazy.Char8 (pack)
import Data.List (intercalate)
import Data.Proxy (Proxy(..))

import Simplicity.Digest
import Simplicity.Term
import Simplicity.Ty
import Simplicity.Ty.Memo

tag :: [String] -> IV
tag = bsIv . pack . intercalate "\US"

prefix = ["Simplicity"]
typePrefix = prefix ++ ["Type"]
termPrefix = prefix ++ ["Term"]
witnessPrefix = prefix ++ ["Witness"]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

typeRoot :: Ty -> Hash256
typeRoot = memoCataTy typeRootF
 where
  typeRootF :: TyF Hash256 -> Hash256
  typeRootF One        = ivHash $ typeTag "unit"
  typeRootF (Sum a b)  = ivHash $ compress (typeTag "sum") (a, b)
  typeRootF (Prod a b) = ivHash $ compress (typeTag "prod") (a, b)

typeRootR :: TyReflect a -> Hash256
typeRootR = typeRoot . unreflect

newtype CommitmentRoot a b = CommitmentRoot { commitmentRoot :: Hash256 }

commitmentTag :: String -> IV
commitmentTag x = tag $ termPrefix ++ [x]

commitment :: IV -> CommitmentRoot a b
commitment = CommitmentRoot . ivHash

instance Core CommitmentRoot where
  iden                                        = commitment $ commitmentTag "iden"
  comp (CommitmentRoot t) (CommitmentRoot s)  = commitment $ compress (commitmentTag "iden") (t, s)
  unit                                        = commitment $ commitmentTag "unit"
  injl (CommitmentRoot t)                     = commitment $ compressHalf (commitmentTag "injl") t
  injr (CommitmentRoot t)                     = commitment $ compressHalf (commitmentTag "injr") t
  match (CommitmentRoot t) (CommitmentRoot s) = commitment $ compress (commitmentTag "match") (t, s)
  pair (CommitmentRoot t) (CommitmentRoot s)  = commitment $ compress (commitmentTag "pair") (t, s)
  take (CommitmentRoot t)                     = commitment $ compressHalf (commitmentTag "take") t
  drop (CommitmentRoot t)                     = commitment $ compressHalf (commitmentTag "drop") t

newtype WitnessRoot a b = WitnessRoot { witnessRoot :: Hash256 }

witnessTag x = tag $ witnessPrefix ++ [x]

witness :: IV -> WitnessRoot a b
witness = WitnessRoot . ivHash

instance Core WitnessRoot where
  iden = result
   where
    result = witness $ compressHalf (witnessTag "iden") (typeRootR (reifyProxy result))

  comp wt@(WitnessRoot t) ws@(WitnessRoot s) = result
   where
    result = witness $ compressHalf (compress (compress (witnessTag "pair") (t,s))
                                              (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                    (typeRootR (reifyProxy proxyC))
    proxy :: proxy a b -> proxy b c -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy wt ws

  unit = result
   where
    result = witness $ compressHalf (witnessTag "unit") (typeRootR (fst (reifyArrow result)))

  injl (WitnessRoot t) = result
   where
    result = witness $ compress (compress (witnessTag "injl") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  injr (WitnessRoot t) = result
   where
    result = witness $ compress (compress (witnessTag "injr") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  match (WitnessRoot t) (WitnessRoot s) = result
   where
    result = witness $ compress (compress (compress (witnessTag "pair") (t,s))
                                          (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD))
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  pair (WitnessRoot t) (WitnessRoot s) = result
   where
    result = witness $ compressHalf (compress (compress (witnessTag "pair") (t,s))
                                              (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                    (typeRootR (reifyProxy proxyC))
    proxy :: proxy a (b,c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  take (WitnessRoot t) = result
   where
    result = witness $ compress (compress (witnessTag "take") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  drop (WitnessRoot t) = result
   where
    result = witness $ compress (compress (witnessTag "drop") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result
