module Simplicity.MerkleRoot
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy.Char8 as BSC
import Data.List (intercalate)
import Data.Proxy (Proxy(..))

import Simplicity.Digest
import Simplicity.Primitive
import Simplicity.Term
import Simplicity.Ty
import Simplicity.Ty.Word
import Simplicity.Ty.Memo

tag :: [String] -> IV
tag ws | length str < 56 = bsIv . BSC.pack $ str
       | otherwise = error $ "Simplicity.MerkleRoot.Tag.tag: tag is too long: " ++ show ws
 where
  str = intercalate "\US" ws

prefix = ["Simplicity"]
typePrefix = prefix ++ ["Type"]
termPrefix = prefix ++ ["Term"]
witnessPrefix = prefix ++ ["Witness"]
primitivePrefix = prefix ++ ["Primitive", primPrefix]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

termTag :: String -> IV
termTag x = tag $ termPrefix ++ [x]

witnessTag :: String -> IV
witnessTag x = tag $ witnessPrefix ++ [x]

primTag :: String -> IV
primTag x = tag $ primitivePrefix ++ [x]

jetTag :: IV
jetTag = tag (prefix ++ ["Jet"])

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
commit = CommitmentRoot . ivHash

instance Core CommitmentRoot where
  iden                                        = commit $ termTag "iden"
  comp (CommitmentRoot t) (CommitmentRoot s)  = commit $ compress (termTag "iden") (t, s)
  unit                                        = commit $ termTag "unit"
  injl (CommitmentRoot t)                     = commit $ compressHalf (termTag "injl") t
  injr (CommitmentRoot t)                     = commit $ compressHalf (termTag "injr") t
  match (CommitmentRoot t) (CommitmentRoot s) = commit $ compress (termTag "case") (t, s)
  pair (CommitmentRoot t) (CommitmentRoot s)  = commit $ compress (termTag "pair") (t, s)
  take (CommitmentRoot t)                     = commit $ compressHalf (termTag "take") t
  drop (CommitmentRoot t)                     = commit $ compressHalf (termTag "drop") t

instance Assert CommitmentRoot where
  assertl (CommitmentRoot t) s = commit $ compress (termTag "case") (t, hashWord256 s)
  assertr t (CommitmentRoot s) = commit $ compress (termTag "case") (hashWord256 t, s)

instance Primitive CommitmentRoot where
  primitive = commit . primTag . primName

instance Jet CommitmentRoot where
  jet t = CommitmentRoot . witnessRoot $ jet t

instance Witness CommitmentRoot where
  witness _ = commit $ termTag "witness"

instance Delegate CommitmentRoot where
  disconnect (CommitmentRoot s) _ = commit $ compressHalf (termTag "disconnect") s

instance Simplicity CommitmentRoot where

newtype WitnessRoot a b = WitnessRoot { witnessRoot :: Hash256 }
observe = WitnessRoot . ivHash

instance Core WitnessRoot where
  iden = result
   where
    result = observe $ compressHalf (witnessTag "iden") (typeRootR (reifyProxy result))

  comp wt@(WitnessRoot t) ws@(WitnessRoot s) = result
   where
    result = observe $ compressHalf (compress (compress (witnessTag "comp") (t,s))
                                              (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                    (typeRootR (reifyProxy proxyC))
    proxy :: proxy a b -> proxy b c -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy wt ws

  unit = result
   where
    result = observe $ compressHalf (witnessTag "unit") (typeRootR (fst (reifyArrow result)))

  injl (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injl") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  injr (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injr") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  match (WitnessRoot t) (WitnessRoot s) = result
   where
    result = observe $ compress (compress (compress (witnessTag "case") (t,s))
                                          (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD))
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  pair (WitnessRoot t) (WitnessRoot s) = result
   where
    result = observe $ compressHalf (compress (compress (witnessTag "pair") (t,s))
                                              (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                    (typeRootR (reifyProxy proxyC))
    proxy :: proxy a (b,c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  take (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "take") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  drop (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "drop") (t,typeRootR (reifyProxy proxyA)))
                                (typeRootR (reifyProxy proxyB), typeRootR (reifyProxy proxyC))
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

instance Assert WitnessRoot where
  assertl (WitnessRoot t) s = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertl") (t,hashWord256 s))
                                          (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD))
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  assertr t (WitnessRoot s) = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertr") (hashWord256 t,s))
                                          (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD))
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

instance Primitive WitnessRoot where
  primitive = observe . primTag . primName

instance Jet WitnessRoot where
  jet (WitnessRoot t) = observe $ compressHalf jetTag t

hashWord256 :: Word256 -> Hash256
hashWord256 (((((w00,w01),(w02,w03)),((w04,w05),(w06,w07))),(((w08,w09),(w0a,w0b)),((w0c,w0d),(w0e,w0f))))
            ,((((w10,w11),(w12,w13)),((w14,w15),(w16,w17))),(((w18,w19),(w1a,w1b)),((w1c,w1d),(w1e,w1f))))
            ) = Hash256 $ BS.pack (convert <$> words)
  where
   words = [w00, w01, w02, w03, w04, w05, w06, w07, w08, w09, w0a, w0b, w0c, w0d, w0e, w0f
           ,w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w1a, w1b, w1c, w1d, w1e, w1f]
   convert = fromInteger . fromWord8
