{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- This modules tests Simplicity's serialization and deserialization functions.
module Simplicity.Serialization.Tests (tests) where

import Control.Arrow (right)
import Data.Serialize (Get, Putter, runGetState, runPut)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV

import Simplicity.Dag
import Simplicity.Digest
import Simplicity.Inference
import Simplicity.MerkleRoot
import Simplicity.Primitive
import Simplicity.Programs.Word
import Simplicity.Programs.Sha256
import Simplicity.Serialization
import Simplicity.Serialization.BitString as BitString
import Simplicity.Serialization.ByteString as ByteString
import Simplicity.Term

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck ( testProperty, Positive(Positive)
                             , Gen, Property, arbitrary, choose, elements, forAll, listOf, oneof)
import Test.QuickCheck.Property (liftBool)

-- This collects the tests for the various serialization/deserialization pairs.
tests :: TestTree
tests = testGroup "Serialization"
        [ testProperty "get-put bit-string" prop_getPutBitString
        , testProperty "get-put positive" prop_getPutPositive
        , testProperty "get-put BitString DAG" prop_getPutBitStringDag
        , testProperty "get-put ByteString DAG" prop_getPutByteStringDag
        -- This collection tests type inference on a few sample programs.
        , testGroup "Inference"
          [ testInference "fullAdder word8" (fullAdder word8)
          , testInference "adder word8" (adder word8)
          , testInference "fullMultiplier word8" (fullMultiplier word8)
          , testInference "multiplier word8" (multiplier word8)
          , testInference "hashBlock" hashBlock
        ] ]

-- Check that deserialization of serialization of bit-strings returns the original input.
prop_getPutBitString :: [Bool] -> Bool
prop_getPutBitString l = evalExactVector getBitString (UV.fromList (putBitString l [])) == Just l

-- Check that deserialization of serialization of positive numbers returns the original input.
prop_getPutPositive :: Positive Integer -> Bool
prop_getPutPositive (Positive n) = evalExactVector getPositive (UV.fromList (putPositive n [])) == Just n

-- Test an UntypedSimplicityDag predicate over suitable Arbitrary inputs.
forallUntypedTermDag :: (UntypedSimplicityDag -> Bool) -> Property
forallUntypedTermDag = forAll gen_UntypedTermF_list
 where
  gen_UntypedTermF_list = do
    l <- traverse f =<< (zip [1..] <$> listOf gen_UntypedTermF)
    case l of
     [] -> return []
     nl -> (:nl) <$> elements [uIden, uUnit]
   where
    f (i, term) = traverse (const (choose (1,i))) term
  gen_UntypedTermF :: Gen (UntypedTermF ())
  gen_UntypedTermF = oneof
    [ pure uIden
    , pure uUnit
    , pure $ uInjl ()
    , pure $ uInjr ()
    , pure $ uTake ()
    , pure $ uDrop ()
    , pure $ uComp () ()
    , pure $ uCase () ()
    , pure $ uPair () ()
    , pure $ uDisconnect () ()
    , uHidden <$> get256Bits arbitrary
    , uWitness . UV.fromList <$> arbitrary
    , uPrim <$> elements allPrim
    ]
   where
    allPrim = getPrimBit [False,True]

-- Check that deserialization of serialization of UntypeSimplicityDags works for the bit-string serialization.
prop_getPutBitStringDag :: Property
prop_getPutBitStringDag = forallUntypedTermDag prop
 where
  prop v = evalStreamWithError BitString.getDag (BitString.putDag v) == Right v
        && evalStreamWithError BitString.getDag (init (BitString.putDag v)) == Left EndOfInput
  shrink v | V.null v = []
           | otherwise  = [ V.tail v ] ++ [ V.cons (V.head v) xs' | xs' <- shrink (V.tail v) ]

-- Check that deserialization of serialization of UntypeSimplicityDags works for the byte-string serialization.
prop_getPutByteStringDag :: Property
prop_getPutByteStringDag = forallUntypedTermDag prop
 where
  prop v = runGetState ByteString.getDag bs 0 == Right (v, mempty)
   where
    bs = runPut (ByteString.putDag v)

-- Check that type inference on dags produce correct terms by testing the generated Merkle roots.
testInference :: forall a b. (TyC a, TyC b) => String -> (forall term. (Core term) => term a b) -> TestTree
testInference name program = testProperty name . liftBool $ assertion1 && assertion2
 where
  -- type inference on first pass is not necessarily equal to the orginal program because the Haskell type of internal nodes in the original program might not have the most general type.
  pass1 :: forall term. Simplicity term => Either String (term a b)
  pass1 = typeCheckDag . linearizeDag $ program
  -- I think type inference on the second pass ought to be equal to the first pass.
  pass2 :: forall term. Simplicity term => Either String (term a b)
  pass2 = typeCheckDag . linearizeDag =<< pass1
  assertion1 = pass1 == Right (program :: CommitmentRoot a b)
  assertion2 = pass2 == (pass1 :: Either String (WitnessRoot a b))
