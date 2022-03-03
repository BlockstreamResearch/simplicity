-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Elements.Arbitrary
 ( genBoundaryCases,
   genPrimEnv, forallPrimEnv, forallInPrimEnv, forallOutPrimEnv
 ) where

import Data.Array (bounds, listArray, rangeSize)
import Data.Bits ((.&.))
import qualified Data.ByteString.Lazy as BSL
import Data.Serialize.Put (runPutLazy, putWord8, putWord16le, putWord32le, putLazyByteString)
import Lens.Family2 (review, over)

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Primitive
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.LibSecp256k1.Spec
import Simplicity.Ty.Arbitrary
import Simplicity.Word

import Test.Tasty.QuickCheck ( Arbitrary(..), Discard(Discard), Gen, Property, Testable
                             , arbitraryBoundedIntegral, arbitrarySizedBoundedIntegral
                             , chooseBoundedIntegral
                             , choose, frequency, oneof, listOf, listOf1, suchThat
                             , forAll, property
                             )

nonZeroAmount :: Amount -> Bool
nonZeroAmount (Amount (Explicit 0)) = False
nonZeroAmount _ = True

genBoundaryCases :: (Bounded w, Integral w) => w -> Gen w
genBoundaryCases 0 = oneof [return 0, chooseBoundedIntegral (1, maxBound)]
genBoundaryCases 1 = oneof [return 0, return 1, chooseBoundedIntegral (2, maxBound)]
genBoundaryCases boundary = oneof [return 0, chooseBoundedIntegral (1, boundary-1), return boundary, chooseBoundedIntegral (boundary + 1, maxBound)]

arbitraryVersion :: Gen Word32
arbitraryVersion = genBoundaryCases 2

arbitraryLock :: Gen Lock
arbitraryLock = genBoundaryCases 500000000

arbitraryHash256 :: Gen Hash256
arbitraryHash256 = review (over be256) <$> arbitraryBoundedIntegral

arbitraryPoint :: Gen Point
arbitraryPoint = pointAsSpec <$> arbitrary

arbitraryBS :: Gen BSL.ByteString
arbitraryBS = BSL.pack <$> listOf arbitrary

arbitraryNullData :: Gen BSL.ByteString
arbitraryNullData = BSL.cons op_return . BSL.concat <$> listOf arbitraryDatum
 where
  op_return = 0x6a
  arbitraryDatum = oneof $ [immediate, push1, push2, push4] ++ (return . BSL.singleton <$> [0x4f .. 0x60])
  immediate = do
   l <- listOf arbitraryBoundedIntegral `suchThat` ((<= 0x4b). length)
   return . runPutLazy $ putWord8 (fromIntegral (length l)) >> putLazyByteString (BSL.pack l)
  push1 = do
   l <- listOf arbitraryBoundedIntegral `suchThat` ((<= 0xff). length)
   return . runPutLazy $ putWord8 0x4c >> putWord8 (fromIntegral (length l)) >> putLazyByteString (BSL.pack l)
  push2 = do
   l <- listOf arbitraryBoundedIntegral `suchThat` ((<= 0xffff). length)
   return . runPutLazy $ putWord8 0x4d >> putWord16le (fromIntegral (length l)) >> putLazyByteString (BSL.pack l)
  push4 = do
   l <- listOf arbitraryBoundedIntegral `suchThat` ((<= 0xffffffff). length)
   return . runPutLazy $ putWord8 0x4e >> putWord32le (fromIntegral (length l)) >> putLazyByteString (BSL.pack l)

arbitraryNonNullData :: Gen BSL.ByteString
arbitraryNonNullData = do
  nulldata <- arbitraryNullData
  nondata <- arbitraryBS
  return $ BSL.append nulldata nondata

arbitraryConfidential :: Gen a -> Gen (Confidential a)
arbitraryConfidential genA = oneof [conf, nonConf]
   where
    conf = Confidential <$> arbitraryPoint
    nonConf = Explicit <$> genA

instance Arbitrary Asset where
  arbitrary = Asset <$> arbitraryConfidential arbitraryHash256

instance Arbitrary Amount where
  arbitrary = Amount <$> arbitraryConfidential arbitrarySizedBoundedIntegral

instance Arbitrary Nonce where
  arbitrary = Nonce <$> arbitraryConfidential arbitraryHash256

instance Arbitrary TxOutput where
  arbitrary = TxOutput <$> arbitrary <*> arbitrary <*> arbitrary <*> oneof [arbitraryBS, arbitraryNullData, arbitraryNonNullData]

instance Arbitrary UTXO where
  arbitrary = UTXO <$> arbitrary <*> arbitrary <*> arbitraryBS

instance Arbitrary Outpoint where
  arbitrary = Outpoint <$> arbitraryHash256 <*> arbitrarySizedBoundedIntegral

instance Arbitrary NewIssuance where
  arbitrary = (NewIssuance <$> arbitraryHash256 <*> arbitrary <*> arbitrary) `suchThat` nonZeroIssuance
   where
    nonZeroIssuance x = nonZeroAmount (newIssuanceAmount x) || nonZeroAmount (newIssuanceTokenAmount x)

instance Arbitrary Reissuance where
  arbitrary = Reissuance <$> arbitraryHash256 <*> arbitraryHash256 <*> (arbitrary `suchThat` nonZeroAmount)

instance Arbitrary SigTxInput where
  arbitrary = SigTxInput <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitraryBoundedIntegral <*> arbitrary

instance Arbitrary SigTx where
  arbitrary = SigTx <$> arbitraryVersion
                    <*> (mkArray <$> listOf1 arbitrary)
                    <*> (mkArray <$> listOf1 arbitrary)
                    <*> arbitraryLock
   where
    mkArray l = listArray (0, fromIntegral (length l - 1)) l

instance Arbitrary TapEnv where
  arbitrary = TapEnv <$> oneof [return Nothing, Just <$> arbitraryBS]
                     <*> ((0xfe .&.) <$> arbitraryBoundedIntegral)
                     <*> (mkPubKey <$> arbitraryPoint)
                     <*> listOf arbitraryHash256
   where
    mkPubKey (Point _ x) = PubKey (fe_pack x)

genPrimEnv :: Gen (Maybe PrimEnv)
genPrimEnv = do
   tx <- arbitrary
   tapenv <- arbitrary
   cmr <- arbitraryHash256
   ix <- choose (bounds (sigTxIn tx))
   return $ primEnv tx ix tapenv cmr

forallPrimEnv :: Testable prop => (PrimEnv -> prop) -> Property
forallPrimEnv p = forAll genPrimEnv go
  where
   go (Just env) = property $ p env
   go Nothing = property Discard

forallInPrimEnv :: Testable prop => (PrimEnv -> Word32 -> prop) -> Property
forallInPrimEnv p = forAll genPrimEnv go
  where
   go Nothing = property Discard
   go (Just env) = forAll genIx $ \i -> property $ p env i
    where
     (0, bnd) = bounds (sigTxIn (envTx env))
     genIx = genBoundaryCases (bnd + 1)

forallOutPrimEnv :: Testable prop => (PrimEnv -> Word32 -> prop) -> Property
forallOutPrimEnv p = forAll genPrimEnv go
  where
   go Nothing = property Discard
   go (Just env) = forAll genIx $ \i -> property $ p env i
    where
     (0, bnd) = bounds (sigTxOut (envTx env))
     genIx = genBoundaryCases (bnd + 1)
