-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Elements.Arbitrary
 ( arbitraryLock
 , genPrimEnv, forallPrimEnv, forallInPrimEnv, forallOutPrimEnv
 ) where

import Data.Bits ((.&.))
import qualified Data.ByteString.Lazy as BSL
import Data.Serialize.Put (runPutLazy, putWord8, putWord16le, putWord32le, putLazyByteString)
import Data.Vector (fromList)
import Lens.Family2 (review, over)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Elements.DataTypes
import Simplicity.Elements.Primitive
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.LibSecp256k1.Spec
import Simplicity.Ty.Arbitrary
import Simplicity.Word

import Test.Tasty.QuickCheck ( Arbitrary(..), Discard(Discard), Gen, Property, Testable
                             , arbitraryBoundedIntegral, arbitrarySizedBoundedIntegral
                             , choose, frequency, oneof, listOf, listOf1, suchThat
                             , forAll, property
                             )

nonZeroAmount :: AmountWith prf -> Bool
nonZeroAmount (Amount (Explicit 0)) = False
nonZeroAmount _ = True

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

arbitraryConfidential :: Gen prf -> Gen a -> Gen (Confidential prf a)
arbitraryConfidential genPrf genA = oneof [conf, nonConf]
   where
    conf = Confidential <$> arbitraryPoint <*> genPrf
    nonConf = Explicit <$> genA

arbitraryAsset :: Gen Asset
arbitraryAsset = Asset <$> arbitraryConfidential (return ()) arbitraryHash256

arbitraryAssetWithWitness :: Gen AssetWithWitness
arbitraryAssetWithWitness = Asset <$> arbitraryConfidential arbitraryBS arbitraryHash256

arbitraryAmount :: Gen Amount
arbitraryAmount = Amount <$> arbitraryConfidential (return ()) arbitrarySizedBoundedIntegral

arbitraryAmountWithWitness :: Gen AmountWithWitness
arbitraryAmountWithWitness = Amount <$> arbitraryConfidential arbitraryBS arbitrarySizedBoundedIntegral

instance Arbitrary Nonce where
  arbitrary = Nonce <$> oneof [Left <$> ((,) <$> arbitrary <*> (fromInteger <$> arbitrary)),  Right <$> arbitraryHash256]

instance Arbitrary TxOutput where
  arbitrary = TxOutput <$> arbitraryAssetWithWitness <*> arbitraryAmountWithWitness <*> arbitrary <*> oneof [arbitraryBS, arbitraryNullData, arbitraryNonNullData]

instance Arbitrary UTXO where
  arbitrary = UTXO <$> arbitraryAsset <*> arbitraryAmount <*> arbitraryBS

instance Arbitrary Outpoint where
  arbitrary = Outpoint <$> arbitraryHash256 <*> arbitrarySizedBoundedIntegral

instance Arbitrary NewIssuance where
  arbitrary = (NewIssuance <$> arbitraryHash256 <*> oneof [return (Amount (Explicit 0)), arbitraryAmountWithWitness]
                                                <*> oneof [return (Amount (Explicit 0)), arbitraryAmountWithWitness]
              ) `suchThat` nonZeroIssuance
   where
    nonZeroIssuance x = nonZeroAmount (newIssuanceAmount x) || nonZeroAmount (newIssuanceTokenAmount x)

instance Arbitrary Reissuance where
  arbitrary = Reissuance <$> arbitraryHash256 <*> arbitraryHash256 <*> (arbitraryAmountWithWitness `suchThat` nonZeroAmount)

instance Arbitrary SigTxInput where
  arbitrary = SigTxInput <$> oneof [return Nothing, Just <$> arbitraryHash256]
                         <*> arbitrary
                         <*> arbitrary
                         <*> oneof [return maxBound, arbitraryBoundedIntegral]
                         <*> arbitrary
                         <*> oneof [return Nothing, Just <$> arbitraryBS]
                         <*> arbitraryBS

instance Arbitrary SigTx where
  arbitrary = SigTx <$> arbitraryVersion
                    <*> (fromList <$> listOf1 arbitrary)
                    <*> (fromList <$> listOf1 arbitrary)
                    <*> arbitraryLock

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
   gen <- arbitraryHash256
   cmr <- arbitraryHash256
   ix <- fromIntegral <$> choose (0, length (sigTxIn tx) - 1)
   return $ primEnv tx ix tapenv gen cmr

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
     genIx = fromIntegral <$> genBoundaryCases (length (sigTxIn (envTx env))) -- Generate out of bounds cases too.

forallOutPrimEnv :: Testable prop => (PrimEnv -> Word32 -> prop) -> Property
forallOutPrimEnv p = forAll genPrimEnv go
  where
   go Nothing = property Discard
   go (Just env) = forAll genIx $ \i -> property $ p env i
    where
     genIx = fromIntegral <$> genBoundaryCases (length (sigTxOut (envTx env))) -- Generate out of bounds cases too.
