-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Bitcoin.Arbitrary
 ( arbitraryHash256, arbitraryLock
 , genPrimEnv, forallPrimEnv, forallInPrimEnv, forallOutPrimEnv
 ) where

import Data.Bits ((.&.))
import qualified Data.ByteString.Lazy as BSL
import Data.Vector (fromList)
import Lens.Family2 (review, over)

import Simplicity.Arbitrary
import Simplicity.Digest
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive
import Simplicity.LibSecp256k1.Spec
import Simplicity.Ty.Arbitrary
import Simplicity.Word

import Test.Tasty.QuickCheck ( Arbitrary(..), Discard(Discard), Gen, Property, Testable
                             , arbitraryBoundedIntegral, arbitrarySizedBoundedIntegral
                             , choose, oneof, listOf, listOf1
                             , forAll, property
                             )

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

instance Arbitrary TxOutput where
  arbitrary = TxOutput <$> arbitrarySizedBoundedIntegral <*> arbitraryBS

instance Arbitrary Outpoint where
  arbitrary = Outpoint <$> arbitraryHash256 <*> arbitrarySizedBoundedIntegral

instance Arbitrary SigTxInput where
  arbitrary = SigTxInput <$> arbitrary
                         <*> arbitrary
                         <*> oneof [return maxBound, arbitraryBoundedIntegral]
                         <*> oneof [return Nothing, Just <$> arbitraryBS]
                         <*> arbitraryBS

instance Arbitrary SigTx where
  arbitrary = SigTx <$> arbitraryVersion
                    <*> (fromList <$> listOf1 arbitrary)
                    <*> (fromList <$> listOf1 arbitrary)
                    <*> arbitraryLock

instance Arbitrary TapEnv where
  arbitrary = TapEnv <$> ((0xfe .&.) <$> arbitraryBoundedIntegral)
                     <*> (mkPubKey <$> arbitraryPoint)
                     <*> listOf arbitraryHash256
                     <*> arbitraryHash256
   where
    mkPubKey (Point _ x) = PubKey (fe_pack x)

genPrimEnv :: Gen (Maybe PrimEnv)
genPrimEnv = do
   tx <- arbitrary
   tapenv <- arbitrary
   ix <- fromIntegral <$> choose (0, length (sigTxIn tx) - 1)
   return $ primEnv tx ix tapenv

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
