-- | This modules provides a GADT for a type of "core" Simplicity jets, i.e. those jets that don't use applicaiton specific primitives.
--
-- While the 'CoreJet' data type could be made an instance of 'Simplicity.JetType.JetType', we instead generally expect it to be used as a substructure of all jets used in each specific Simplicity application.
-- The other exports of this library aid in building an instance of 'Simplicity.JetType.JetType' for those that make use of 'CoreJet' as a substructure.
{-# LANGUAGE RankNTypes, GADTs, StandaloneDeriving, ScopedTypeVariables, TypeFamilies #-}
module Simplicity.CoreJets
 ( CoreJet(..), WordJet(..), ArithJet(..), HashJet(..), Secp256k1Jet(..), SignatureJet(..), BitcoinJet(..)
 , specification, coreJetMap, coreJetLookup
 , implementation
 , fastCoreEval
 , putJetBit, getJetBit
 , ConstWordContent(..), specificationConstWord, implementationConstWord, putConstWordBit
 , SomeConstWordContent(..), getConstWordBit
 , FastCoreEval
 ) where

import Prelude hiding (fail, drop, take, subtract, Word)

import Control.Arrow ((+++), Kleisli(Kleisli), runKleisli)
import Data.Bits (shift)
import qualified Data.ByteString as BS
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Serialize (encode)
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)
import Lens.Family2 ((^..), over, review)

import Simplicity.Bitcoin
import Simplicity.Digest
import Simplicity.FFI.Jets as FFI
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Programs.Bit as Prog
import Simplicity.Programs.Arith as Prog
import Simplicity.Programs.Generic as Prog
import qualified Simplicity.Programs.CheckSig.Lib as CheckSig
import qualified Simplicity.Programs.TimeLock as TimeLock
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp256k1
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Term.Core

-- | A data type of (typed) tokens representing known "core" jets.
--
-- A core jet is a jet that doesn't use primitives.
data CoreJet a b where
  WordJet :: WordJet a b -> CoreJet a b
  ArithJet :: ArithJet a b -> CoreJet a b
  HashJet :: HashJet a b -> CoreJet a b
  Secp256k1Jet :: Secp256k1Jet a b -> CoreJet a b
  SignatureJet :: SignatureJet a b -> CoreJet a b
  BitcoinJet :: BitcoinJet a b -> CoreJet a b
deriving instance Eq (CoreJet a b)
deriving instance Show (CoreJet a b)

data WordJet a b where
  Verify :: WordJet Bit ()
  Low32 :: WordJet () Word32
  Eq32 :: WordJet (Word32, Word32) Bit
  Eq256 :: WordJet (Word256, Word256) Bit
deriving instance Eq (WordJet a b)
deriving instance Show (WordJet a b)

data ArithJet a b where
  One32 :: ArithJet () Word32
  Add32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullAdd32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Subtract32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullSubtract32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Multiply32 :: ArithJet (Word32, Word32) Word64
  FullMultiply32 :: ArithJet ((Word32, Word32), (Word32, Word32)) Word64
  Le32 :: ArithJet (Word32, Word32) Bit
deriving instance Eq (ArithJet a b)
deriving instance Show (ArithJet a b)

data HashJet a b where
  Sha256Block :: HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash
  Sha256Iv :: HashJet () Sha256.Hash
  Sha256Ctx8Init :: HashJet () Sha256.Ctx8
  Sha256Ctx8Add1 :: HashJet (Sha256.Ctx8, Word8) Sha256.Ctx8
  Sha256Ctx8Add2 :: HashJet (Sha256.Ctx8, Word16) Sha256.Ctx8
  Sha256Ctx8Add4 :: HashJet (Sha256.Ctx8, Word32) Sha256.Ctx8
  Sha256Ctx8Add8 :: HashJet (Sha256.Ctx8, Word64) Sha256.Ctx8
  Sha256Ctx8Add16 :: HashJet (Sha256.Ctx8, Word128) Sha256.Ctx8
  Sha256Ctx8Add32 :: HashJet (Sha256.Ctx8, Word256) Sha256.Ctx8
  Sha256Ctx8Add64 :: HashJet (Sha256.Ctx8, Word512) Sha256.Ctx8
  Sha256Ctx8Add128 :: HashJet (Sha256.Ctx8, Word1024) Sha256.Ctx8
  Sha256Ctx8Add256 :: HashJet (Sha256.Ctx8, Word2048) Sha256.Ctx8
  Sha256Ctx8Add512 :: HashJet (Sha256.Ctx8, Word4096) Sha256.Ctx8
  Sha256Ctx8AddBuffer511 :: HashJet (Sha256.Ctx8, Buffer511 Word8) Sha256.Ctx8
  Sha256Ctx8Finalize :: HashJet Sha256.Ctx8 Sha256.Hash
deriving instance Eq (HashJet a b)
deriving instance Show (HashJet a b)

data Secp256k1Jet a b where
  FeNormalize :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeNegate :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeAdd :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE
  FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE
  FeMultiplyBeta :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeInvert :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeSquareRoot :: Secp256k1Jet Secp256k1.FE (Either () Secp256k1.FE)
  FeIsZero :: Secp256k1Jet Secp256k1.FE Bit
  FeIsOdd :: Secp256k1Jet Secp256k1.FE Bit
  ScalarNormalize :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarNegate :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarAdd :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar
  ScalarSquare :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarMultiply :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar
  ScalarMultiplyLambda :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarInvert :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarIsZero :: Secp256k1Jet Secp256k1.Scalar Bit
  GejInfinity :: Secp256k1Jet () Secp256k1.GEJ
  GejNormalize :: Secp256k1Jet Secp256k1.GEJ (Either () Secp256k1.GE)
  GejNegate :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ
  GeNegate :: Secp256k1Jet Secp256k1.GE Secp256k1.GE
  GejDouble :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ
  GejAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GEJ) Secp256k1.GEJ
  GejGeAddEx :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) (Secp256k1.FE, Secp256k1.GEJ)
  GejGeAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) Secp256k1.GEJ
  GejRescale :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.FE) Secp256k1.GEJ
  GejIsInfinity :: Secp256k1Jet Secp256k1.GEJ Bit
  GejXEquiv :: Secp256k1Jet (Secp256k1.FE, Secp256k1.GEJ) Bit
  GejYIsOdd :: Secp256k1Jet Secp256k1.GEJ Bit
  GejIsOnCurve :: Secp256k1Jet Secp256k1.GEJ Bit
  GeIsOnCurve :: Secp256k1Jet Secp256k1.GE Bit
  Generate :: Secp256k1Jet Secp256k1.Scalar Secp256k1.GEJ
  Scale :: Secp256k1Jet (Secp256k1.Scalar,Secp256k1.GEJ) Secp256k1.GEJ
  LinearCombination1 :: Secp256k1Jet ((Secp256k1.Scalar,Secp256k1.GEJ),Secp256k1.Scalar) Secp256k1.GEJ
  LinearVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.GE),Secp256k1.Scalar),Secp256k1.GE) ()
  PointVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.Point),Secp256k1.Scalar),Secp256k1.Point) ()
  Decompress :: Secp256k1Jet Secp256k1.Point (Either () Secp256k1.GE)
deriving instance Eq (Secp256k1Jet a b)
deriving instance Show (Secp256k1Jet a b)

data SignatureJet a b where
  CheckSigVerify :: SignatureJet ((Secp256k1.PubKey, Word512),Secp256k1.Sig) ()
  Bip0340Verify :: SignatureJet ((Secp256k1.PubKey, Word256),Secp256k1.Sig) ()
deriving instance Eq (SignatureJet a b)
deriving instance Show (SignatureJet a b)

data BitcoinJet a b where
  ParseLock :: BitcoinJet Word32 (Either Word32 Word32)
  ParseSequence :: BitcoinJet Word32 (Either () (Either Word16 Word16))
deriving instance Eq (BitcoinJet a b)
deriving instance Show (BitcoinJet a b)

-- | The specification of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.specification' method.
specification :: Assert term => CoreJet a b -> term a b
specification (WordJet x) = specificationWord x
specification (ArithJet x) = specificationArith x
specification (HashJet x) = specificationHash x
specification (Secp256k1Jet x) = specificationSecp256k1 x
specification (SignatureJet x) = specificationSignature x
specification (BitcoinJet x) = specificationBitcoin x

specificationWord :: Assert term => WordJet a b -> term a b
specificationWord Verify = assert iden
specificationWord Low32 = zero word32
specificationWord Eq32 = eq
specificationWord Eq256 = eq

specificationArith :: Assert term => ArithJet a b -> term a b
specificationArith One32 = Prog.one word32
specificationArith Add32 = add word32
specificationArith FullAdd32 = full_add word32
specificationArith Subtract32 = subtract word32
specificationArith FullSubtract32 = full_subtract word32
specificationArith Multiply32 = multiply word32
specificationArith FullMultiply32 = full_multiply word32
specificationArith Le32 = le word32

specificationHash :: Assert term => HashJet a b -> term a b
specificationHash Sha256Block = Sha256.hashBlock
specificationHash Sha256Iv = Sha256.iv
specificationHash Sha256Ctx8Add1 = Sha256.ctx8Add1
specificationHash Sha256Ctx8Add2 = Sha256.ctx8Addn vector2
specificationHash Sha256Ctx8Add4 = Sha256.ctx8Addn vector4
specificationHash Sha256Ctx8Add8 = Sha256.ctx8Addn vector8
specificationHash Sha256Ctx8Add16 = Sha256.ctx8Addn vector16
specificationHash Sha256Ctx8Add32 = Sha256.ctx8Addn vector32
specificationHash Sha256Ctx8Add64 = Sha256.ctx8Addn vector64
specificationHash Sha256Ctx8Add128 = Sha256.ctx8Addn vector128
specificationHash Sha256Ctx8Add256 = Sha256.ctx8Addn vector256
specificationHash Sha256Ctx8Add512 = Sha256.ctx8Addn vector512
specificationHash Sha256Ctx8AddBuffer511 = Sha256.ctx8AddBuffer buffer511
specificationHash Sha256Ctx8Finalize = Sha256.ctx8Finalize
specificationHash Sha256Ctx8Init = Sha256.ctx8Init

specificationSecp256k1 :: Assert term => Secp256k1Jet a b -> term a b
specificationSecp256k1 FeNormalize = Secp256k1.fe_normalize
specificationSecp256k1 FeNegate = Secp256k1.fe_negate
specificationSecp256k1 FeAdd = Secp256k1.fe_add
specificationSecp256k1 FeSquare = Secp256k1.fe_square
specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply
specificationSecp256k1 FeMultiplyBeta = Secp256k1.fe_multiply_beta
specificationSecp256k1 FeInvert = Secp256k1.fe_invert
specificationSecp256k1 FeSquareRoot = Secp256k1.fe_square_root
specificationSecp256k1 FeIsZero = Secp256k1.fe_is_zero
specificationSecp256k1 FeIsOdd = Secp256k1.fe_is_odd
specificationSecp256k1 ScalarNormalize = Secp256k1.scalar_normalize
specificationSecp256k1 ScalarNegate = Secp256k1.scalar_negate
specificationSecp256k1 ScalarAdd = Secp256k1.scalar_add
specificationSecp256k1 ScalarSquare = Secp256k1.scalar_square
specificationSecp256k1 ScalarMultiply = Secp256k1.scalar_multiply
specificationSecp256k1 ScalarMultiplyLambda = Secp256k1.scalar_multiply_lambda
specificationSecp256k1 ScalarInvert = Secp256k1.scalar_invert
specificationSecp256k1 ScalarIsZero = Secp256k1.scalar_is_zero
specificationSecp256k1 GejInfinity = Secp256k1.gej_infinity
specificationSecp256k1 GejNormalize = Secp256k1.gej_normalize
specificationSecp256k1 GejNegate = Secp256k1.gej_negate
specificationSecp256k1 GeNegate = Secp256k1.ge_negate
specificationSecp256k1 GejDouble = Secp256k1.gej_double
specificationSecp256k1 GejAdd = Secp256k1.gej_add
specificationSecp256k1 GejGeAddEx = Secp256k1.gej_ge_add_ex
specificationSecp256k1 GejGeAdd = Secp256k1.gej_ge_add
specificationSecp256k1 GejRescale = Secp256k1.gej_rescale
specificationSecp256k1 GejIsInfinity = Secp256k1.gej_is_infinity
specificationSecp256k1 GejXEquiv = Secp256k1.gej_x_equiv
specificationSecp256k1 GejYIsOdd = Secp256k1.gej_y_is_odd
specificationSecp256k1 GejIsOnCurve = Secp256k1.gej_is_on_curve
specificationSecp256k1 GeIsOnCurve = Secp256k1.ge_is_on_curve
specificationSecp256k1 Generate = Secp256k1.generate
specificationSecp256k1 Scale = Secp256k1.scale
specificationSecp256k1 LinearCombination1 = Secp256k1.linear_combination_1
specificationSecp256k1 LinearVerify1 = Secp256k1.linear_verify_1
specificationSecp256k1 PointVerify1 = Secp256k1.point_verify_1
specificationSecp256k1 Decompress = Secp256k1.decompress

specificationSignature :: Assert term => SignatureJet a b -> term a b
specificationSignature CheckSigVerify = CheckSig.checkSigVerify
specificationSignature Bip0340Verify = Secp256k1.bip_0340_verify

specificationBitcoin :: Assert term => BitcoinJet a b -> term a b
specificationBitcoin ParseLock = TimeLock.parseLock
specificationBitcoin ParseSequence = TimeLock.parseSequence

-- | A jetted implementaiton for "core" jets.
--
-- @
-- 'implementation' x === 'runKleisli' ('specification' x)
-- @
implementation :: CoreJet a b -> a -> Maybe b
implementation (WordJet x) = implementationWord x
implementation (ArithJet x) = implementationArith x
implementation (HashJet x) = implementationHash x
implementation (Secp256k1Jet x) = implementationSecp256k1 x
implementation (SignatureJet x) = implementationSignature x
implementation (BitcoinJet x) = implementationBitcoin x

implementationWord :: WordJet a b -> a -> Maybe b
implementationWord Verify = either (const Nothing) Just
implementationWord Low32 = const . return $ toWord32 0
implementationWord Eq32 = \(x, y) -> return (toBit (x == y))
implementationWord Eq256 = \(x, y) -> return (toBit (x == y))

implementationArith :: ArithJet a b -> a -> Maybe b
implementationArith One32 = const . return $ toWord32 1
implementationArith Add32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith FullAdd32 = \(c, (x, y)) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith Subtract32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementationArith FullSubtract32 = \(b, (x, y)) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementationArith Multiply32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementationArith FullMultiply32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)
implementationArith Le32 = \(x, y) -> do
  let z = fromWord32 x <= fromWord32 y
  return (toBit z)

implementationHash :: HashJet a b -> a -> Maybe b
implementationHash = go
 where
  go :: HashJet a b -> a -> Maybe b
  go Sha256Block = \(h, (b1, b2)) ->
    Just . toWord256 . integerHash256 . ivHash $ compress (freeStart (fromHash h)) (fromHash b1, fromHash b2)
  go Sha256Iv = const (Just . toWord256 . integerHash256 . ivHash $ noTagIv)
  go Sha256Ctx8Add1 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack [fromInteger . fromWord8 $ v]))
  go Sha256Ctx8Add2 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector2)))
  go Sha256Ctx8Add4 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector4)))
  go Sha256Ctx8Add8 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector8)))
  go Sha256Ctx8Add16 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector16)))
  go Sha256Ctx8Add32 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector32)))
  go Sha256Ctx8Add64 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector64)))
  go Sha256Ctx8Add128 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector128)))
  go Sha256Ctx8Add256 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector256)))
  go Sha256Ctx8Add512 = \(ctx, v) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> v^..vector_ vector512)))
  go Sha256Ctx8AddBuffer511 = \(ctx, b) -> toCtx <$> (fromCtx ctx >>= flip ctxAdd (BS.pack (fromInteger . fromWord8 <$> b^..buffer_ buffer511)))
  go Sha256Ctx8Finalize = \ctx -> toWord256 . integerHash256 . ctxFinalize <$> fromCtx ctx
  go Sha256Ctx8Init = const (Just . toCtx $ ctxInit)
  fromHash = review (over be256) . fromIntegral . fromWord256
  fromCtx (buffer, (count, midstate)) = ctxBuild (fromInteger . fromWord8 <$> buffer^..buffer_ buffer63)
                                                 (fromWord64 count)
                                                 (fromHash midstate)
  toCtx ctx = (buffer, (count, midstate))
   where
    buffer = fst $ bufferFill buffer63 (toWord8 . fromIntegral <$> BS.unpack (ctxBuffer ctx))
    count = toWord64 . fromIntegral $ ctxCounter ctx
    midstate = toWord256 . integerHash256 . ivHash $ ctxIV ctx

implementationSecp256k1 :: Secp256k1Jet a b -> a -> Maybe b
implementationSecp256k1 FeNormalize = FFI.fe_normalize
implementationSecp256k1 FeNegate = FFI.fe_negate
implementationSecp256k1 FeAdd = FFI.fe_add
implementationSecp256k1 FeSquare = FFI.fe_square
implementationSecp256k1 FeMultiply = FFI.fe_multiply
implementationSecp256k1 FeMultiplyBeta = FFI.fe_multiply_beta
implementationSecp256k1 FeInvert = FFI.fe_invert
implementationSecp256k1 FeSquareRoot = FFI.fe_square_root
implementationSecp256k1 FeIsZero = FFI.fe_is_zero
implementationSecp256k1 FeIsOdd = FFI.fe_is_odd
implementationSecp256k1 ScalarNormalize = FFI.scalar_normalize
implementationSecp256k1 ScalarNegate = FFI.scalar_negate
implementationSecp256k1 ScalarAdd = FFI.scalar_add
implementationSecp256k1 ScalarSquare = FFI.scalar_square
implementationSecp256k1 ScalarMultiply = FFI.scalar_multiply
implementationSecp256k1 ScalarMultiplyLambda = FFI.scalar_multiply_lambda
implementationSecp256k1 ScalarInvert = FFI.scalar_invert
implementationSecp256k1 ScalarIsZero = FFI.scalar_is_zero
implementationSecp256k1 GejInfinity = FFI.gej_infinity
implementationSecp256k1 GejNormalize = FFI.gej_normalize
implementationSecp256k1 GejNegate = FFI.gej_negate
implementationSecp256k1 GeNegate = FFI.ge_negate
implementationSecp256k1 GejDouble = FFI.gej_double
implementationSecp256k1 GejAdd = FFI.gej_add
implementationSecp256k1 GejGeAddEx = FFI.gej_ge_add_ex
implementationSecp256k1 GejGeAdd = FFI.gej_ge_add
implementationSecp256k1 GejRescale = FFI.gej_rescale
implementationSecp256k1 GejIsInfinity = FFI.gej_is_infinity
implementationSecp256k1 GejXEquiv = FFI.gej_x_equiv
implementationSecp256k1 GejYIsOdd = FFI.gej_y_is_odd
implementationSecp256k1 GejIsOnCurve = FFI.gej_is_on_curve
implementationSecp256k1 GeIsOnCurve = FFI.ge_is_on_curve
implementationSecp256k1 Generate = FFI.generate
implementationSecp256k1 Scale = FFI.scale
implementationSecp256k1 LinearCombination1 = FFI.linear_combination_1
implementationSecp256k1 LinearVerify1 = FFI.linear_verify_1
implementationSecp256k1 PointVerify1 = FFI.point_verify_1
implementationSecp256k1 Decompress = FFI.decompress

implementationSignature :: SignatureJet a b -> a -> Maybe b
implementationSignature CheckSigVerify ((pk, (ir, h)), sig) = FFI.bip_0340_verify ((pk, msg), sig)
  where
   msg = toWord256 . integerHash256 $ sigHash (mkHash ir) (mkHash h)
   mkHash = review (over be256) . fromInteger . fromWord256
implementationSignature Bip0340Verify a = FFI.bip_0340_verify a

implementationBitcoin :: BitcoinJet a b -> a -> Maybe b
implementationBitcoin ParseLock v = Just . (toW32 +++ toW32) . parseLock $ fromW32 v
  where
   toW32 = toWord32 . fromIntegral
   fromW32 = fromInteger . fromWord32
implementationBitcoin ParseSequence v = Just . maybe (Left ()) (Right . (toW16 +++ toW16)) . parseSequence $ fromW32 v
  where
   toW16 = toWord16 . fromIntegral
   fromW32 = fromInteger . fromWord32

-- | A canonical deserialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.getJetBit' method.
getJetBit :: (Monad m) => m Void -> m Bool -> m (SomeArrow CoreJet)
getJetBit abort next =  getPositive next >>= match
 where
  makeArrow p = return (SomeArrow p)
  match 1 = (someArrowMap WordJet) <$> getJetBitWord abort next
  match 2 = (someArrowMap ArithJet) <$> getJetBitArith abort next
  match 3 = (someArrowMap HashJet) <$> getJetBitHash abort next
  match 4 = (someArrowMap Secp256k1Jet) <$> getJetBitSecp256k1 abort next
  match 5 = (someArrowMap SignatureJet) <$> getJetBitSignature abort next
  match 7 = (someArrowMap BitcoinJet) <$> getJetBitBitcoin abort next
  match _ = vacuous abort
  getJetBitWord :: (Monad m) => m Void -> m Bool -> m (SomeArrow WordJet)
  getJetBitWord abort next = getPositive next >>= matchWord
   where
    matchWord 1 = makeArrow Verify
    matchWord 2 = getPositive next >>= matchLow
    matchWord 13 = getPositive next >>= matchEq
    matchLow 5 = makeArrow Low32
    matchLow _ = vacuous abort
    matchEq 5 = makeArrow Eq32
    matchEq 8 = makeArrow Eq256
    matchEq _ = vacuous abort
  getJetBitArith :: (Monad m) => m Void -> m Bool -> m (SomeArrow ArithJet)
  getJetBitArith abort next = getPositive next >>= matchArith
   where
    matchArith 1 = getPositive next >>= matchOne
    matchArith 2 = getPositive next >>= matchFullAdd
    matchArith 3 = getPositive next >>= matchAdd
    matchArith 7 = getPositive next >>= matchFullSubtract
    matchArith 8 = getPositive next >>= matchSubtract
    matchArith 12 = getPositive next >>= matchFullMultiply
    matchArith 13 = getPositive next >>= matchMultiply
    matchArith 16 = getPositive next >>= matchLe
    matchArith _ = vacuous abort
    matchOne 5 = makeArrow Add32
    matchOne _ = vacuous abort
    matchAdd 5 = makeArrow Add32
    matchAdd _ = vacuous abort
    matchFullAdd 5 = makeArrow FullAdd32
    matchFullAdd _ = vacuous abort
    matchSubtract 5 = makeArrow Subtract32
    matchSubtract _ = vacuous abort
    matchFullSubtract 5 = makeArrow FullSubtract32
    matchFullSubtract _ = vacuous abort
    matchMultiply 5 = makeArrow Multiply32
    matchMultiply _ = vacuous abort
    matchFullMultiply 5 = makeArrow FullMultiply32
    matchFullMultiply _ = vacuous abort
    matchLe 5 = makeArrow Le32
    matchLe _ = vacuous abort
  getJetBitHash :: (Monad m) => m Void -> m Bool -> m (SomeArrow HashJet)
  getJetBitHash abort next = getPositive next >>= matchHash
   where
    matchHash 1 = getPositive next >>= matchSha2
    matchHash _ = vacuous abort
    matchSha2 1 = makeArrow Sha256Block
    matchSha2 2 = makeArrow Sha256Iv
    matchSha2 3 = getPositive next >>= matchSha2Addn
    matchSha2 4 = makeArrow Sha256Ctx8AddBuffer511
    matchSha2 5 = makeArrow Sha256Ctx8Finalize
    matchSha2 6 = makeArrow Sha256Ctx8Init
    matchSha2 _ = vacuous abort
    matchSha2Addn 1 = makeArrow Sha256Ctx8Add1
    matchSha2Addn 2 = makeArrow Sha256Ctx8Add2
    matchSha2Addn 3 = makeArrow Sha256Ctx8Add4
    matchSha2Addn 4 = makeArrow Sha256Ctx8Add8
    matchSha2Addn 5 = makeArrow Sha256Ctx8Add16
    matchSha2Addn 6 = makeArrow Sha256Ctx8Add32
    matchSha2Addn 7 = makeArrow Sha256Ctx8Add64
    matchSha2Addn 8 = makeArrow Sha256Ctx8Add128
    matchSha2Addn 9 = makeArrow Sha256Ctx8Add256
    matchSha2Addn 10 = makeArrow Sha256Ctx8Add512
    matchSha2Addn _ = vacuous abort
  getJetBitSecp256k1 :: (Monad m) => m Void -> m Bool -> m (SomeArrow Secp256k1Jet)
  getJetBitSecp256k1 abort next = getPositive next >>= matchSecp256k1
   where
    matchSecp256k1 35 = makeArrow FeNormalize
    matchSecp256k1 36 = makeArrow FeNegate
    matchSecp256k1 37 = makeArrow FeAdd
    matchSecp256k1 38 = makeArrow FeSquare
    matchSecp256k1 39 = makeArrow FeMultiply
    matchSecp256k1 40 = makeArrow FeMultiplyBeta
    matchSecp256k1 41 = makeArrow FeInvert
    matchSecp256k1 42 = makeArrow FeSquareRoot
    matchSecp256k1 43 = makeArrow FeIsZero
    matchSecp256k1 44 = makeArrow FeIsOdd
    matchSecp256k1 23 = makeArrow ScalarNormalize
    matchSecp256k1 24 = makeArrow ScalarNegate
    matchSecp256k1 25 = makeArrow ScalarAdd
    matchSecp256k1 26 = makeArrow ScalarSquare
    matchSecp256k1 27 = makeArrow ScalarMultiply
    matchSecp256k1 28 = makeArrow ScalarMultiplyLambda
    matchSecp256k1 29 = makeArrow ScalarInvert
    matchSecp256k1 30 = makeArrow ScalarIsZero
    matchSecp256k1 7  = makeArrow GejInfinity
    matchSecp256k1 8  = makeArrow GejNormalize
    matchSecp256k1 9  = makeArrow GejNegate
    matchSecp256k1 10 = makeArrow GeNegate
    matchSecp256k1 11 = makeArrow GejDouble
    matchSecp256k1 12 = makeArrow GejAdd
    matchSecp256k1 13 = makeArrow GejGeAddEx
    matchSecp256k1 14 = makeArrow GejGeAdd
    matchSecp256k1 15 = makeArrow GejRescale
    matchSecp256k1 16 = makeArrow GejIsInfinity
    matchSecp256k1 19 = makeArrow GejXEquiv
    matchSecp256k1 20 = makeArrow GejYIsOdd
    matchSecp256k1 21 = makeArrow GejIsOnCurve
    matchSecp256k1 22 = makeArrow GeIsOnCurve
    matchSecp256k1 6  = makeArrow Generate
    matchSecp256k1 5  = makeArrow Scale
    matchSecp256k1 4  = getPositive next >>= matchLinearCombination
    matchSecp256k1 3  = getPositive next >>= matchLinearVerify
    matchSecp256k1 1  = getPositive next >>= matchPointVerify
    matchSecp256k1 2  = makeArrow Decompress
    matchLinearCombination 1 = makeArrow LinearCombination1
    matchLinearCombination _ = vacuous abort
    matchLinearVerify 1 = makeArrow LinearVerify1
    matchLinearVerify _ = vacuous abort
    matchPointVerify 1 = makeArrow PointVerify1
    matchPointVerify _ = vacuous abort
  getJetBitSignature :: (Monad m) => m Void -> m Bool -> m (SomeArrow SignatureJet)
  getJetBitSignature abort next = getPositive next >>= matchSignature
   where
    matchSignature 1 = makeArrow CheckSigVerify
    matchSignature 2 = makeArrow Bip0340Verify
    matchSignature _ = vacuous abort
  getJetBitBitcoin :: (Monad m) => m Void -> m Bool -> m (SomeArrow BitcoinJet)
  getJetBitBitcoin abort next = getPositive next >>= matchBitcoin
   where
    matchBitcoin 1 = makeArrow ParseLock
    matchBitcoin 2 = makeArrow ParseSequence
    matchBitcoin _ = vacuous abort

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit (WordJet x) = putPositive 1 . putJetBitWord x
putJetBit (ArithJet x) = putPositive 2 . putJetBitArith x
putJetBit (HashJet x) = putPositive 3 . putJetBitHash x
putJetBit (Secp256k1Jet x) = putPositive 4 . putJetBitSecp256k1 x
putJetBit (SignatureJet x) = putPositive 5 . putJetBitSignature x
putJetBit (BitcoinJet x) = putPositive 7 . putJetBitBitcoin x

putJetBitWord :: WordJet a b -> DList Bool
putJetBitWord Verify = putPositive 1 . putPositive 5
putJetBitWord Low32  = putPositive 2 . putPositive 5
putJetBitWord Eq32   = putPositive 13 . putPositive 5
putJetBitWord Eq256  = putPositive 13 . putPositive 8

putJetBitArith :: ArithJet a b -> DList Bool
putJetBitArith One32          = putPositive 1 . putPositive 5
putJetBitArith FullAdd32      = putPositive 2 . putPositive 5
putJetBitArith Add32          = putPositive 3 . putPositive 5
putJetBitArith FullSubtract32 = putPositive 7 . putPositive 5
putJetBitArith Subtract32     = putPositive 8 . putPositive 5
putJetBitArith FullMultiply32 = putPositive 12 . putPositive 5
putJetBitArith Multiply32     = putPositive 13 . putPositive 5
putJetBitArith Le32           = putPositive 16 . putPositive 5

putJetBitHash :: HashJet a b -> DList Bool
putJetBitHash Sha256Block = putPositive 1 . putPositive 1
putJetBitHash Sha256Iv = putPositive 1 . putPositive 2
putJetBitHash Sha256Ctx8Add1 = putPositive 1 . putPositive 3 . putPositive 1
putJetBitHash Sha256Ctx8Add2 = putPositive 1 . putPositive 3 . putPositive 2
putJetBitHash Sha256Ctx8Add4 = putPositive 1 . putPositive 3 . putPositive 3
putJetBitHash Sha256Ctx8Add8 = putPositive 1 . putPositive 3 . putPositive 4
putJetBitHash Sha256Ctx8Add16 = putPositive 1 . putPositive 3 . putPositive 5
putJetBitHash Sha256Ctx8Add32 = putPositive 1 . putPositive 3 . putPositive 6
putJetBitHash Sha256Ctx8Add64 = putPositive 1 . putPositive 3 . putPositive 7
putJetBitHash Sha256Ctx8Add128 = putPositive 1 . putPositive 3 . putPositive 8
putJetBitHash Sha256Ctx8Add256 = putPositive 1 . putPositive 3 . putPositive 9
putJetBitHash Sha256Ctx8Add512 = putPositive 1 . putPositive 3 . putPositive 10
putJetBitHash Sha256Ctx8AddBuffer511 = putPositive 1 . putPositive 4
putJetBitHash Sha256Ctx8Finalize = putPositive 1 . putPositive 5
putJetBitHash Sha256Ctx8Init = putPositive 1 . putPositive 6

putJetBitSecp256k1 :: Secp256k1Jet a b -> DList Bool
putJetBitSecp256k1 FeNormalize = putPositive 35
putJetBitSecp256k1 FeNegate = putPositive 36
putJetBitSecp256k1 FeAdd = putPositive 37
putJetBitSecp256k1 FeSquare = putPositive 38
putJetBitSecp256k1 FeMultiply = putPositive 39
putJetBitSecp256k1 FeMultiplyBeta = putPositive 40
putJetBitSecp256k1 FeInvert = putPositive 41
putJetBitSecp256k1 FeSquareRoot = putPositive 42
putJetBitSecp256k1 FeIsZero = putPositive 43
putJetBitSecp256k1 FeIsOdd = putPositive 44
putJetBitSecp256k1 ScalarNormalize = putPositive 23
putJetBitSecp256k1 ScalarNegate = putPositive 24
putJetBitSecp256k1 ScalarAdd = putPositive 25
putJetBitSecp256k1 ScalarSquare = putPositive 26
putJetBitSecp256k1 ScalarMultiply = putPositive 27
putJetBitSecp256k1 ScalarMultiplyLambda = putPositive 28
putJetBitSecp256k1 ScalarInvert = putPositive 29
putJetBitSecp256k1 ScalarIsZero = putPositive 30
putJetBitSecp256k1 GejInfinity = putPositive 7
putJetBitSecp256k1 GejNormalize = putPositive 8
putJetBitSecp256k1 GejNegate = putPositive 9
putJetBitSecp256k1 GeNegate = putPositive 10
putJetBitSecp256k1 GejDouble = putPositive 11
putJetBitSecp256k1 GejAdd = putPositive 12
putJetBitSecp256k1 GejGeAddEx = putPositive 13
putJetBitSecp256k1 GejGeAdd = putPositive 14
putJetBitSecp256k1 GejRescale = putPositive 15
putJetBitSecp256k1 GejIsInfinity = putPositive 16
putJetBitSecp256k1 GejXEquiv = putPositive 19
putJetBitSecp256k1 GejYIsOdd = putPositive 20
putJetBitSecp256k1 GejIsOnCurve = putPositive 21
putJetBitSecp256k1 GeIsOnCurve = putPositive 22
putJetBitSecp256k1 Generate = putPositive 6
putJetBitSecp256k1 Scale = putPositive 5
putJetBitSecp256k1 LinearCombination1 = putPositive 4 . putPositive 1
putJetBitSecp256k1 LinearVerify1 = putPositive 3 . putPositive 1
putJetBitSecp256k1 PointVerify1 = putPositive 1 . putPositive 1
putJetBitSecp256k1 Decompress = putPositive 2

putJetBitSignature :: SignatureJet a b -> DList Bool
putJetBitSignature CheckSigVerify = putPositive 1
putJetBitSignature Bip0340Verify = putPositive 2

putJetBitBitcoin :: BitcoinJet a b -> DList Bool
putJetBitBitcoin ParseLock  = putPositive 1
putJetBitBitcoin ParseSequence  = putPositive 2

-- | A 'Map.Map' from the identity roots of the "core" jet specification to their corresponding token.
-- This can be used to help instantiate the 'Simplicity.JetType.matcher' method.
coreJetMap :: Map.Map Hash256 (SomeArrow CoreJet)
coreJetMap = Map.fromList
  [ -- WordJet
    mkAssoc (WordJet Verify)
  , mkAssoc (WordJet Low32)
  , mkAssoc (WordJet Eq32)
  , mkAssoc (WordJet Eq256)
    -- ArithJet
  , mkAssoc (ArithJet One32)
  , mkAssoc (ArithJet Add32)
  , mkAssoc (ArithJet Subtract32)
  , mkAssoc (ArithJet Multiply32)
  , mkAssoc (ArithJet FullAdd32)
  , mkAssoc (ArithJet FullSubtract32)
  , mkAssoc (ArithJet FullMultiply32)
  , mkAssoc (ArithJet Le32)
    -- HashJet
  , mkAssoc (HashJet Sha256Block)
  , mkAssoc (HashJet Sha256Iv)
  , mkAssoc (HashJet Sha256Ctx8Add1)
  , mkAssoc (HashJet Sha256Ctx8Add2)
  , mkAssoc (HashJet Sha256Ctx8Add4)
  , mkAssoc (HashJet Sha256Ctx8Add8)
  , mkAssoc (HashJet Sha256Ctx8Add16)
  , mkAssoc (HashJet Sha256Ctx8Add32)
  , mkAssoc (HashJet Sha256Ctx8Add64)
  , mkAssoc (HashJet Sha256Ctx8Add128)
  , mkAssoc (HashJet Sha256Ctx8Add256)
  , mkAssoc (HashJet Sha256Ctx8Add512)
  , mkAssoc (HashJet Sha256Ctx8AddBuffer511)
  , mkAssoc (HashJet Sha256Ctx8Finalize)
  , mkAssoc (HashJet Sha256Ctx8Init)
    -- Secp256k1Jet
  , mkAssoc (Secp256k1Jet FeNormalize)
  , mkAssoc (Secp256k1Jet FeNegate)
  , mkAssoc (Secp256k1Jet FeAdd)
  , mkAssoc (Secp256k1Jet FeSquare)
  , mkAssoc (Secp256k1Jet FeMultiply)
  , mkAssoc (Secp256k1Jet FeMultiplyBeta)
  , mkAssoc (Secp256k1Jet FeInvert)
  , mkAssoc (Secp256k1Jet FeSquareRoot)
  , mkAssoc (Secp256k1Jet FeIsZero)
  , mkAssoc (Secp256k1Jet FeIsOdd)
  , mkAssoc (Secp256k1Jet ScalarNormalize)
  , mkAssoc (Secp256k1Jet ScalarNegate)
  , mkAssoc (Secp256k1Jet ScalarAdd)
  , mkAssoc (Secp256k1Jet ScalarSquare)
  , mkAssoc (Secp256k1Jet ScalarMultiply)
  , mkAssoc (Secp256k1Jet ScalarMultiplyLambda)
  , mkAssoc (Secp256k1Jet ScalarInvert)
  , mkAssoc (Secp256k1Jet ScalarIsZero)
  , mkAssoc (Secp256k1Jet GejInfinity)
  , mkAssoc (Secp256k1Jet GejNormalize)
  , mkAssoc (Secp256k1Jet GejNegate)
  , mkAssoc (Secp256k1Jet GeNegate)
  , mkAssoc (Secp256k1Jet GejDouble)
  , mkAssoc (Secp256k1Jet GejAdd)
  , mkAssoc (Secp256k1Jet GejGeAddEx)
  , mkAssoc (Secp256k1Jet GejGeAdd)
  , mkAssoc (Secp256k1Jet GejRescale)
  , mkAssoc (Secp256k1Jet GejIsInfinity)
  , mkAssoc (Secp256k1Jet GejXEquiv)
  , mkAssoc (Secp256k1Jet GejYIsOdd)
  , mkAssoc (Secp256k1Jet GejIsOnCurve)
  , mkAssoc (Secp256k1Jet GeIsOnCurve)
  , mkAssoc (Secp256k1Jet Generate)
  , mkAssoc (Secp256k1Jet Scale)
  , mkAssoc (Secp256k1Jet LinearCombination1)
  , mkAssoc (Secp256k1Jet LinearVerify1)
  , mkAssoc (Secp256k1Jet PointVerify1)
  , mkAssoc (Secp256k1Jet Decompress)
    -- SignatureJet
  , mkAssoc (SignatureJet CheckSigVerify)
  , mkAssoc (SignatureJet Bip0340Verify)
    -- BitcoinJet
  , mkAssoc (BitcoinJet ParseLock)
  , mkAssoc (BitcoinJet ParseSequence)
  ]
 where
  mkAssoc :: (TyC a, TyC b) => CoreJet a b -> (Hash256, (SomeArrow CoreJet))
  mkAssoc jt = (identityRoot (specification jt), SomeArrow jt)

-- | Performs a lookup from `coreJetMap` from an `IdentityRoot`.
-- This operation preserves the Simplicity types.
coreJetLookup :: (TyC a, TyC b) => IdentityRoot a b -> Maybe (CoreJet a b)
coreJetLookup ir = do
  SomeArrow jt <- Map.lookup (identityRoot ir) coreJetMap
  let (ira, irb) = reifyArrow ir
  let (jta, jtb) = reifyArrow jt
  case (equalTyReflect ira jta, equalTyReflect irb jtb) of
    (Just Refl, Just Refl) -> return jt
    otherwise -> error "Simplicity.CoreJets.coreJetLookup: type match error"

-- | The contents of the serialized content of a constant word jet.
-- It consists of a "depth" indicating what word type the word jet produces,
-- and a numeric value that the jet outputs.
-- This numeric value fits with the size of the word type.
data ConstWordContent b = ConstWordContent (Word b) Integer
instance Eq (ConstWordContent b) where
  ConstWordContent _ x == ConstWordContent _ y = x == y
instance Show (ConstWordContent b) where
  show (ConstWordContent w v) = show v ++ ": 2^" ++ show (wordSize w)

-- | @Exists b. (Ty b) *> ConstWordContent b@
data SomeConstWordContent = forall b. (TyC b) => SomeConstWordContent (ConstWordContent b)

-- | Returns the specification of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
specificationConstWord :: (Core term, TyC b) => ConstWordContent b -> term () b
specificationConstWord (ConstWordContent w v) = scribe (toWord w v)

-- | Returns an implementation of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
implementationConstWord :: ConstWordContent b -> () -> Maybe b
implementationConstWord (ConstWordContent w v) _ = Just (toWord w v)

-- | Parses the depth and value of a constant word jet and returns 'SomeConstWordContent'.
getConstWordBit :: forall m. (Monad m) => m Void -> m Bool -> m SomeConstWordContent
getConstWordBit abort next = do
  depth <- (\x -> x - 1) <$> getPositive next
  unDepth depth (fmap SomeConstWordContent . getValue)
 where
  unDepth :: Integer -> (forall b. TyC b => Word b -> o) -> o
  unDepth 0 k = k SingleV
  unDepth n k = unDepth (n-1) (k . DoubleV)
  getValue :: TyC b => Word b -> m (ConstWordContent b)
  getValue w@SingleV = do
   b <- next
   return $ ConstWordContent w (if b then 1 else 0)
  getValue ww@(DoubleV w) = do
   (ConstWordContent _ v1) <- getValue w
   (ConstWordContent _ v2) <- getValue w
   return (ConstWordContent ww (shift v1 (wordSize w) + v2))

-- | Given a 'ConstWordContent' of some type, output the serialization of that depth and value.
putConstWordBit :: ConstWordContent b -> DList Bool
putConstWordBit (ConstWordContent w v) = putPositive (1 + depth w) . (bits ++)
 where
  depth :: Word b -> Integer
  depth (SingleV) = 0
  depth (DoubleV w) = 1 + depth w
  bits = List.reverse . List.take (wordSize w) $ List.unfoldr (\i -> Just (odd i, i `div` 2)) v

-- | An Assert instance for 'fastCoreEval'.
data FastCoreEval a b = FastCoreEval { fastCoreEvalSem :: Kleisli Maybe a b
                                     , fastCoreEvalMatcher :: IdentityRoot a b
                                     }

-- | 'fastCoreEval' optimizes Simplicity with assertions evaluation using jets.
--
-- @
-- 'fastCoreEval' t === 'sem' t
-- @
fastCoreEval = runKleisli . fastCoreEvalSem

withJets :: (TyC a, TyC b) => FastCoreEval a b -> FastCoreEval a b
withJets ~(FastCoreEval _ ir) | Just cj <- coreJetLookup ir =
  FastCoreEval { fastCoreEvalSem = Kleisli $ implementation cj
               , fastCoreEvalMatcher = ir
               }
withJets fe | otherwise = fe

mkLeaf sComb jmComb = withJets $
  FastCoreEval { fastCoreEvalSem = sComb
               , fastCoreEvalMatcher = jmComb
               }

mkUnary sComb jmComb t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher t)
               }
mkBinary sComb jmComb s t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem s) (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher s) (fastCoreEvalMatcher t)
               }

instance Core FastCoreEval where
  iden = mkLeaf iden iden
  comp = mkBinary comp comp
  unit = mkLeaf unit unit
  injl = mkUnary injl injl
  injr = mkUnary injr injr
  match = mkBinary match match
  pair = mkBinary pair pair
  take = mkUnary take take
  drop = mkUnary drop drop

instance Assert FastCoreEval where
  assertl s h = mkUnary (flip assertl h) (flip assertl h) s
  assertr h t = mkUnary (assertr h) (assertr h) t
  fail b = mkLeaf (fail b) (fail b)
