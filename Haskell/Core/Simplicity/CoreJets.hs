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
 , jetCost
 , ConstWordContent(..), specificationConstWord, implementationConstWord, putConstWordBit, putConstWordValueBit, costConstWord
 , SomeConstWordContent(..), getConstWordBit
 , FastCoreEval
 ) where

import qualified Prelude
import Prelude hiding (fail, drop, take, negate, subtract, min, max, Word)

import Control.Arrow ((+++), Kleisli(Kleisli), runKleisli)
import Data.Bits ((.&.), (.|.), complement, rotate, shift, xor)
import qualified Data.ByteString as BS
import Data.Foldable (toList)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Serialize (encode)
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)
import Lens.Family2 ((^..), over, review)

import qualified Simplicity.Benchmarks as Benchmarks
import Simplicity.Bitcoin
import Simplicity.BitMachine.StaticAnalysis.Cost
import Simplicity.Digest
import Simplicity.FFI.Jets as FFI
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.MerkleRoot
import Simplicity.Serialization
import qualified Simplicity.Programs.Bit as Prog
import qualified Simplicity.Programs.Arith as Prog
import Simplicity.Programs.Generic as Prog
import qualified Simplicity.Programs.CheckSig.Lib as CheckSig
import qualified Simplicity.Programs.TimeLock as TimeLock
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp256k1
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import qualified Simplicity.Programs.Word as Prog
import Simplicity.Term.Core
import Simplicity.Tree
import Simplicity.Ty.LibSecp256k1
import Simplicity.Ty.Word
import Simplicity.Weight
import qualified Simplicity.Word as W

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
  Low1 :: WordJet () Word1
  Low8 :: WordJet () Word8
  Low16 :: WordJet () Word16
  Low32 :: WordJet () Word32
  Low64 :: WordJet () Word64
  High1 :: WordJet () Word1
  High8 :: WordJet () Word8
  High16 :: WordJet () Word16
  High32 :: WordJet () Word32
  High64 :: WordJet () Word64
  Complement1 :: WordJet Word1 Word1
  Complement8 :: WordJet Word8 Word8
  Complement16 :: WordJet Word16 Word16
  Complement32 :: WordJet Word32 Word32
  Complement64 :: WordJet Word64 Word64
  And1 :: WordJet (Word1, Word1) Word1
  And8 :: WordJet (Word8, Word8) Word8
  And16 :: WordJet (Word16, Word16) Word16
  And32 :: WordJet (Word32, Word32) Word32
  And64 :: WordJet (Word64, Word64) Word64
  Or1 :: WordJet (Word1, Word1) Word1
  Or8 :: WordJet (Word8, Word8) Word8
  Or16 :: WordJet (Word16, Word16) Word16
  Or32 :: WordJet (Word32, Word32) Word32
  Or64 :: WordJet (Word64, Word64) Word64
  Xor1 :: WordJet (Word1, Word1) Word1
  Xor8 :: WordJet (Word8, Word8) Word8
  Xor16 :: WordJet (Word16, Word16) Word16
  Xor32 :: WordJet (Word32, Word32) Word32
  Xor64 :: WordJet (Word64, Word64) Word64
  Maj1 :: WordJet (Word1, (Word1, Word1)) Word1
  Maj8 :: WordJet (Word8, (Word8, Word8)) Word8
  Maj16 :: WordJet (Word16, (Word16, Word16)) Word16
  Maj32 :: WordJet (Word32, (Word32, Word32)) Word32
  Maj64 :: WordJet (Word64, (Word64, Word64)) Word64
  XorXor1 :: WordJet (Word1, (Word1, Word1)) Word1
  XorXor8 :: WordJet (Word8, (Word8, Word8)) Word8
  XorXor16 :: WordJet (Word16, (Word16, Word16)) Word16
  XorXor32 :: WordJet (Word32, (Word32, Word32)) Word32
  XorXor64 :: WordJet (Word64, (Word64, Word64)) Word64
  Ch1 :: WordJet (Word1, (Word1, Word1)) Word1
  Ch8 :: WordJet (Word8, (Word8, Word8)) Word8
  Ch16 :: WordJet (Word16, (Word16, Word16)) Word16
  Ch32 :: WordJet (Word32, (Word32, Word32)) Word32
  Ch64 :: WordJet (Word64, (Word64, Word64)) Word64
  Some1 :: WordJet Word1 Bit
  Some8 :: WordJet Word8 Bit
  Some16 :: WordJet Word16 Bit
  Some32 :: WordJet Word32 Bit
  Some64 :: WordJet Word64 Bit
  All8 :: WordJet Word8 Bit
  All16 :: WordJet Word16 Bit
  All32 :: WordJet Word32 Bit
  All64 :: WordJet Word64 Bit
  Eq1 :: WordJet (Word1, Word1) Bit
  Eq8 :: WordJet (Word8, Word8) Bit
  Eq16 :: WordJet (Word16, Word16) Bit
  Eq32 :: WordJet (Word32, Word32) Bit
  Eq64 :: WordJet (Word64, Word64) Bit
  Eq256 :: WordJet (Word256, Word256) Bit
  FullLeftShift8_1 :: WordJet (Word8, Word1) (Word1, Word8)
  FullLeftShift8_2 :: WordJet (Word8, Word2) (Word2, Word8)
  FullLeftShift8_4 :: WordJet (Word8, Word4) (Word4, Word8)
  FullLeftShift16_1 :: WordJet (Word16, Word1) (Word1, Word16)
  FullLeftShift16_2 :: WordJet (Word16, Word2) (Word2, Word16)
  FullLeftShift16_4 :: WordJet (Word16, Word4) (Word4, Word16)
  FullLeftShift16_8 :: WordJet (Word16, Word8) (Word8, Word16)
  FullLeftShift32_1 :: WordJet (Word32, Word1) (Word1, Word32)
  FullLeftShift32_2 :: WordJet (Word32, Word2) (Word2, Word32)
  FullLeftShift32_4 :: WordJet (Word32, Word4) (Word4, Word32)
  FullLeftShift32_8 :: WordJet (Word32, Word8) (Word8, Word32)
  FullLeftShift32_16 :: WordJet (Word32, Word16) (Word16, Word32)
  FullLeftShift64_1 :: WordJet (Word64, Word1) (Word1, Word64)
  FullLeftShift64_2 :: WordJet (Word64, Word2) (Word2, Word64)
  FullLeftShift64_4 :: WordJet (Word64, Word4) (Word4, Word64)
  FullLeftShift64_8 :: WordJet (Word64, Word8) (Word8, Word64)
  FullLeftShift64_16 :: WordJet (Word64, Word16) (Word16, Word64)
  FullLeftShift64_32 :: WordJet (Word64, Word32) (Word32, Word64)
  FullRightShift8_1 :: WordJet (Word1, Word8) (Word8, Word1)
  FullRightShift8_2 :: WordJet (Word2, Word8) (Word8, Word2)
  FullRightShift8_4 :: WordJet (Word4, Word8) (Word8, Word4)
  FullRightShift16_1 :: WordJet (Word1, Word16) (Word16, Word1)
  FullRightShift16_2 :: WordJet (Word2, Word16) (Word16, Word2)
  FullRightShift16_4 :: WordJet (Word4, Word16) (Word16, Word4)
  FullRightShift16_8 :: WordJet (Word8, Word16) (Word16, Word8)
  FullRightShift32_1 :: WordJet (Word1, Word32) (Word32, Word1)
  FullRightShift32_2 :: WordJet (Word2, Word32) (Word32, Word2)
  FullRightShift32_4 :: WordJet (Word4, Word32) (Word32, Word4)
  FullRightShift32_8 :: WordJet (Word8, Word32) (Word32, Word8)
  FullRightShift32_16 :: WordJet (Word16, Word32) (Word32, Word16)
  FullRightShift64_1 :: WordJet (Word1, Word64) (Word64, Word1)
  FullRightShift64_2 :: WordJet (Word2, Word64) (Word64, Word2)
  FullRightShift64_4 :: WordJet (Word4, Word64) (Word64, Word4)
  FullRightShift64_8 :: WordJet (Word8, Word64) (Word64, Word8)
  FullRightShift64_16 :: WordJet (Word16, Word64) (Word64, Word16)
  FullRightShift64_32 :: WordJet (Word32, Word64) (Word64, Word32)
  Leftmost8_1 :: WordJet Word8 Word1
  Leftmost8_2 :: WordJet Word8 Word2
  Leftmost8_4 :: WordJet Word8 Word4
  Leftmost16_1 :: WordJet Word16 Word1
  Leftmost16_2 :: WordJet Word16 Word2
  Leftmost16_4 :: WordJet Word16 Word4
  Leftmost16_8 :: WordJet Word16 Word8
  Leftmost32_1 :: WordJet Word32 Word1
  Leftmost32_2 :: WordJet Word32 Word2
  Leftmost32_4 :: WordJet Word32 Word4
  Leftmost32_8 :: WordJet Word32 Word8
  Leftmost32_16 :: WordJet Word32 Word16
  Leftmost64_1 :: WordJet Word64 Word1
  Leftmost64_2 :: WordJet Word64 Word2
  Leftmost64_4 :: WordJet Word64 Word4
  Leftmost64_8 :: WordJet Word64 Word8
  Leftmost64_16 :: WordJet Word64 Word16
  Leftmost64_32 :: WordJet Word64 Word32
  Rightmost8_1 :: WordJet Word8 Word1
  Rightmost8_2 :: WordJet Word8 Word2
  Rightmost8_4 :: WordJet Word8 Word4
  Rightmost16_1 :: WordJet Word16 Word1
  Rightmost16_2 :: WordJet Word16 Word2
  Rightmost16_4 :: WordJet Word16 Word4
  Rightmost16_8 :: WordJet Word16 Word8
  Rightmost32_1 :: WordJet Word32 Word1
  Rightmost32_2 :: WordJet Word32 Word2
  Rightmost32_4 :: WordJet Word32 Word4
  Rightmost32_8 :: WordJet Word32 Word8
  Rightmost32_16 :: WordJet Word32 Word16
  Rightmost64_1 :: WordJet Word64 Word1
  Rightmost64_2 :: WordJet Word64 Word2
  Rightmost64_4 :: WordJet Word64 Word4
  Rightmost64_8 :: WordJet Word64 Word8
  Rightmost64_16 :: WordJet Word64 Word16
  Rightmost64_32 :: WordJet Word64 Word32
  LeftPadLow1_8 :: WordJet Word1 Word8
  LeftPadLow1_16 :: WordJet Word1 Word16
  LeftPadLow8_16 :: WordJet Word8 Word16
  LeftPadLow1_32 :: WordJet Word1 Word32
  LeftPadLow8_32 :: WordJet Word8 Word32
  LeftPadLow16_32 :: WordJet Word16 Word32
  LeftPadLow1_64 :: WordJet Word1 Word64
  LeftPadLow8_64 :: WordJet Word8 Word64
  LeftPadLow16_64 :: WordJet Word16 Word64
  LeftPadLow32_64 :: WordJet Word32 Word64
  LeftPadHigh1_8 :: WordJet Word1 Word8
  LeftPadHigh1_16 :: WordJet Word1 Word16
  LeftPadHigh8_16 :: WordJet Word8 Word16
  LeftPadHigh1_32 :: WordJet Word1 Word32
  LeftPadHigh8_32 :: WordJet Word8 Word32
  LeftPadHigh16_32 :: WordJet Word16 Word32
  LeftPadHigh1_64 :: WordJet Word1 Word64
  LeftPadHigh8_64 :: WordJet Word8 Word64
  LeftPadHigh16_64 :: WordJet Word16 Word64
  LeftPadHigh32_64 :: WordJet Word32 Word64
  LeftExtend1_8 :: WordJet Word1 Word8
  LeftExtend1_16 :: WordJet Word1 Word16
  LeftExtend8_16 :: WordJet Word8 Word16
  LeftExtend1_32 :: WordJet Word1 Word32
  LeftExtend8_32 :: WordJet Word8 Word32
  LeftExtend16_32 :: WordJet Word16 Word32
  LeftExtend1_64 :: WordJet Word1 Word64
  LeftExtend8_64 :: WordJet Word8 Word64
  LeftExtend16_64 :: WordJet Word16 Word64
  LeftExtend32_64 :: WordJet Word32 Word64
  RightPadLow1_8 :: WordJet Word1 Word8
  RightPadLow1_16 :: WordJet Word1 Word16
  RightPadLow8_16 :: WordJet Word8 Word16
  RightPadLow1_32 :: WordJet Word1 Word32
  RightPadLow8_32 :: WordJet Word8 Word32
  RightPadLow16_32 :: WordJet Word16 Word32
  RightPadLow1_64 :: WordJet Word1 Word64
  RightPadLow8_64 :: WordJet Word8 Word64
  RightPadLow16_64 :: WordJet Word16 Word64
  RightPadLow32_64 :: WordJet Word32 Word64
  RightPadHigh1_8 :: WordJet Word1 Word8
  RightPadHigh1_16 :: WordJet Word1 Word16
  RightPadHigh8_16 :: WordJet Word8 Word16
  RightPadHigh1_32 :: WordJet Word1 Word32
  RightPadHigh8_32 :: WordJet Word8 Word32
  RightPadHigh16_32 :: WordJet Word16 Word32
  RightPadHigh1_64 :: WordJet Word1 Word64
  RightPadHigh8_64 :: WordJet Word8 Word64
  RightPadHigh16_64 :: WordJet Word16 Word64
  RightPadHigh32_64 :: WordJet Word32 Word64
  RightExtend8_16 :: WordJet Word8 Word16
  RightExtend8_32 :: WordJet Word8 Word32
  RightExtend16_32 :: WordJet Word16 Word32
  RightExtend8_64 :: WordJet Word8 Word64
  RightExtend16_64 :: WordJet Word16 Word64
  RightExtend32_64 :: WordJet Word32 Word64
  LeftShiftWith8 :: WordJet (Bit, (Word4, Word8)) Word8
  LeftShiftWith16 :: WordJet (Bit, (Word4, Word16)) Word16
  LeftShiftWith32 :: WordJet (Bit, (Word8, Word32)) Word32
  LeftShiftWith64 :: WordJet (Bit, (Word8, Word64)) Word64
  LeftShift8 :: WordJet (Word4, Word8) Word8
  LeftShift16 :: WordJet (Word4, Word16) Word16
  LeftShift32 :: WordJet (Word8, Word32) Word32
  LeftShift64 :: WordJet (Word8, Word64) Word64
  RightShiftWith8 :: WordJet (Bit, (Word4, Word8)) Word8
  RightShiftWith16 :: WordJet (Bit, (Word4, Word16)) Word16
  RightShiftWith32 :: WordJet (Bit, (Word8, Word32)) Word32
  RightShiftWith64 :: WordJet (Bit, (Word8, Word64)) Word64
  RightShift8 :: WordJet (Word4, Word8) Word8
  RightShift16 :: WordJet (Word4, Word16) Word16
  RightShift32 :: WordJet (Word8, Word32) Word32
  RightShift64 :: WordJet (Word8, Word64) Word64
  LeftRotate8 :: WordJet (Word4, Word8) Word8
  LeftRotate16 :: WordJet (Word4, Word16) Word16
  LeftRotate32 :: WordJet (Word8, Word32) Word32
  LeftRotate64 :: WordJet (Word8, Word64) Word64
  RightRotate8 :: WordJet (Word4, Word8) Word8
  RightRotate16 :: WordJet (Word4, Word16) Word16
  RightRotate32 :: WordJet (Word8, Word32) Word32
  RightRotate64 :: WordJet (Word8, Word64) Word64

deriving instance Eq (WordJet a b)
deriving instance Show (WordJet a b)

data ArithJet a b where
  One8 :: ArithJet () Word8
  One16 :: ArithJet () Word16
  One32 :: ArithJet () Word32
  One64 :: ArithJet () Word64
  Add8 :: ArithJet (Word8, Word8) (Bit, Word8)
  Add16 :: ArithJet (Word16, Word16) (Bit, Word16)
  Add32 :: ArithJet (Word32, Word32) (Bit, Word32)
  Add64 :: ArithJet (Word64, Word64) (Bit, Word64)
  FullAdd8 :: ArithJet (Bit, (Word8, Word8)) (Bit, Word8)
  FullAdd16 :: ArithJet (Bit, (Word16, Word16)) (Bit, Word16)
  FullAdd32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  FullAdd64 :: ArithJet (Bit, (Word64, Word64)) (Bit, Word64)
  FullIncrement8 :: ArithJet (Bit, Word8) (Bit, Word8)
  FullIncrement16 :: ArithJet (Bit, Word16) (Bit, Word16)
  FullIncrement32 :: ArithJet (Bit, Word32) (Bit, Word32)
  FullIncrement64 :: ArithJet (Bit, Word64) (Bit, Word64)
  Increment8 :: ArithJet Word8 (Bit, Word8)
  Increment16 :: ArithJet Word16 (Bit, Word16)
  Increment32 :: ArithJet Word32 (Bit, Word32)
  Increment64 :: ArithJet Word64 (Bit, Word64)
  Subtract8 :: ArithJet (Word8, Word8) (Bit, Word8)
  Subtract16 :: ArithJet (Word16, Word16) (Bit, Word16)
  Subtract32 :: ArithJet (Word32, Word32) (Bit, Word32)
  Subtract64 :: ArithJet (Word64, Word64) (Bit, Word64)
  FullSubtract8 :: ArithJet (Bit, (Word8, Word8)) (Bit, Word8)
  FullSubtract16 :: ArithJet (Bit, (Word16, Word16)) (Bit, Word16)
  FullSubtract32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  FullSubtract64 :: ArithJet (Bit, (Word64, Word64)) (Bit, Word64)
  Negate8 :: ArithJet Word8 (Bit, Word8)
  Negate16 :: ArithJet Word16 (Bit, Word16)
  Negate32 :: ArithJet Word32 (Bit, Word32)
  Negate64 :: ArithJet Word64 (Bit, Word64)
  FullDecrement8 :: ArithJet (Bit, Word8) (Bit, Word8)
  FullDecrement16 :: ArithJet (Bit, Word16) (Bit, Word16)
  FullDecrement32 :: ArithJet (Bit, Word32) (Bit, Word32)
  FullDecrement64 :: ArithJet (Bit, Word64) (Bit, Word64)
  Decrement8 :: ArithJet Word8 (Bit, Word8)
  Decrement16 :: ArithJet Word16 (Bit, Word16)
  Decrement32 :: ArithJet Word32 (Bit, Word32)
  Decrement64 :: ArithJet Word64 (Bit, Word64)
  Multiply8 :: ArithJet (Word8, Word8) Word16
  Multiply16 :: ArithJet (Word16, Word16) Word32
  Multiply32 :: ArithJet (Word32, Word32) Word64
  Multiply64 :: ArithJet (Word64, Word64) Word128
  FullMultiply8 :: ArithJet ((Word8, Word8), (Word8, Word8)) Word16
  FullMultiply16 :: ArithJet ((Word16, Word16), (Word16, Word16)) Word32
  FullMultiply32 :: ArithJet ((Word32, Word32), (Word32, Word32)) Word64
  FullMultiply64 :: ArithJet ((Word64, Word64), (Word64, Word64)) Word128
  IsZero8 :: ArithJet Word8 Bit
  IsZero16 :: ArithJet Word16 Bit
  IsZero32 :: ArithJet Word32 Bit
  IsZero64 :: ArithJet Word64 Bit
  IsOne8 :: ArithJet Word8 Bit
  IsOne16 :: ArithJet Word16 Bit
  IsOne32 :: ArithJet Word32 Bit
  IsOne64 :: ArithJet Word64 Bit
  Le8 :: ArithJet (Word8, Word8) Bit
  Le16 :: ArithJet (Word16, Word16) Bit
  Le32 :: ArithJet (Word32, Word32) Bit
  Le64 :: ArithJet (Word64, Word64) Bit
  Lt8 :: ArithJet (Word8, Word8) Bit
  Lt16 :: ArithJet (Word16, Word16) Bit
  Lt32 :: ArithJet (Word32, Word32) Bit
  Lt64 :: ArithJet (Word64, Word64) Bit
  Min8 :: ArithJet (Word8, Word8) Word8
  Min16 :: ArithJet (Word16, Word16) Word16
  Min32 :: ArithJet (Word32, Word32) Word32
  Min64 :: ArithJet (Word64, Word64) Word64
  Max8 :: ArithJet (Word8, Word8) Word8
  Max16 :: ArithJet (Word16, Word16) Word16
  Max32 :: ArithJet (Word32, Word32) Word32
  Max64 :: ArithJet (Word64, Word64) Word64
  Median8 :: ArithJet (Word8, (Word8, Word8)) Word8
  Median16 :: ArithJet (Word16, (Word16, Word16)) Word16
  Median32 :: ArithJet (Word32, (Word32, Word32)) Word32
  Median64 :: ArithJet (Word64, (Word64, Word64)) Word64
  DivMod8 :: ArithJet (Word8, Word8) (Word8, Word8)
  DivMod16 :: ArithJet (Word16, Word16) (Word16, Word16)
  DivMod32 :: ArithJet (Word32, Word32) (Word32, Word32)
  DivMod64 :: ArithJet (Word64, Word64) (Word64, Word64)
  Divide8 :: ArithJet (Word8, Word8) Word8
  Divide16 :: ArithJet (Word16, Word16) Word16
  Divide32 :: ArithJet (Word32, Word32) Word32
  Divide64 :: ArithJet (Word64, Word64) Word64
  Modulo8 :: ArithJet (Word8, Word8) Word8
  Modulo16 :: ArithJet (Word16, Word16) Word16
  Modulo32 :: ArithJet (Word32, Word32) Word32
  Modulo64 :: ArithJet (Word64, Word64) Word64
  Divides8 :: ArithJet (Word8, Word8) Bit
  Divides16 :: ArithJet (Word16, Word16) Bit
  Divides32 :: ArithJet (Word32, Word32) Bit
  Divides64 :: ArithJet (Word64, Word64) Bit
  DivMod128_64 :: ArithJet (Word128, Word64) (Word64, Word64)
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
  GejEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GEJ) Bit
  GejGeEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GE) Bit
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
specificationWord Verify = Prog.verify
specificationWord Low1 = Prog.zero word1
specificationWord Low8 = Prog.zero word8
specificationWord Low16 = Prog.zero word16
specificationWord Low32 = Prog.zero word32
specificationWord Low64 = Prog.zero word64
specificationWord High1 = Prog.high word1
specificationWord High8 = Prog.high word8
specificationWord High16 = Prog.high word16
specificationWord High32 = Prog.high word32
specificationWord High64 = Prog.high word64
specificationWord Complement1 = Prog.complement word1
specificationWord Complement8 = Prog.complement word8
specificationWord Complement16 = Prog.complement word16
specificationWord Complement32 = Prog.complement word32
specificationWord Complement64 = Prog.complement word64
specificationWord And1 = Prog.bitwise_and word1
specificationWord And8 = Prog.bitwise_and word8
specificationWord And16 = Prog.bitwise_and word16
specificationWord And32 = Prog.bitwise_and word32
specificationWord And64 = Prog.bitwise_and word64
specificationWord Or1 = Prog.bitwise_or word1
specificationWord Or8 = Prog.bitwise_or word8
specificationWord Or16 = Prog.bitwise_or word16
specificationWord Or32 = Prog.bitwise_or word32
specificationWord Or64 = Prog.bitwise_or word64
specificationWord Xor1 = Prog.bitwise_xor word1
specificationWord Xor8 = Prog.bitwise_xor word8
specificationWord Xor16 = Prog.bitwise_xor word16
specificationWord Xor32 = Prog.bitwise_xor word32
specificationWord Xor64 = Prog.bitwise_xor word64
specificationWord Maj1 = Prog.bitwise_maj word1
specificationWord Maj8 = Prog.bitwise_maj word8
specificationWord Maj16 = Prog.bitwise_maj word16
specificationWord Maj32 = Prog.bitwise_maj word32
specificationWord Maj64 = Prog.bitwise_maj word64
specificationWord XorXor1 = Prog.bitwise_xor_xor word1
specificationWord XorXor8 = Prog.bitwise_xor_xor word8
specificationWord XorXor16 = Prog.bitwise_xor_xor word16
specificationWord XorXor32 = Prog.bitwise_xor_xor word32
specificationWord XorXor64 = Prog.bitwise_xor_xor word64
specificationWord Ch1 = Prog.bitwise_ch word1
specificationWord Ch8 = Prog.bitwise_ch word8
specificationWord Ch16 = Prog.bitwise_ch word16
specificationWord Ch32 = Prog.bitwise_ch word32
specificationWord Ch64 = Prog.bitwise_ch word64
specificationWord Some1 = Prog.some word1
specificationWord Some8 = Prog.some word8
specificationWord Some16 = Prog.some word16
specificationWord Some32 = Prog.some word32
specificationWord Some64 = Prog.some word64
specificationWord All8 = Prog.all word8
specificationWord All16 = Prog.all word16
specificationWord All32 = Prog.all word32
specificationWord All64 = Prog.all word64
specificationWord Eq1 = eq
specificationWord Eq8 = eq
specificationWord Eq16 = eq
specificationWord Eq32 = eq
specificationWord Eq64 = eq
specificationWord Eq256 = eq
specificationWord FullLeftShift8_1 = Prog.full_shift word8 word1
specificationWord FullLeftShift8_2 = Prog.full_shift word8 word2
specificationWord FullLeftShift8_4 = Prog.full_shift word8 word4
specificationWord FullLeftShift16_1 = Prog.full_shift word16 word1
specificationWord FullLeftShift16_2 = Prog.full_shift word16 word2
specificationWord FullLeftShift16_4 = Prog.full_shift word16 word4
specificationWord FullLeftShift16_8 = Prog.full_shift word16 word8
specificationWord FullLeftShift32_1 = Prog.full_shift word32 word1
specificationWord FullLeftShift32_2 = Prog.full_shift word32 word2
specificationWord FullLeftShift32_4 = Prog.full_shift word32 word4
specificationWord FullLeftShift32_8 = Prog.full_shift word32 word8
specificationWord FullLeftShift32_16 = Prog.full_shift word32 word16
specificationWord FullLeftShift64_1 = Prog.full_shift word64 word1
specificationWord FullLeftShift64_2 = Prog.full_shift word64 word2
specificationWord FullLeftShift64_4 = Prog.full_shift word64 word4
specificationWord FullLeftShift64_8 = Prog.full_shift word64 word8
specificationWord FullLeftShift64_16 = Prog.full_shift word64 word16
specificationWord FullLeftShift64_32 = Prog.full_shift word64 word32
specificationWord FullRightShift8_1 = Prog.full_shift word1 word8
specificationWord FullRightShift8_2 = Prog.full_shift word2 word8
specificationWord FullRightShift8_4 = Prog.full_shift word4 word8
specificationWord FullRightShift16_1 = Prog.full_shift word1 word16
specificationWord FullRightShift16_2 = Prog.full_shift word2 word16
specificationWord FullRightShift16_4 = Prog.full_shift word4 word16
specificationWord FullRightShift16_8 = Prog.full_shift word8 word16
specificationWord FullRightShift32_1 = Prog.full_shift word1 word32
specificationWord FullRightShift32_2 = Prog.full_shift word2 word32
specificationWord FullRightShift32_4 = Prog.full_shift word4 word32
specificationWord FullRightShift32_8 = Prog.full_shift word8 word32
specificationWord FullRightShift32_16 = Prog.full_shift word16 word32
specificationWord FullRightShift64_1 = Prog.full_shift word1 word64
specificationWord FullRightShift64_2 = Prog.full_shift word2 word64
specificationWord FullRightShift64_4 = Prog.full_shift word4 word64
specificationWord FullRightShift64_8 = Prog.full_shift word8 word64
specificationWord FullRightShift64_16 = Prog.full_shift word16 word64
specificationWord FullRightShift64_32 = Prog.full_shift word32 word64
specificationWord Leftmost8_1 = Prog.leftmost vector8
specificationWord Leftmost8_2 = Prog.leftmost vector4
specificationWord Leftmost8_4 = Prog.leftmost vector2
specificationWord Leftmost16_1 = Prog.leftmost vector16
specificationWord Leftmost16_2 = Prog.leftmost vector8
specificationWord Leftmost16_4 = Prog.leftmost vector4
specificationWord Leftmost16_8 = Prog.leftmost vector2
specificationWord Leftmost32_1 = Prog.leftmost vector32
specificationWord Leftmost32_2 = Prog.leftmost vector16
specificationWord Leftmost32_4 = Prog.leftmost vector8
specificationWord Leftmost32_8 = Prog.leftmost vector4
specificationWord Leftmost32_16 = Prog.leftmost vector2
specificationWord Leftmost64_1 = Prog.leftmost vector64
specificationWord Leftmost64_2 = Prog.leftmost vector32
specificationWord Leftmost64_4 = Prog.leftmost vector16
specificationWord Leftmost64_8 = Prog.leftmost vector8
specificationWord Leftmost64_16 = Prog.leftmost vector4
specificationWord Leftmost64_32 = Prog.leftmost vector2
specificationWord Rightmost8_1 = Prog.rightmost vector8
specificationWord Rightmost8_2 = Prog.rightmost vector4
specificationWord Rightmost8_4 = Prog.rightmost vector2
specificationWord Rightmost16_1 = Prog.rightmost vector16
specificationWord Rightmost16_2 = Prog.rightmost vector8
specificationWord Rightmost16_4 = Prog.rightmost vector4
specificationWord Rightmost16_8 = Prog.rightmost vector2
specificationWord Rightmost32_1 = Prog.rightmost vector32
specificationWord Rightmost32_2 = Prog.rightmost vector16
specificationWord Rightmost32_4 = Prog.rightmost vector8
specificationWord Rightmost32_8 = Prog.rightmost vector4
specificationWord Rightmost32_16 = Prog.rightmost vector2
specificationWord Rightmost64_1 = Prog.rightmost vector64
specificationWord Rightmost64_2 = Prog.rightmost vector32
specificationWord Rightmost64_4 = Prog.rightmost vector16
specificationWord Rightmost64_8 = Prog.rightmost vector8
specificationWord Rightmost64_16 = Prog.rightmost vector4
specificationWord Rightmost64_32 = Prog.rightmost vector2
specificationWord LeftPadLow1_8 = Prog.left_pad_low word1 vector8
specificationWord LeftPadLow1_16 = Prog.left_pad_low word1 vector16
specificationWord LeftPadLow8_16 = Prog.left_pad_low word8 vector2
specificationWord LeftPadLow1_32 = Prog.left_pad_low word1 vector32
specificationWord LeftPadLow8_32 = Prog.left_pad_low word8 vector4
specificationWord LeftPadLow16_32 = Prog.left_pad_low word16 vector2
specificationWord LeftPadLow1_64 = Prog.left_pad_low word1 vector64
specificationWord LeftPadLow8_64 = Prog.left_pad_low word8 vector8
specificationWord LeftPadLow16_64 = Prog.left_pad_low word16 vector4
specificationWord LeftPadLow32_64 = Prog.left_pad_low word32 vector2
specificationWord LeftPadHigh1_8 = Prog.left_pad_high word1 vector8
specificationWord LeftPadHigh1_16 = Prog.left_pad_high word1 vector16
specificationWord LeftPadHigh8_16 = Prog.left_pad_high word8 vector2
specificationWord LeftPadHigh1_32 = Prog.left_pad_high word1 vector32
specificationWord LeftPadHigh8_32 = Prog.left_pad_high word8 vector4
specificationWord LeftPadHigh16_32 = Prog.left_pad_high word16 vector2
specificationWord LeftPadHigh1_64 = Prog.left_pad_high word1 vector64
specificationWord LeftPadHigh8_64 = Prog.left_pad_high word8 vector8
specificationWord LeftPadHigh16_64 = Prog.left_pad_high word16 vector4
specificationWord LeftPadHigh32_64 = Prog.left_pad_high word32 vector2
specificationWord LeftExtend1_8 = Prog.left_extend word1 vector8
specificationWord LeftExtend1_16 = Prog.left_extend word1 vector16
specificationWord LeftExtend8_16 = Prog.left_extend word8 vector2
specificationWord LeftExtend1_32 = Prog.left_extend word1 vector32
specificationWord LeftExtend8_32 = Prog.left_extend word8 vector4
specificationWord LeftExtend16_32 = Prog.left_extend word16 vector2
specificationWord LeftExtend1_64 = Prog.left_extend word1 vector64
specificationWord LeftExtend8_64 = Prog.left_extend word8 vector8
specificationWord LeftExtend16_64 = Prog.left_extend word16 vector4
specificationWord LeftExtend32_64 = Prog.left_extend word32 vector2
specificationWord RightPadLow1_8 = Prog.right_pad_low word1 vector8
specificationWord RightPadLow1_16 = Prog.right_pad_low word1 vector16
specificationWord RightPadLow8_16 = Prog.right_pad_low word8 vector2
specificationWord RightPadLow1_32 = Prog.right_pad_low word1 vector32
specificationWord RightPadLow8_32 = Prog.right_pad_low word8 vector4
specificationWord RightPadLow16_32 = Prog.right_pad_low word16 vector2
specificationWord RightPadLow1_64 = Prog.right_pad_low word1 vector64
specificationWord RightPadLow8_64 = Prog.right_pad_low word8 vector8
specificationWord RightPadLow16_64 = Prog.right_pad_low word16 vector4
specificationWord RightPadLow32_64 = Prog.right_pad_low word32 vector2
specificationWord RightPadHigh1_8 = Prog.right_pad_high word1 vector8
specificationWord RightPadHigh1_16 = Prog.right_pad_high word1 vector16
specificationWord RightPadHigh8_16 = Prog.right_pad_high word8 vector2
specificationWord RightPadHigh1_32 = Prog.right_pad_high word1 vector32
specificationWord RightPadHigh8_32 = Prog.right_pad_high word8 vector4
specificationWord RightPadHigh16_32 = Prog.right_pad_high word16 vector2
specificationWord RightPadHigh1_64 = Prog.right_pad_high word1 vector64
specificationWord RightPadHigh8_64 = Prog.right_pad_high word8 vector8
specificationWord RightPadHigh16_64 = Prog.right_pad_high word16 vector4
specificationWord RightPadHigh32_64 = Prog.right_pad_high word32 vector2
specificationWord RightExtend8_16 = Prog.right_extend word8 vector2
specificationWord RightExtend8_32 = Prog.right_extend word8 vector4
specificationWord RightExtend16_32 = Prog.right_extend word16 vector2
specificationWord RightExtend8_64 = Prog.right_extend word8 vector8
specificationWord RightExtend16_64 = Prog.right_extend word16 vector4
specificationWord RightExtend32_64 = Prog.right_extend word32 vector2
specificationWord LeftShiftWith8 = Prog.left_shift_with word4 word8
specificationWord LeftShiftWith16 = Prog.left_shift_with word4 word16
specificationWord LeftShiftWith32 = Prog.left_shift_with word8 word32
specificationWord LeftShiftWith64 = Prog.left_shift_with word8 word64
specificationWord LeftShift8 = Prog.left_shift word4 word8
specificationWord LeftShift16 = Prog.left_shift word4 word16
specificationWord LeftShift32 = Prog.left_shift word8 word32
specificationWord LeftShift64 = Prog.left_shift word8 word64
specificationWord RightShiftWith8 = Prog.right_shift_with word4 word8
specificationWord RightShiftWith16 = Prog.right_shift_with word4 word16
specificationWord RightShiftWith32 = Prog.right_shift_with word8 word32
specificationWord RightShiftWith64 = Prog.right_shift_with word8 word64
specificationWord RightShift8 = Prog.right_shift word4 word8
specificationWord RightShift16 = Prog.right_shift word4 word16
specificationWord RightShift32 = Prog.right_shift word8 word32
specificationWord RightShift64 = Prog.right_shift word8 word64
specificationWord LeftRotate8 = Prog.left_rotate word4 word8
specificationWord LeftRotate16 = Prog.left_rotate word4 word16
specificationWord LeftRotate32 = Prog.left_rotate word8 word32
specificationWord LeftRotate64 = Prog.left_rotate word8 word64
specificationWord RightRotate8 = Prog.right_rotate word4 word8
specificationWord RightRotate16 = Prog.right_rotate word4 word16
specificationWord RightRotate32 = Prog.right_rotate word8 word32
specificationWord RightRotate64 = Prog.right_rotate word8 word64

specificationArith :: Assert term => ArithJet a b -> term a b
specificationArith One8 = Prog.one word8
specificationArith One16 = Prog.one word16
specificationArith One32 = Prog.one word32
specificationArith One64 = Prog.one word64
specificationArith Add8 = Prog.add word8
specificationArith Add16 = Prog.add word16
specificationArith Add32 = Prog.add word32
specificationArith Add64 = Prog.add word64
specificationArith FullAdd8 = Prog.full_add word8
specificationArith FullAdd16 = Prog.full_add word16
specificationArith FullAdd32 = Prog.full_add word32
specificationArith FullAdd64 = Prog.full_add word64
specificationArith FullIncrement8 = Prog.full_increment word8
specificationArith FullIncrement16 = Prog.full_increment word16
specificationArith FullIncrement32 = Prog.full_increment word32
specificationArith FullIncrement64 = Prog.full_increment word64
specificationArith Increment8 = Prog.increment word8
specificationArith Increment16 = Prog.increment word16
specificationArith Increment32 = Prog.increment word32
specificationArith Increment64 = Prog.increment word64
specificationArith Subtract8 = Prog.subtract word8
specificationArith Subtract16 = Prog.subtract word16
specificationArith Subtract32 = Prog.subtract word32
specificationArith Subtract64 = Prog.subtract word64
specificationArith FullSubtract8 = Prog.full_subtract word8
specificationArith FullSubtract16 = Prog.full_subtract word16
specificationArith FullSubtract32 = Prog.full_subtract word32
specificationArith FullSubtract64 = Prog.full_subtract word64
specificationArith Negate8 = Prog.negate word8
specificationArith Negate16 = Prog.negate word16
specificationArith Negate32 = Prog.negate word32
specificationArith Negate64 = Prog.negate word64
specificationArith FullDecrement8 = Prog.full_decrement word8
specificationArith FullDecrement16 = Prog.full_decrement word16
specificationArith FullDecrement32 = Prog.full_decrement word32
specificationArith FullDecrement64 = Prog.full_decrement word64
specificationArith Decrement8 = Prog.decrement word8
specificationArith Decrement16 = Prog.decrement word16
specificationArith Decrement32 = Prog.decrement word32
specificationArith Decrement64 = Prog.decrement word64
specificationArith Multiply8 = Prog.multiply word8
specificationArith Multiply16 = Prog.multiply word16
specificationArith Multiply32 = Prog.multiply word32
specificationArith Multiply64 = Prog.multiply word64
specificationArith FullMultiply8 = Prog.full_multiply word8
specificationArith FullMultiply16 = Prog.full_multiply word16
specificationArith FullMultiply32 = Prog.full_multiply word32
specificationArith FullMultiply64 = Prog.full_multiply word64
specificationArith IsZero8 = Prog.is_zero word8
specificationArith IsZero16 = Prog.is_zero word16
specificationArith IsZero32 = Prog.is_zero word32
specificationArith IsZero64 = Prog.is_zero word64
specificationArith IsOne8 = Prog.is_one word8
specificationArith IsOne16 = Prog.is_one word16
specificationArith IsOne32 = Prog.is_one word32
specificationArith IsOne64 = Prog.is_one word64
specificationArith Le8 = Prog.le word8
specificationArith Le16 = Prog.le word16
specificationArith Le32 = Prog.le word32
specificationArith Le64 = Prog.le word64
specificationArith Lt8 = Prog.lt word8
specificationArith Lt16 = Prog.lt word16
specificationArith Lt32 = Prog.lt word32
specificationArith Lt64 = Prog.lt word64
specificationArith Min8 = Prog.min word8
specificationArith Min16 = Prog.min word16
specificationArith Min32 = Prog.min word32
specificationArith Min64 = Prog.min word64
specificationArith Max8 = Prog.max word8
specificationArith Max16 = Prog.max word16
specificationArith Max32 = Prog.max word32
specificationArith Max64 = Prog.max word64
specificationArith Median8 = Prog.median word8
specificationArith Median16 = Prog.median word16
specificationArith Median32 = Prog.median word32
specificationArith Median64 = Prog.median word64
specificationArith DivMod8 = Prog.div_mod word8
specificationArith DivMod16 = Prog.div_mod word16
specificationArith DivMod32 = Prog.div_mod word32
specificationArith DivMod64 = Prog.div_mod word64
specificationArith Divide8 = Prog.divide word8
specificationArith Divide16 = Prog.divide word16
specificationArith Divide32 = Prog.divide word32
specificationArith Divide64 = Prog.divide word64
specificationArith Modulo8 = Prog.modulo word8
specificationArith Modulo16 = Prog.modulo word16
specificationArith Modulo32 = Prog.modulo word32
specificationArith Modulo64 = Prog.modulo word64
specificationArith Divides8 = Prog.divides word8
specificationArith Divides16 = Prog.divides word16
specificationArith Divides32 = Prog.divides word32
specificationArith Divides64 = Prog.divides word64
specificationArith DivMod128_64 = Prog.div2n1n word64

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
specificationSecp256k1 GejEquiv = Secp256k1.gej_equiv
specificationSecp256k1 GejGeEquiv = Secp256k1.gej_ge_equiv
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
implementationWord Low1 = const . return $ toWord1 0
implementationWord Low8 = const . return $ toWord8 0
implementationWord Low16 = const . return $ toWord16 0
implementationWord Low32 = const . return $ toWord32 0
implementationWord Low64 = const . return $ toWord64 0
implementationWord High1 = const . return $ toWord1 (-1)
implementationWord High8 = const . return $ toWord8 (-1)
implementationWord High16 = const . return $ toWord16 (-1)
implementationWord High32 = const . return $ toWord32 (-1)
implementationWord High64 = const . return $ toWord64 (-1)
implementationWord Complement1 = \x -> return (toWord1 (complement (fromWord1 x)))
implementationWord Complement8 = \x -> return (toWord8 (complement (fromWord8 x)))
implementationWord Complement16 = \x -> return (toWord16 (complement (fromWord16 x)))
implementationWord Complement32 = \x -> return (toWord32 (complement (fromWord32 x)))
implementationWord Complement64 = \x -> return (toWord64 (complement (fromWord64 x)))
implementationWord And1 = \(x, y) -> return (toWord1 (fromWord1 x .&. fromWord1 y))
implementationWord And8 = \(x, y) -> return (toWord8 (fromWord8 x .&. fromWord8 y))
implementationWord And16 = \(x, y) -> return (toWord16 (fromWord16 x .&. fromWord16 y))
implementationWord And32 = \(x, y) -> return (toWord32 (fromWord32 x .&. fromWord32 y))
implementationWord And64 = \(x, y) -> return (toWord64 (fromWord64 x .&. fromWord64 y))
implementationWord Or1 = \(x, y) -> return (toWord1 (fromWord1 x .|. fromWord1 y))
implementationWord Or8 = \(x, y) -> return (toWord8 (fromWord8 x .|. fromWord8 y))
implementationWord Or16 = \(x, y) -> return (toWord16 (fromWord16 x .|. fromWord16 y))
implementationWord Or32 = \(x, y) -> return (toWord32 (fromWord32 x .|. fromWord32 y))
implementationWord Or64 = \(x, y) -> return (toWord64 (fromWord64 x .|. fromWord64 y))
implementationWord Xor1 = \(x, y) -> return (toWord1 (fromWord1 x `xor` fromWord1 y))
implementationWord Xor8 = \(x, y) -> return (toWord8 (fromWord8 x `xor` fromWord8 y))
implementationWord Xor16 = \(x, y) -> return (toWord16 (fromWord16 x `xor` fromWord16 y))
implementationWord Xor32 = \(x, y) -> return (toWord32 (fromWord32 x `xor` fromWord32 y))
implementationWord Xor64 = \(x, y) -> return (toWord64 (fromWord64 x `xor` fromWord64 y))
implementationWord Maj1 = \(x, (y, z)) -> return (toWord1 (fromWord1 x .&. fromWord1 y
                                                       .|. fromWord1 y .&. fromWord1 z
                                                       .|. fromWord1 z .&. fromWord1 x))
implementationWord Maj8 = \(x, (y, z)) -> return (toWord8 (fromWord8 x .&. fromWord8 y
                                                       .|. fromWord8 y .&. fromWord8 z
                                                       .|. fromWord8 z .&. fromWord8 x))
implementationWord Maj16 = \(x, (y, z)) -> return (toWord16 (fromWord16 x .&. fromWord16 y
                                                         .|. fromWord16 y .&. fromWord16 z
                                                         .|. fromWord16 z .&. fromWord16 x))
implementationWord Maj32 = \(x, (y, z)) -> return (toWord32 (fromWord32 x .&. fromWord32 y
                                                         .|. fromWord32 y .&. fromWord32 z
                                                         .|. fromWord32 z .&. fromWord32 x))
implementationWord Maj64 = \(x, (y, z)) -> return (toWord64 (fromWord64 x .&. fromWord64 y
                                                         .|. fromWord64 y .&. fromWord64 z
                                                         .|. fromWord64 z .&. fromWord64 x))
implementationWord XorXor1 = \(x, (y, z)) -> return (toWord1 (fromWord1 x `xor` fromWord1 y `xor` fromWord1 z))
implementationWord XorXor8 = \(x, (y, z)) -> return (toWord8 (fromWord8 x `xor` fromWord8 y `xor` fromWord8 z))
implementationWord XorXor16 = \(x, (y, z)) -> return (toWord16 (fromWord16 x `xor` fromWord16 y `xor` fromWord16 z))
implementationWord XorXor32 = \(x, (y, z)) -> return (toWord32 (fromWord32 x `xor` fromWord32 y `xor` fromWord32 z))
implementationWord XorXor64 = \(x, (y, z)) -> return (toWord64 (fromWord64 x `xor` fromWord64 y `xor` fromWord64 z))
implementationWord Ch1 = \(x, (y, z)) -> return (toWord1 (fromWord1 x .&. fromWord1 y
                                                      .|. complement (fromWord1 x) .&. fromWord1 z))
implementationWord Ch8 = \(x, (y, z)) -> return (toWord8 (fromWord8 x .&. fromWord8 y
                                                      .|. complement (fromWord8 x) .&. fromWord8 z))
implementationWord Ch16 = \(x, (y, z)) -> return (toWord16 (fromWord16 x .&. fromWord16 y
                                                        .|. complement (fromWord16 x) .&. fromWord16 z))
implementationWord Ch32 = \(x, (y, z)) -> return (toWord32 (fromWord32 x .&. fromWord32 y
                                                        .|. complement (fromWord32 x) .&. fromWord32 z))
implementationWord Ch64 = \(x, (y, z)) -> return (toWord64 (fromWord64 x .&. fromWord64 y
                                                        .|. complement (fromWord64 x) .&. fromWord64 z))
implementationWord Some1 = \x -> do
  let z = fromWord1 x /= 0
  return (toBit z)
implementationWord Some8 = \x -> do
  let z = fromWord8 x /= 0
  return (toBit z)
implementationWord Some16 = \x -> do
  let z = fromWord16 x /= 0
  return (toBit z)
implementationWord Some32 = \x -> do
  let z = fromWord32 x /= 0
  return (toBit z)
implementationWord Some64 = \x -> do
  let z = fromWord64 x /= 0
  return (toBit z)
implementationWord All8 = \x -> do
  let z = fromWord8 x == 2^8 - 1
  return (toBit z)
implementationWord All16 = \x -> do
  let z = fromWord16 x == 2^16 - 1
  return (toBit z)
implementationWord All32 = \x -> do
  let z = fromWord32 x == 2^32 - 1
  return (toBit z)
implementationWord All64 = \x -> do
  let z = fromWord64 x == 2^64 - 1
  return (toBit z)
implementationWord Eq1 = \(x, y) -> return (toBit (x == y))
implementationWord Eq8 = \(x, y) -> return (toBit (x == y))
implementationWord Eq16 = \(x, y) -> return (toBit (x == y))
implementationWord Eq32 = \(x, y) -> return (toBit (x == y))
implementationWord Eq64 = \(x, y) -> return (toBit (x == y))
implementationWord Eq256 = \(x, y) -> return (toBit (x == y))
implementationWord FullLeftShift8_1 = \(x, y) ->
  return (toWord1 $ fromWord8 x `shift` (1-8), toWord8 $ fromWord8 x `shift` 1 .|. fromWord1 y)
implementationWord FullLeftShift8_2 = \(x, y) ->
  return (toWord2 $ fromWord8 x `shift` (2-8), toWord8 $ fromWord8 x `shift` 2 .|. fromWord2 y)
implementationWord FullLeftShift8_4 = \(x, y) ->
  return (toWord4 $ fromWord8 x `shift` (4-8), toWord8 $ fromWord8 x `shift` 4 .|. fromWord4 y)
implementationWord FullLeftShift16_1 = \(x, y) ->
  return (toWord1 $ fromWord16 x `shift` (1-16), toWord16 $ fromWord16 x `shift` 1 .|. fromWord1 y)
implementationWord FullLeftShift16_2 = \(x, y) ->
  return (toWord2 $ fromWord16 x `shift` (2-16), toWord16 $ fromWord16 x `shift` 2 .|. fromWord2 y)
implementationWord FullLeftShift16_4 = \(x, y) ->
  return (toWord4 $ fromWord16 x `shift` (4-16), toWord16 $ fromWord16 x `shift` 4 .|. fromWord4 y)
implementationWord FullLeftShift16_8 = \(x, y) ->
  return (toWord8 $ fromWord16 x `shift` (8-16), toWord16 $ fromWord16 x `shift` 8 .|. fromWord8 y)
implementationWord FullLeftShift32_1 = \(x, y) ->
  return (toWord1 $ fromWord32 x `shift` (1-32), toWord32 $ fromWord32 x `shift` 1 .|. fromWord1 y)
implementationWord FullLeftShift32_2 = \(x, y) ->
  return (toWord2 $ fromWord32 x `shift` (2-32), toWord32 $ fromWord32 x `shift` 2 .|. fromWord2 y)
implementationWord FullLeftShift32_4 = \(x, y) ->
  return (toWord4 $ fromWord32 x `shift` (4-32), toWord32 $ fromWord32 x `shift` 4 .|. fromWord4 y)
implementationWord FullLeftShift32_8 = \(x, y) ->
  return (toWord8 $ fromWord32 x `shift` (8-32), toWord32 $ fromWord32 x `shift` 8 .|. fromWord8 y)
implementationWord FullLeftShift32_16 = \(x, y) ->
  return (toWord16 $ fromWord32 x `shift` (16-32), toWord32 $ fromWord32 x `shift` 16 .|. fromWord16 y)
implementationWord FullLeftShift64_1 = \(x, y) ->
  return (toWord1 $ fromWord64 x `shift` (1-64), toWord64 $ fromWord64 x `shift` 1 .|. fromWord1 y)
implementationWord FullLeftShift64_2 = \(x, y) ->
  return (toWord2 $ fromWord64 x `shift` (2-64), toWord64 $ fromWord64 x `shift` 2 .|. fromWord2 y)
implementationWord FullLeftShift64_4 = \(x, y) ->
  return (toWord4 $ fromWord64 x `shift` (4-64), toWord64 $ fromWord64 x `shift` 4 .|. fromWord4 y)
implementationWord FullLeftShift64_8 = \(x, y) ->
  return (toWord8 $ fromWord64 x `shift` (8-64), toWord64 $ fromWord64 x `shift` 8 .|. fromWord8 y)
implementationWord FullLeftShift64_16 = \(x, y) ->
  return (toWord16 $ fromWord64 x `shift` (16-64), toWord64 $ fromWord64 x `shift` 16 .|. fromWord16 y)
implementationWord FullLeftShift64_32 = \(x, y) ->
  return (toWord32 $ fromWord64 x `shift` (32-64), toWord64 $ fromWord64 x `shift` 32 .|. fromWord32 y)
implementationWord FullRightShift8_1 = \(x, y) ->
  return (toWord8 $ fromWord1 x `shift` (8-1) .|. fromWord8 y `shift` (-1), toWord1 $ fromWord8 y)
implementationWord FullRightShift8_2 = \(x, y) ->
  return (toWord8 $ fromWord2 x `shift` (8-2) .|. fromWord8 y `shift` (-2), toWord2 $ fromWord8 y)
implementationWord FullRightShift8_4 = \(x, y) ->
  return (toWord8 $ fromWord4 x `shift` (8-4) .|. fromWord8 y `shift` (-4), toWord4 $ fromWord8 y)
implementationWord FullRightShift16_1 = \(x, y) ->
  return (toWord16 $ fromWord1 x `shift` (16-1) .|. fromWord16 y `shift` (-1), toWord1 $ fromWord16 y)
implementationWord FullRightShift16_2 = \(x, y) ->
  return (toWord16 $ fromWord2 x `shift` (16-2) .|. fromWord16 y `shift` (-2), toWord2 $ fromWord16 y)
implementationWord FullRightShift16_4 = \(x, y) ->
  return (toWord16 $ fromWord4 x `shift` (16-4) .|. fromWord16 y `shift` (-4), toWord4 $ fromWord16 y)
implementationWord FullRightShift16_8 = \(x, y) ->
  return (toWord16 $ fromWord8 x `shift` (16-8) .|. fromWord16 y `shift` (-8), toWord8 $ fromWord16 y)
implementationWord FullRightShift32_1 = \(x, y) ->
  return (toWord32 $ fromWord1 x `shift` (32-1) .|. fromWord32 y `shift` (-1), toWord1 $ fromWord32 y)
implementationWord FullRightShift32_2 = \(x, y) ->
  return (toWord32 $ fromWord2 x `shift` (32-2) .|. fromWord32 y `shift` (-2), toWord2 $ fromWord32 y)
implementationWord FullRightShift32_4 = \(x, y) ->
  return (toWord32 $ fromWord4 x `shift` (32-4) .|. fromWord32 y `shift` (-4), toWord4 $ fromWord32 y)
implementationWord FullRightShift32_8 = \(x, y) ->
  return (toWord32 $ fromWord8 x `shift` (32-8) .|. fromWord32 y `shift` (-8), toWord8 $ fromWord32 y)
implementationWord FullRightShift32_16 = \(x, y) ->
  return (toWord32 $ fromWord16 x `shift` (32-16) .|. fromWord32 y `shift` (-16), toWord16 $ fromWord32 y)
implementationWord FullRightShift64_1 = \(x, y) ->
  return (toWord64 $ fromWord1 x `shift` (64-1) .|. fromWord64 y `shift` (-1), toWord1 $ fromWord64 y)
implementationWord FullRightShift64_2 = \(x, y) ->
  return (toWord64 $ fromWord2 x `shift` (64-2) .|. fromWord64 y `shift` (-2), toWord2 $ fromWord64 y)
implementationWord FullRightShift64_4 = \(x, y) ->
  return (toWord64 $ fromWord4 x `shift` (64-4) .|. fromWord64 y `shift` (-4), toWord4 $ fromWord64 y)
implementationWord FullRightShift64_8 = \(x, y) ->
  return (toWord64 $ fromWord8 x `shift` (64-8) .|. fromWord64 y `shift` (-8), toWord8 $ fromWord64 y)
implementationWord FullRightShift64_16 = \(x, y) ->
  return (toWord64 $ fromWord16 x `shift` (64-16) .|. fromWord64 y `shift` (-16), toWord16 $ fromWord64 y)
implementationWord FullRightShift64_32 = \(x, y) ->
  return (toWord64 $ fromWord32 x `shift` (64-32) .|. fromWord64 y `shift` (-32), toWord32 $ fromWord64 y)
implementationWord Leftmost8_1 = Just . fst . fst . fst
implementationWord Leftmost8_2 = Just . fst . fst
implementationWord Leftmost8_4 = Just . fst
implementationWord Leftmost16_1 = Just . fst . fst . fst . fst
implementationWord Leftmost16_2 = Just . fst . fst . fst
implementationWord Leftmost16_4 = Just . fst . fst
implementationWord Leftmost16_8 = Just . fst
implementationWord Leftmost32_1 = Just . fst . fst . fst . fst . fst
implementationWord Leftmost32_2 = Just . fst . fst . fst . fst
implementationWord Leftmost32_4 = Just . fst . fst . fst
implementationWord Leftmost32_8 = Just . fst . fst
implementationWord Leftmost32_16 = Just . fst
implementationWord Leftmost64_1 = Just . fst . fst . fst . fst . fst . fst
implementationWord Leftmost64_2 = Just . fst . fst . fst . fst . fst
implementationWord Leftmost64_4 = Just . fst . fst . fst . fst
implementationWord Leftmost64_8 = Just . fst . fst . fst
implementationWord Leftmost64_16 = Just . fst . fst
implementationWord Leftmost64_32 = Just . fst
implementationWord Rightmost8_1 = Just . snd . snd . snd
implementationWord Rightmost8_2 = Just . snd . snd
implementationWord Rightmost8_4 = Just . snd
implementationWord Rightmost16_1 = Just . snd . snd . snd . snd
implementationWord Rightmost16_2 = Just . snd . snd . snd
implementationWord Rightmost16_4 = Just . snd . snd
implementationWord Rightmost16_8 = Just . snd
implementationWord Rightmost32_1 = Just . snd . snd . snd . snd . snd
implementationWord Rightmost32_2 = Just . snd . snd . snd . snd
implementationWord Rightmost32_4 = Just . snd . snd . snd
implementationWord Rightmost32_8 = Just . snd . snd
implementationWord Rightmost32_16 = Just . snd
implementationWord Rightmost64_1 = Just . snd . snd . snd . snd . snd . snd
implementationWord Rightmost64_2 = Just . snd . snd . snd . snd . snd
implementationWord Rightmost64_4 = Just . snd . snd . snd . snd
implementationWord Rightmost64_8 = Just . snd . snd . snd
implementationWord Rightmost64_16 = Just . snd . snd
implementationWord Rightmost64_32 = Just . snd
implementationWord LeftPadLow1_8 = Just . toWord8 . fromWord1
implementationWord LeftPadLow1_16 = Just . toWord16 . fromWord1
implementationWord LeftPadLow8_16 = Just . toWord16 . fromWord8
implementationWord LeftPadLow1_32 = Just . toWord32 . fromWord1
implementationWord LeftPadLow8_32 = Just . toWord32 . fromWord8
implementationWord LeftPadLow16_32 = Just . toWord32 . fromWord16
implementationWord LeftPadLow1_64 = Just . toWord64 . fromWord1
implementationWord LeftPadLow8_64 = Just . toWord64 . fromWord8
implementationWord LeftPadLow16_64 = Just . toWord64 . fromWord16
implementationWord LeftPadLow32_64 = Just . toWord64 . fromWord32
implementationWord LeftPadHigh1_8 = \x -> Just . toWord8 $ ((-1) `shift` 1) .|. fromWord1 x
implementationWord LeftPadHigh1_16 = \x -> Just . toWord16 $ ((-1) `shift` 1) .|. fromWord1 x
implementationWord LeftPadHigh8_16 = \x -> Just . toWord16 $ ((-1) `shift` 8) .|. fromWord8 x
implementationWord LeftPadHigh1_32 = \x -> Just . toWord32 $ ((-1) `shift` 1) .|. fromWord1 x
implementationWord LeftPadHigh8_32 = \x -> Just . toWord32 $ ((-1) `shift` 8) .|. fromWord8 x
implementationWord LeftPadHigh16_32 = \x -> Just . toWord32 $ ((-1) `shift` 16) .|. fromWord16 x
implementationWord LeftPadHigh1_64 = \x -> Just . toWord64 $ ((-1) `shift` 1) .|. fromWord1 x
implementationWord LeftPadHigh8_64 = \x -> Just . toWord64 $ ((-1) `shift` 8) .|. fromWord8 x
implementationWord LeftPadHigh16_64 = \x -> Just . toWord64 $ ((-1) `shift` 16) .|. fromWord16 x
implementationWord LeftPadHigh32_64 = \x -> Just . toWord64 $ ((-1) `shift` 32) .|. fromWord32 x
implementationWord LeftExtend1_8 = Just . toWord8 . fromInt1
implementationWord LeftExtend1_16 = Just . toWord16 . fromInt1
implementationWord LeftExtend8_16 = Just . toWord16 . fromInt8
implementationWord LeftExtend1_32 = Just . toWord32 . fromInt1
implementationWord LeftExtend8_32 = Just . toWord32 . fromInt8
implementationWord LeftExtend16_32 = Just . toWord32 . fromInt16
implementationWord LeftExtend1_64 = Just . toWord64 . fromInt1
implementationWord LeftExtend8_64 = Just . toWord64 . fromInt8
implementationWord LeftExtend16_64 = Just . toWord64 . fromInt16
implementationWord LeftExtend32_64 = Just . toWord64 . fromInt32
implementationWord RightPadLow1_8 = \x -> Just . toWord8 $ fromWord1 x `shift` (8 - 1)
implementationWord RightPadLow1_16 = \x -> Just . toWord16 $ fromWord1 x `shift` (16 - 1)
implementationWord RightPadLow8_16 = \x -> Just . toWord16 $ fromWord8 x `shift` (16 - 8)
implementationWord RightPadLow1_32 = \x -> Just . toWord32 $ fromWord1 x `shift` (32 - 1)
implementationWord RightPadLow8_32 = \x -> Just . toWord32 $ fromWord8 x `shift` (32 - 8)
implementationWord RightPadLow16_32 = \x -> Just . toWord32 $ fromWord16 x `shift` (32 - 16)
implementationWord RightPadLow1_64 = \x -> Just . toWord64 $ fromWord1 x `shift` (64 - 1)
implementationWord RightPadLow8_64 = \x -> Just . toWord64 $ fromWord8 x `shift` (64 - 8)
implementationWord RightPadLow16_64 = \x -> Just . toWord64 $ fromWord16 x `shift` (64 - 16)
implementationWord RightPadLow32_64 = \x -> Just . toWord64 $ fromWord32 x `shift` (64 - 32)
implementationWord RightPadHigh1_8 = \x -> Just . toWord8 $ (fromWord1 x `shift` (8 - 1) .|. (2^(8 - 1) - 1))
implementationWord RightPadHigh1_16 = \x -> Just . toWord16 $ (fromWord1 x `shift` (16 - 1) .|. (2^(16 - 1) - 1))
implementationWord RightPadHigh8_16 = \x -> Just . toWord16 $ (fromWord8 x `shift` (16 - 8) .|. (2^(16 - 8) - 1))
implementationWord RightPadHigh1_32 = \x -> Just . toWord32 $ (fromWord1 x `shift` (32 - 1) .|. (2^(32 - 1) - 1))
implementationWord RightPadHigh8_32 = \x -> Just . toWord32 $ (fromWord8 x `shift` (32 - 8) .|. (2^(32 - 8) - 1))
implementationWord RightPadHigh16_32 = \x -> Just . toWord32 $ (fromWord16 x `shift` (32 - 16) .|. (2^(32 - 16) - 1))
implementationWord RightPadHigh1_64 = \x -> Just . toWord64 $ (fromWord1 x `shift` (64 - 1) .|. (2^(64 - 1) - 1))
implementationWord RightPadHigh8_64 = \x -> Just . toWord64 $ (fromWord8 x `shift` (64 - 8) .|. (2^(64 - 8) - 1))
implementationWord RightPadHigh16_64 = \x -> Just . toWord64 $ (fromWord16 x `shift` (64 - 16) .|. (2^(64 - 16) - 1))
implementationWord RightPadHigh32_64 = \x -> Just . toWord64 $ (fromWord32 x `shift` (64 - 32) .|. (2^(64 - 32) - 1))
implementationWord RightExtend8_16 = \x -> Just . toWord16 $ (fromWord8 x `shift` (16 - 8) .|. if odd (fromWord8 x) then (2^(16 - 8) - 1) else 0)
implementationWord RightExtend8_32 = \x -> Just . toWord32 $ (fromWord8 x `shift` (32 - 8) .|. if odd (fromWord8 x) then (2^(32 - 8) - 1) else 0)
implementationWord RightExtend16_32 = \x -> Just . toWord32 $ (fromWord16 x `shift` (32 - 16) .|. if odd (fromWord16 x) then (2^(32 - 16) - 1) else 0)
implementationWord RightExtend8_64 = \x -> Just . toWord64 $ (fromWord8 x `shift` (64 - 8) .|. if odd (fromWord8 x) then (2^(64 - 8) - 1) else 0)
implementationWord RightExtend16_64 = \x -> Just . toWord64 $ (fromWord16 x `shift` (64 - 16) .|. if odd (fromWord16 x) then (2^(64 - 16) - 1) else 0)
implementationWord RightExtend32_64 = \x -> Just . toWord64 $ (fromWord32 x `shift` (64 - 32) .|. if odd (fromWord32 x) then (2^(64 - 32) - 1) else 0)
implementationWord LeftShiftWith8 = \(w,(x,y)) -> Just . toWord8 $ (fromWord8 y `shift` fromInteger (fromWord4 x)) .|. if fromBit w then (2^(fromWord4 x) -1) else 0
implementationWord LeftShiftWith16 = \(w,(x,y)) -> Just . toWord16 $ (fromWord16 y `shift` fromInteger (fromWord4 x)) .|. if fromBit w then (2^(fromWord4 x) -1) else 0
implementationWord LeftShiftWith32 = \(w,(x,y)) -> Just . toWord32 $ (fromWord32 y `shift` fromInteger (fromWord8 x)) .|. if fromBit w then (2^(fromWord8 x) -1) else 0
implementationWord LeftShiftWith64 = \(w,(x,y)) -> Just . toWord64 $ (fromWord64 y `shift` fromInteger (fromWord8 x)) .|. if fromBit w then (2^(fromWord8 x) -1) else 0
implementationWord LeftShift8 = \(x,y) -> Just . toWord8 $ fromWord8 y `shift` fromInteger (fromWord4 x)
implementationWord LeftShift16 = \(x,y) -> Just . toWord16 $ fromWord16 y `shift` fromInteger (fromWord4 x)
implementationWord LeftShift32 = \(x,y) -> Just . toWord32 $ fromWord32 y `shift` fromInteger (fromWord8 x)
implementationWord LeftShift64 = \(x,y) -> Just . toWord64 $ fromWord64 y `shift` fromInteger (fromWord8 x)
implementationWord RightShiftWith8 = \(w,(x,y)) -> Just . toWord8 $ (fromWord8 y `shift` fromInteger (-fromWord4 x)) .|. if fromBit w then ((-1 :: Integer) `shift` fromInteger (8-fromWord4 x)) else 0
implementationWord RightShiftWith16 = \(w,(x,y)) -> Just . toWord16 $ (fromWord16 y `shift` fromInteger (-fromWord4 x)) .|. if fromBit w then ((-1 :: Integer) `shift` fromInteger (16-fromWord4 x)) else 0
implementationWord RightShiftWith32 = \(w,(x,y)) -> Just . toWord32 $ (fromWord32 y `shift` fromInteger (-fromWord8 x)) .|. if fromBit w then ((-1 :: Integer) `shift` fromInteger (32-fromWord8 x)) else 0
implementationWord RightShiftWith64 = \(w,(x,y)) -> Just . toWord64 $ (fromWord64 y `shift` fromInteger (-fromWord8 x)) .|. if fromBit w then ((-1 :: Integer) `shift` fromInteger (64-fromWord8 x)) else 0
implementationWord RightShift8 = \(x,y) -> Just . toWord8 $ fromWord8 y `shift` fromInteger (-fromWord4 x)
implementationWord RightShift16 = \(x,y) -> Just . toWord16 $ fromWord16 y `shift` fromInteger (-fromWord4 x)
implementationWord RightShift32 = \(x,y) -> Just . toWord32 $ fromWord32 y `shift` fromInteger (-fromWord8 x)
implementationWord RightShift64 = \(x,y) -> Just . toWord64 $ fromWord64 y `shift` fromInteger (-fromWord8 x)
implementationWord LeftRotate8 = \(x,y) -> Just . toWord8 . toInteger $ (fromInteger (fromWord8 y) :: W.Word8) `rotate` fromInteger (fromWord4 x)
implementationWord LeftRotate16 = \(x,y) -> Just . toWord16 . toInteger $ (fromInteger (fromWord16 y) :: W.Word16) `rotate` fromInteger (fromWord4 x)
implementationWord LeftRotate32 = \(x,y) -> Just . toWord32 . toInteger $ (fromInteger (fromWord32 y) :: W.Word32) `rotate` fromInteger (fromWord8 x)
implementationWord LeftRotate64 = \(x,y) -> Just . toWord64 . toInteger $ (fromInteger (fromWord64 y) :: W.Word64) `rotate` fromInteger (fromWord8 x)
implementationWord RightRotate8 = \(x,y) -> Just . toWord8 . toInteger $ (fromInteger (fromWord8 y) :: W.Word8) `rotate` fromInteger (-fromWord4 x)
implementationWord RightRotate16 = \(x,y) -> Just . toWord16 . toInteger $ (fromInteger (fromWord16 y) :: W.Word16) `rotate` fromInteger (-fromWord4 x)
implementationWord RightRotate32 = \(x,y) -> Just . toWord32 . toInteger $ (fromInteger (fromWord32 y) :: W.Word32) `rotate` fromInteger (-fromWord8 x)
implementationWord RightRotate64 = \(x,y) -> Just . toWord64 . toInteger $ (fromInteger (fromWord64 y) :: W.Word64) `rotate` fromInteger (-fromWord8 x)

implementationArith :: ArithJet a b -> a -> Maybe b
implementationArith One8 = const . return $ toWord8 1
implementationArith One16 = const . return $ toWord16 1
implementationArith One32 = const . return $ toWord32 1
implementationArith One64 = const . return $ toWord64 1
implementationArith Add8 = \(x, y) -> do
  let z = fromWord8 x + fromWord8 y
  return (toBit (z >= 2 ^ 8), toWord8 z)
implementationArith Add16 = \(x, y) -> do
  let z = fromWord16 x + fromWord16 y
  return (toBit (z >= 2 ^ 16), toWord16 z)
implementationArith Add32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith Add64 = \(x, y) -> do
  let z = fromWord64 x + fromWord64 y
  return (toBit (z >= 2 ^ 64), toWord64 z)
implementationArith FullAdd8 = \(c, (x, y)) -> do
  let z = fromWord8 x + fromWord8 y + fromWord1 c
  return (toBit (z >= 2 ^ 8), toWord8 z)
implementationArith FullAdd16 = \(c, (x, y)) -> do
  let z = fromWord16 x + fromWord16 y + fromWord1 c
  return (toBit (z >= 2 ^ 16), toWord16 z)
implementationArith FullAdd32 = \(c, (x, y)) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith FullAdd64 = \(c, (x, y)) -> do
  let z = fromWord64 x + fromWord64 y + fromWord1 c
  return (toBit (z >= 2 ^ 64), toWord64 z)
implementationArith FullIncrement8 = \(b, x) -> do
  let z = fromWord8 x + fromWord1 b
  return (toBit (z >= 2 ^ 8), toWord8 z)
implementationArith FullIncrement16 = \(b, x) -> do
  let z = fromWord16 x + fromWord1 b
  return (toBit (z >= 2 ^ 16), toWord16 z)
implementationArith FullIncrement32 = \(b, x) -> do
  let z = fromWord32 x + fromWord1 b
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith FullIncrement64 = \(b, x) -> do
  let z = fromWord64 x + fromWord1 b
  return (toBit (z >= 2 ^ 64), toWord64 z)
implementationArith Increment8 = \x -> do
  let z = fromWord8 x + 1
  return (toBit (z >= 2 ^ 8), toWord8 z)
implementationArith Increment16 = \x -> do
  let z = fromWord16 x + 1
  return (toBit (z >= 2 ^ 16), toWord16 z)
implementationArith Increment32 = \x -> do
  let z = fromWord32 x + 1
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith Increment64 = \x -> do
  let z = fromWord64 x + 1
  return (toBit (z >= 2 ^ 64), toWord64 z)
implementationArith Subtract8 = \(x, y) -> do
  let z = fromWord8 x - fromWord8 y
  return (toBit (z < 0), toWord8 z)
implementationArith Subtract16 = \(x, y) -> do
  let z = fromWord16 x - fromWord16 y
  return (toBit (z < 0), toWord16 z)
implementationArith Subtract32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementationArith Subtract64 = \(x, y) -> do
  let z = fromWord64 x - fromWord64 y
  return (toBit (z < 0), toWord64 z)
implementationArith FullSubtract8 = \(b, (x, y)) -> do
  let z = fromWord8 x - fromWord8 y - fromWord1 b
  return (toBit (z < 0), toWord8 z)
implementationArith FullSubtract16 = \(b, (x, y)) -> do
  let z = fromWord16 x - fromWord16 y - fromWord1 b
  return (toBit (z < 0), toWord16 z)
implementationArith FullSubtract32 = \(b, (x, y)) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementationArith FullSubtract64 = \(b, (x, y)) -> do
  let z = fromWord64 x - fromWord64 y - fromWord1 b
  return (toBit (z < 0), toWord64 z)
implementationArith Negate8 = \x -> do
  let z = - fromWord8 x
  return (toBit (z < 0), toWord8 z)
implementationArith Negate16 = \x -> do
  let z = - fromWord16 x
  return (toBit (z < 0), toWord16 z)
implementationArith Negate32 = \x -> do
  let z = - fromWord32 x
  return (toBit (z < 0), toWord32 z)
implementationArith Negate64 = \x -> do
  let z = - fromWord64 x
  return (toBit (z < 0), toWord64 z)
implementationArith FullDecrement8 = \(b, x) -> do
  let z = fromWord8 x - fromWord1 b
  return (toBit (z < 0), toWord8 z)
implementationArith FullDecrement16 = \(b, x) -> do
  let z = fromWord16 x - fromWord1 b
  return (toBit (z < 0), toWord16 z)
implementationArith FullDecrement32 = \(b, x) -> do
  let z = fromWord32 x - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementationArith FullDecrement64 = \(b, x) -> do
  let z = fromWord64 x - fromWord1 b
  return (toBit (z < 0), toWord64 z)
implementationArith Decrement8 = \x -> do
  let z = fromWord8 x - 1
  return (toBit (z < 0), toWord8 z)
implementationArith Decrement16 = \x -> do
  let z = fromWord16 x - 1
  return (toBit (z < 0), toWord16 z)
implementationArith Decrement32 = \x -> do
  let z = fromWord32 x - 1
  return (toBit (z < 0), toWord32 z)
implementationArith Decrement64 = \x -> do
  let z = fromWord64 x - 1
  return (toBit (z < 0), toWord64 z)
implementationArith Multiply8 = \(x, y) -> do
  let z = fromWord8 x * fromWord8 y
  return (toWord16 z)
implementationArith Multiply16 = \(x, y) -> do
  let z = fromWord16 x * fromWord16 y
  return (toWord32 z)
implementationArith Multiply32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementationArith Multiply64 = \(x, y) -> do
  let z = fromWord64 x * fromWord64 y
  return (toWord128 z)
implementationArith FullMultiply8 = \((x, y), (a, b)) -> do
  let z = fromWord8 x * fromWord8 y + fromWord8 a + fromWord8 b
  return (toWord16 z)
implementationArith FullMultiply16 = \((x, y), (a, b)) -> do
  let z = fromWord16 x * fromWord16 y + fromWord16 a + fromWord16 b
  return (toWord32 z)
implementationArith FullMultiply32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)
implementationArith FullMultiply64 = \((x, y), (a, b)) -> do
  let z = fromWord64 x * fromWord64 y + fromWord64 a + fromWord64 b
  return (toWord128 z)
implementationArith IsZero8 = \x -> do
  let z = fromWord8 x == 0
  return (toBit z)
implementationArith IsZero16 = \x -> do
  let z = fromWord16 x == 0
  return (toBit z)
implementationArith IsZero32 = \x -> do
  let z = fromWord32 x == 0
  return (toBit z)
implementationArith IsZero64 = \x -> do
  let z = fromWord64 x == 0
  return (toBit z)
implementationArith IsOne8 = \x -> do
  let z = fromWord8 x == 1
  return (toBit z)
implementationArith IsOne16 = \x -> do
  let z = fromWord16 x == 1
  return (toBit z)
implementationArith IsOne32 = \x -> do
  let z = fromWord32 x == 1
  return (toBit z)
implementationArith IsOne64 = \x -> do
  let z = fromWord64 x == 1
  return (toBit z)
implementationArith Le8 = \(x, y) -> do
  let z = fromWord8 x <= fromWord8 y
  return (toBit z)
implementationArith Le16 = \(x, y) -> do
  let z = fromWord16 x <= fromWord16 y
  return (toBit z)
implementationArith Le32 = \(x, y) -> do
  let z = fromWord32 x <= fromWord32 y
  return (toBit z)
implementationArith Le64 = \(x, y) -> do
  let z = fromWord64 x <= fromWord64 y
  return (toBit z)
implementationArith Lt8 = \(x, y) -> do
  let z = fromWord8 x < fromWord8 y
  return (toBit z)
implementationArith Lt16 = \(x, y) -> do
  let z = fromWord16 x < fromWord16 y
  return (toBit z)
implementationArith Lt32 = \(x, y) -> do
  let z = fromWord32 x < fromWord32 y
  return (toBit z)
implementationArith Lt64 = \(x, y) -> do
  let z = fromWord64 x < fromWord64 y
  return (toBit z)
implementationArith Min8 = \(x, y) -> do
  let z = Prelude.min (fromWord8 x) (fromWord8 y)
  return (toWord8 z)
implementationArith Min16 = \(x, y) -> do
  let z = Prelude.min (fromWord16 x) (fromWord16 y)
  return (toWord16 z)
implementationArith Min32 = \(x, y) -> do
  let z = Prelude.min (fromWord32 x) (fromWord32 y)
  return (toWord32 z)
implementationArith Min64 = \(x, y) -> do
  let z = Prelude.min (fromWord64 x) (fromWord64 y)
  return (toWord64 z)
implementationArith Max8 = \(x, y) -> do
  let z = Prelude.max (fromWord8 x) (fromWord8 y)
  return (toWord8 z)
implementationArith Max16 = \(x, y) -> do
  let z = Prelude.max (fromWord16 x) (fromWord16 y)
  return (toWord16 z)
implementationArith Max32 = \(x, y) -> do
  let z = Prelude.max (fromWord32 x) (fromWord32 y)
  return (toWord32 z)
implementationArith Max64 = \(x, y) -> do
  let z = Prelude.max (fromWord64 x) (fromWord64 y)
  return (toWord64 z)
implementationArith Median8 = \(x, (y, z)) -> do
  let r = median (fromWord8 x) (fromWord8 y) (fromWord8 z)
  return (toWord8 r)
implementationArith Median16 = \(x, (y, z)) -> do
  let r = median (fromWord16 x) (fromWord16 y) (fromWord16 z)
  return (toWord16 r)
implementationArith Median32 = \(x, (y, z)) -> do
  let r = median (fromWord32 x) (fromWord32 y) (fromWord32 z)
  return (toWord32 r)
implementationArith Median64 = \(x, (y, z)) -> do
  let r = median (fromWord64 x) (fromWord64 y) (fromWord64 z)
  return (toWord64 r)
implementationArith DivMod8 = \(x, y) -> do
  let (d,m) = Prelude.divMod (fromWord8 x) (fromWord8 y)
  return (if 0 == fromWord8 y then (y, x) else (toWord8 d, toWord8 m))
implementationArith DivMod16 = \(x, y) -> do
  let (d,m) = Prelude.divMod (fromWord16 x) (fromWord16 y)
  return (if 0 == fromWord16 y then (y, x) else (toWord16 d, toWord16 m))
implementationArith DivMod32 = \(x, y) -> do
  let (d,m) = Prelude.divMod (fromWord32 x) (fromWord32 y)
  return (if 0 == fromWord32 y then (y, x) else (toWord32 d, toWord32 m))
implementationArith DivMod64 = \(x, y) -> do
  let (d,m) = Prelude.divMod (fromWord64 x) (fromWord64 y)
  return (if 0 == fromWord64 y then (y, x) else (toWord64 d, toWord64 m))
implementationArith Divide8 = \(x, y) -> do
  let z = Prelude.div (fromWord8 x) (fromWord8 y)
  return (if 0 == fromWord8 y then y else toWord8 z)
implementationArith Divide16 = \(x, y) -> do
  let z = Prelude.div (fromWord16 x) (fromWord16 y)
  return (if 0 == fromWord16 y then y else toWord16 z)
implementationArith Divide32 = \(x, y) -> do
  let z = Prelude.div (fromWord32 x) (fromWord32 y)
  return (if 0 == fromWord32 y then y else toWord32 z)
implementationArith Divide64 = \(x, y) -> do
  let z = Prelude.div (fromWord64 x) (fromWord64 y)
  return (if 0 == fromWord64 y then y else toWord64 z)
implementationArith Modulo8 = \(x, y) -> do
  let z = Prelude.mod (fromWord8 x) (fromWord8 y)
  return (if 0 == fromWord8 y then x else toWord8 z)
implementationArith Modulo16 = \(x, y) -> do
  let z = Prelude.mod (fromWord16 x) (fromWord16 y)
  return (if 0 == fromWord16 y then x else toWord16 z)
implementationArith Modulo32 = \(x, y) -> do
  let z = Prelude.mod (fromWord32 x) (fromWord32 y)
  return (if 0 == fromWord32 y then x else toWord32 z)
implementationArith Modulo64 = \(x, y) -> do
  let z = Prelude.mod (fromWord64 x) (fromWord64 y)
  return (if 0 == fromWord64 y then x else toWord64 z)
implementationArith Divides8 = \(x, y) -> do
  let z = Prelude.mod (fromWord8 y) (fromWord8 x)
  return (toBit (0 == if 0 == fromWord8 x then fromWord8 y else z))
implementationArith Divides16 = \(x, y) -> do
  let z = Prelude.mod (fromWord16 y) (fromWord16 x)
  return (toBit (0 == if 0 == fromWord16 x then fromWord16 y else z))
implementationArith Divides32 = \(x, y) -> do
  let z = Prelude.mod (fromWord32 y) (fromWord32 x)
  return (toBit (0 == if 0 == fromWord32 x then fromWord32 y else z))
implementationArith Divides64 = \(x, y) -> do
  let z = Prelude.mod (fromWord64 y) (fromWord64 x)
  return (toBit (0 == if 0 == fromWord64 x then fromWord64 y else z))
implementationArith DivMod128_64 = \(x0, y0) -> do
  let x = fromWord128 x0
      y = fromWord64 y0
      (d,m) = Prelude.divMod x y
  return (if 2^63 <= y && x < y * 2^64 then (toWord64 d, toWord64 m) else (toWord64 (-1), toWord64 (-1)))

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
implementationSecp256k1 GejEquiv = \(a,b) -> return . toBit $ Spec.gej_equiv (fromGEJ a) (fromGEJ b)
implementationSecp256k1 GejGeEquiv = \(a,b) -> return . toBit $ Spec.gej_ge_equiv (fromGEJ a) (fromGE b)
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
getJetBit = getCatalogue coreCatalogue

coreCatalogue :: Catalogue (SomeArrow CoreJet)
coreCatalogue = Shelf
  [ someArrowMap WordJet <$> wordBook
  , someArrowMap ArithJet <$> arithBook
  , someArrowMap HashJet <$> hashBook
  , someArrowMap Secp256k1Jet <$> secp256k1Book
  , someArrowMap SignatureJet <$> signatureBook
  , Missing
  , someArrowMap BitcoinJet <$> bitcoinBook
  ]
wordBook = Shelf
  [ Item $ SomeArrow Verify
  , lowBook
  , highBook
  , complementBook
  , andBook
  , orBook
  , xorBook
  , majBook
  , xorXorBook
  , chBook
  , someBook
  , allBook
  , eqBook
  , fullLeftShiftBook
  , fullRightShiftBook
  , leftmostBook
  , rightmostBook
  , leftPadLowBook
  , leftPadHighBook
  , leftExtendBook
  , rightPadLowBook
  , rightPadHighBook
  , rightExtendBook
  , leftShiftWithBook
  , rightShiftWithBook
  , leftShiftBook
  , rightShiftBook
  , leftRotateBook
  , rightRotateBook
  ]
lowBook = Shelf
  [ Item $ SomeArrow Low1
  , Missing
  , Item $ SomeArrow Low8
  , Item $ SomeArrow Low16
  , Item $ SomeArrow Low32
  , Item $ SomeArrow Low64
  ]
highBook = Shelf
  [ Item $ SomeArrow High1
  , Missing
  , Item $ SomeArrow High8
  , Item $ SomeArrow High16
  , Item $ SomeArrow High32
  , Item $ SomeArrow High64
  ]
complementBook = Shelf
  [ Item $ SomeArrow Complement1
  , Missing
  , Item $ SomeArrow Complement8
  , Item $ SomeArrow Complement16
  , Item $ SomeArrow Complement32
  , Item $ SomeArrow Complement64
  ]
andBook = Shelf
  [ Item $ SomeArrow And1
  , Missing
  , Item $ SomeArrow And8
  , Item $ SomeArrow And16
  , Item $ SomeArrow And32
  , Item $ SomeArrow And64
  ]
orBook = Shelf
  [ Item $ SomeArrow Or1
  , Missing
  , Item $ SomeArrow Or8
  , Item $ SomeArrow Or16
  , Item $ SomeArrow Or32
  , Item $ SomeArrow Or64
  ]
xorBook = Shelf
  [ Item $ SomeArrow Xor1
  , Missing
  , Item $ SomeArrow Xor8
  , Item $ SomeArrow Xor16
  , Item $ SomeArrow Xor32
  , Item $ SomeArrow Xor64
  ]
majBook = Shelf
  [ Item $ SomeArrow Maj1
  , Missing
  , Item $ SomeArrow Maj8
  , Item $ SomeArrow Maj16
  , Item $ SomeArrow Maj32
  , Item $ SomeArrow Maj64
  ]
xorXorBook = Shelf
  [ Item $ SomeArrow XorXor1
  , Missing
  , Item $ SomeArrow XorXor8
  , Item $ SomeArrow XorXor16
  , Item $ SomeArrow XorXor32
  , Item $ SomeArrow XorXor64
  ]
chBook = Shelf
  [ Item $ SomeArrow Ch1
  , Missing
  , Item $ SomeArrow Ch8
  , Item $ SomeArrow Ch16
  , Item $ SomeArrow Ch32
  , Item $ SomeArrow Ch64
  ]
someBook = Shelf
  [ Item $ SomeArrow Some1
  , Missing
  , Item $ SomeArrow Some8
  , Item $ SomeArrow Some16
  , Item $ SomeArrow Some32
  , Item $ SomeArrow Some64
  ]
allBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow All8
  , Item $ SomeArrow All16
  , Item $ SomeArrow All32
  , Item $ SomeArrow All64
  ]
eqBook = Shelf
  [ Item $ SomeArrow Eq1
  , Missing
  , Item $ SomeArrow Eq8
  , Item $ SomeArrow Eq16
  , Item $ SomeArrow Eq32
  , Item $ SomeArrow Eq64
  , Missing
  , Item $ SomeArrow Eq256
  ]
fullLeftShiftBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow FullLeftShift8_1
    , Item $ SomeArrow FullLeftShift16_1
    , Item $ SomeArrow FullLeftShift32_1
    , Item $ SomeArrow FullLeftShift64_1
    ]
  , Shelf
    [ Missing
    , Item $ SomeArrow FullLeftShift8_2
    , Item $ SomeArrow FullLeftShift16_2
    , Item $ SomeArrow FullLeftShift32_2
    , Item $ SomeArrow FullLeftShift64_2
    ]
  , Shelf
    [ Item $ SomeArrow FullLeftShift8_4
    , Item $ SomeArrow FullLeftShift16_4
    , Item $ SomeArrow FullLeftShift32_4
    , Item $ SomeArrow FullLeftShift64_4
    ]
  , Shelf
    [ Item $ SomeArrow FullLeftShift16_8
    , Item $ SomeArrow FullLeftShift32_8
    , Item $ SomeArrow FullLeftShift64_8
    ]
  , Shelf
    [ Item $ SomeArrow FullLeftShift32_16
    , Item $ SomeArrow FullLeftShift64_16
    ]
  , Shelf
    [ Item $ SomeArrow FullLeftShift64_32
    ]
  ]
fullRightShiftBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow FullRightShift8_1
    , Item $ SomeArrow FullRightShift16_1
    , Item $ SomeArrow FullRightShift32_1
    , Item $ SomeArrow FullRightShift64_1
    ]
  , Shelf
    [ Missing
    , Item $ SomeArrow FullRightShift8_2
    , Item $ SomeArrow FullRightShift16_2
    , Item $ SomeArrow FullRightShift32_2
    , Item $ SomeArrow FullRightShift64_2
    ]
  , Shelf
    [ Item $ SomeArrow FullRightShift8_4
    , Item $ SomeArrow FullRightShift16_4
    , Item $ SomeArrow FullRightShift32_4
    , Item $ SomeArrow FullRightShift64_4
    ]
  , Shelf
    [ Item $ SomeArrow FullRightShift16_8
    , Item $ SomeArrow FullRightShift32_8
    , Item $ SomeArrow FullRightShift64_8
    ]
  , Shelf
    [ Item $ SomeArrow FullRightShift32_16
    , Item $ SomeArrow FullRightShift64_16
    ]
  , Shelf
    [ Item $ SomeArrow FullRightShift64_32
    ]
  ]
leftmostBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow Leftmost8_1
    , Item $ SomeArrow Leftmost16_1
    , Item $ SomeArrow Leftmost32_1
    , Item $ SomeArrow Leftmost64_1
    ]
  , Shelf
    [ Missing
    , Item $ SomeArrow Leftmost8_2
    , Item $ SomeArrow Leftmost16_2
    , Item $ SomeArrow Leftmost32_2
    , Item $ SomeArrow Leftmost64_2
    ]
  , Shelf
    [ Item $ SomeArrow Leftmost8_4
    , Item $ SomeArrow Leftmost16_4
    , Item $ SomeArrow Leftmost32_4
    , Item $ SomeArrow Leftmost64_4
    ]
  , Shelf
    [ Item $ SomeArrow Leftmost16_8
    , Item $ SomeArrow Leftmost32_8
    , Item $ SomeArrow Leftmost64_8
    ]
  , Shelf
    [ Item $ SomeArrow Leftmost32_16
    , Item $ SomeArrow Leftmost64_16
    ]
  , Shelf
    [ Item $ SomeArrow Leftmost64_32
    ]
  ]
rightmostBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow Rightmost8_1
    , Item $ SomeArrow Rightmost16_1
    , Item $ SomeArrow Rightmost32_1
    , Item $ SomeArrow Rightmost64_1
    ]
  , Shelf
    [ Missing
    , Item $ SomeArrow Rightmost8_2
    , Item $ SomeArrow Rightmost16_2
    , Item $ SomeArrow Rightmost32_2
    , Item $ SomeArrow Rightmost64_2
    ]
  , Shelf
    [ Item $ SomeArrow Rightmost8_4
    , Item $ SomeArrow Rightmost16_4
    , Item $ SomeArrow Rightmost32_4
    , Item $ SomeArrow Rightmost64_4
    ]
  , Shelf
    [ Item $ SomeArrow Rightmost16_8
    , Item $ SomeArrow Rightmost32_8
    , Item $ SomeArrow Rightmost64_8
    ]
  , Shelf
    [ Item $ SomeArrow Rightmost32_16
    , Item $ SomeArrow Rightmost64_16
    ]
  , Shelf
    [ Item $ SomeArrow Rightmost64_32
    ]
  ]
leftPadLowBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow LeftPadLow1_8
    , Item $ SomeArrow LeftPadLow1_16
    , Item $ SomeArrow LeftPadLow1_32
    , Item $ SomeArrow LeftPadLow1_64
    ]
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow LeftPadLow8_16
    , Item $ SomeArrow LeftPadLow8_32
    , Item $ SomeArrow LeftPadLow8_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftPadLow16_32
    , Item $ SomeArrow LeftPadLow16_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftPadLow32_64
    ]
  ]
leftPadHighBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow LeftPadHigh1_8
    , Item $ SomeArrow LeftPadHigh1_16
    , Item $ SomeArrow LeftPadHigh1_32
    , Item $ SomeArrow LeftPadHigh1_64
    ]
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow LeftPadHigh8_16
    , Item $ SomeArrow LeftPadHigh8_32
    , Item $ SomeArrow LeftPadHigh8_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftPadHigh16_32
    , Item $ SomeArrow LeftPadHigh16_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftPadHigh32_64
    ]
  ]
leftExtendBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow LeftExtend1_8
    , Item $ SomeArrow LeftExtend1_16
    , Item $ SomeArrow LeftExtend1_32
    , Item $ SomeArrow LeftExtend1_64
    ]
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow LeftExtend8_16
    , Item $ SomeArrow LeftExtend8_32
    , Item $ SomeArrow LeftExtend8_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftExtend16_32
    , Item $ SomeArrow LeftExtend16_64
    ]
  , Shelf
    [ Item $ SomeArrow LeftExtend32_64
    ]
  ]
rightPadLowBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow RightPadLow1_8
    , Item $ SomeArrow RightPadLow1_16
    , Item $ SomeArrow RightPadLow1_32
    , Item $ SomeArrow RightPadLow1_64
    ]
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow RightPadLow8_16
    , Item $ SomeArrow RightPadLow8_32
    , Item $ SomeArrow RightPadLow8_64
    ]
  , Shelf
    [ Item $ SomeArrow RightPadLow16_32
    , Item $ SomeArrow RightPadLow16_64
    ]
  , Shelf
    [ Item $ SomeArrow RightPadLow32_64
    ]
  ]
rightPadHighBook = Shelf
  [ Shelf
    [ Missing
    , Missing
    , Item $ SomeArrow RightPadHigh1_8
    , Item $ SomeArrow RightPadHigh1_16
    , Item $ SomeArrow RightPadHigh1_32
    , Item $ SomeArrow RightPadHigh1_64
    ]
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow RightPadHigh8_16
    , Item $ SomeArrow RightPadHigh8_32
    , Item $ SomeArrow RightPadHigh8_64
    ]
  , Shelf
    [ Item $ SomeArrow RightPadHigh16_32
    , Item $ SomeArrow RightPadHigh16_64
    ]
  , Shelf
    [ Item $ SomeArrow RightPadHigh32_64
    ]
  ]
rightExtendBook = Shelf
  [ Missing
  , Missing
  , Missing
  , Shelf
    [ Item $ SomeArrow RightExtend8_16
    , Item $ SomeArrow RightExtend8_32
    , Item $ SomeArrow RightExtend8_64
    ]
  , Shelf
    [ Item $ SomeArrow RightExtend16_32
    , Item $ SomeArrow RightExtend16_64
    ]
  , Shelf
    [ Item $ SomeArrow RightExtend32_64
    ]
  ]
leftShiftWithBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow LeftShiftWith8
  , Item $ SomeArrow LeftShiftWith16
  , Item $ SomeArrow LeftShiftWith32
  , Item $ SomeArrow LeftShiftWith64
  ]
rightShiftWithBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow RightShiftWith8
  , Item $ SomeArrow RightShiftWith16
  , Item $ SomeArrow RightShiftWith32
  , Item $ SomeArrow RightShiftWith64
  ]
leftShiftBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow LeftShift8
  , Item $ SomeArrow LeftShift16
  , Item $ SomeArrow LeftShift32
  , Item $ SomeArrow LeftShift64
  ]
rightShiftBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow RightShift8
  , Item $ SomeArrow RightShift16
  , Item $ SomeArrow RightShift32
  , Item $ SomeArrow RightShift64
  ]
leftRotateBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow LeftRotate8
  , Item $ SomeArrow LeftRotate16
  , Item $ SomeArrow LeftRotate32
  , Item $ SomeArrow LeftRotate64
  ]
rightRotateBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow RightRotate8
  , Item $ SomeArrow RightRotate16
  , Item $ SomeArrow RightRotate32
  , Item $ SomeArrow RightRotate64
  ]
arithBook = Shelf
  [ oneBook
  , fullAddBook
  , addBook
  , fullIncrementBook
  , incrementBook
  , Missing
  , fullSubtractBook
  , subtractBook
  , negateBook
  , fullDecrementBook
  , decrementBook
  , fullMultiplyBook
  , multiplyBook
  , isZeroBook
  , isOneBook
  , leBook
  , ltBook
  , minBook
  , maxBook
  , medianBook
  , div2n1nBook
  , divModBook
  , divideBook
  , moduloBook
  , dividesBook
  ]
oneBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow One8
  , Item $ SomeArrow One16
  , Item $ SomeArrow One32
  , Item $ SomeArrow One64
  ]
addBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Add8
  , Item $ SomeArrow Add16
  , Item $ SomeArrow Add32
  , Item $ SomeArrow Add64
  ]
fullAddBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow FullAdd8
  , Item $ SomeArrow FullAdd16
  , Item $ SomeArrow FullAdd32
  , Item $ SomeArrow FullAdd64
  ]
fullIncrementBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow FullIncrement8
  , Item $ SomeArrow FullIncrement16
  , Item $ SomeArrow FullIncrement32
  , Item $ SomeArrow FullIncrement64
  ]
incrementBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Increment8
  , Item $ SomeArrow Increment16
  , Item $ SomeArrow Increment32
  , Item $ SomeArrow Increment64
  ]
subtractBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Subtract8
  , Item $ SomeArrow Subtract16
  , Item $ SomeArrow Subtract32
  , Item $ SomeArrow Subtract64
  ]
fullSubtractBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow FullSubtract8
  , Item $ SomeArrow FullSubtract16
  , Item $ SomeArrow FullSubtract32
  , Item $ SomeArrow FullSubtract64
  ]
negateBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Negate8
  , Item $ SomeArrow Negate16
  , Item $ SomeArrow Negate32
  , Item $ SomeArrow Negate64
  ]
fullDecrementBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow FullDecrement8
  , Item $ SomeArrow FullDecrement16
  , Item $ SomeArrow FullDecrement32
  , Item $ SomeArrow FullDecrement64
  ]
decrementBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Decrement8
  , Item $ SomeArrow Decrement16
  , Item $ SomeArrow Decrement32
  , Item $ SomeArrow Decrement64
  ]
multiplyBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Multiply8
  , Item $ SomeArrow Multiply16
  , Item $ SomeArrow Multiply32
  , Item $ SomeArrow Multiply64
  ]
fullMultiplyBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow FullMultiply8
  , Item $ SomeArrow FullMultiply16
  , Item $ SomeArrow FullMultiply32
  , Item $ SomeArrow FullMultiply64
  ]
isZeroBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow IsZero8
  , Item $ SomeArrow IsZero16
  , Item $ SomeArrow IsZero32
  , Item $ SomeArrow IsZero64
  ]
isOneBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow IsOne8
  , Item $ SomeArrow IsOne16
  , Item $ SomeArrow IsOne32
  , Item $ SomeArrow IsOne64
  ]
leBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Le8
  , Item $ SomeArrow Le16
  , Item $ SomeArrow Le32
  , Item $ SomeArrow Le64
  ]
ltBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Lt8
  , Item $ SomeArrow Lt16
  , Item $ SomeArrow Lt32
  , Item $ SomeArrow Lt64
  ]
minBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Min8
  , Item $ SomeArrow Min16
  , Item $ SomeArrow Min32
  , Item $ SomeArrow Min64
  ]
maxBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Max8
  , Item $ SomeArrow Max16
  , Item $ SomeArrow Max32
  , Item $ SomeArrow Max64
  ]
medianBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Median8
  , Item $ SomeArrow Median16
  , Item $ SomeArrow Median32
  , Item $ SomeArrow Median64
  ]
div2n1nBook = Shelf
  [ Missing
  , Missing
  , Missing
  , Missing
  , Missing
  , Item $ SomeArrow DivMod128_64
  ]
divModBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow DivMod8
  , Item $ SomeArrow DivMod16
  , Item $ SomeArrow DivMod32
  , Item $ SomeArrow DivMod64
  ]
divideBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Divide8
  , Item $ SomeArrow Divide16
  , Item $ SomeArrow Divide32
  , Item $ SomeArrow Divide64
  ]
moduloBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Modulo8
  , Item $ SomeArrow Modulo16
  , Item $ SomeArrow Modulo32
  , Item $ SomeArrow Modulo64
  ]
dividesBook = Shelf
  [ Missing
  , Missing
  , Item $ SomeArrow Divides8
  , Item $ SomeArrow Divides16
  , Item $ SomeArrow Divides32
  , Item $ SomeArrow Divides64
  ]
hashBook = Shelf [sha2Book]
sha2Book = Shelf
  [ Item $ SomeArrow Sha256Block
  , Item $ SomeArrow Sha256Iv
  , sha2AddBook
  , Item $ SomeArrow Sha256Ctx8AddBuffer511
  , Item $ SomeArrow Sha256Ctx8Finalize
  , Item $ SomeArrow Sha256Ctx8Init
  ]
sha2AddBook = book
  [ SomeArrow Sha256Ctx8Add1
  , SomeArrow Sha256Ctx8Add2
  , SomeArrow Sha256Ctx8Add4
  , SomeArrow Sha256Ctx8Add8
  , SomeArrow Sha256Ctx8Add16
  , SomeArrow Sha256Ctx8Add32
  , SomeArrow Sha256Ctx8Add64
  , SomeArrow Sha256Ctx8Add128
  , SomeArrow Sha256Ctx8Add256
  , SomeArrow Sha256Ctx8Add512
  ]
secp256k1Book = Shelf
  [ Shelf [Item $ SomeArrow PointVerify1]
  , Item $ SomeArrow Decompress
  , Shelf [Item $ SomeArrow LinearVerify1]
  , Shelf [Item $ SomeArrow LinearCombination1]
  , Item $ SomeArrow Scale
  , Item $ SomeArrow Generate
  , Item $ SomeArrow GejInfinity
  , Item $ SomeArrow GejNormalize
  , Item $ SomeArrow GejNegate
  , Item $ SomeArrow GeNegate
  , Item $ SomeArrow GejDouble
  , Item $ SomeArrow GejAdd
  , Item $ SomeArrow GejGeAddEx
  , Item $ SomeArrow GejGeAdd
  , Item $ SomeArrow GejRescale
  , Item $ SomeArrow GejIsInfinity
  , Item $ SomeArrow GejEquiv
  , Item $ SomeArrow GejGeEquiv
  , Item $ SomeArrow GejXEquiv
  , Item $ SomeArrow GejYIsOdd
  , Item $ SomeArrow GejIsOnCurve
  , Item $ SomeArrow GeIsOnCurve
  , Item $ SomeArrow ScalarNormalize
  , Item $ SomeArrow ScalarNegate
  , Item $ SomeArrow ScalarAdd
  , Item $ SomeArrow ScalarSquare
  , Item $ SomeArrow ScalarMultiply
  , Item $ SomeArrow ScalarMultiplyLambda
  , Item $ SomeArrow ScalarInvert
  , Item $ SomeArrow ScalarIsZero
  , Missing
  , Missing
  , Missing
  , Missing
  , Item $ SomeArrow FeNormalize
  , Item $ SomeArrow FeNegate
  , Item $ SomeArrow FeAdd
  , Item $ SomeArrow FeSquare
  , Item $ SomeArrow FeMultiply
  , Item $ SomeArrow FeMultiplyBeta
  , Item $ SomeArrow FeInvert
  , Item $ SomeArrow FeSquareRoot
  , Item $ SomeArrow FeIsZero
  , Item $ SomeArrow FeIsOdd
  ]
signatureBook = book
  [ SomeArrow CheckSigVerify
  , SomeArrow Bip0340Verify
  ]
bitcoinBook = book
  [ SomeArrow ParseLock
  , SomeArrow ParseSequence
  ]

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit (WordJet x) = putPositive 1 . putJetBitWord x
putJetBit (ArithJet x) = putPositive 2 . putJetBitArith x
putJetBit (HashJet x) = putPositive 3 . putJetBitHash x
putJetBit (Secp256k1Jet x) = putPositive 4 . putJetBitSecp256k1 x
putJetBit (SignatureJet x) = putPositive 5 . putJetBitSignature x
putJetBit (BitcoinJet x) = putPositive 7 . putJetBitBitcoin x

putJetBitWord :: WordJet a b -> DList Bool
putJetBitWord Verify = putPositive 1
putJetBitWord Low1   = putPositive 2 . putPositive 1
putJetBitWord Low8   = putPositive 2 . putPositive 3
putJetBitWord Low16  = putPositive 2 . putPositive 4
putJetBitWord Low32  = putPositive 2 . putPositive 5
putJetBitWord Low64  = putPositive 2 . putPositive 6
putJetBitWord High1   = putPositive 3 . putPositive 1
putJetBitWord High8   = putPositive 3 . putPositive 3
putJetBitWord High16  = putPositive 3 . putPositive 4
putJetBitWord High32  = putPositive 3 . putPositive 5
putJetBitWord High64  = putPositive 3 . putPositive 6
putJetBitWord Complement1   = putPositive 4 . putPositive 1
putJetBitWord Complement8   = putPositive 4 . putPositive 3
putJetBitWord Complement16  = putPositive 4 . putPositive 4
putJetBitWord Complement32  = putPositive 4 . putPositive 5
putJetBitWord Complement64  = putPositive 4 . putPositive 6
putJetBitWord And1   = putPositive 5 . putPositive 1
putJetBitWord And8   = putPositive 5 . putPositive 3
putJetBitWord And16  = putPositive 5 . putPositive 4
putJetBitWord And32  = putPositive 5 . putPositive 5
putJetBitWord And64  = putPositive 5 . putPositive 6
putJetBitWord Or1   = putPositive 6 . putPositive 1
putJetBitWord Or8   = putPositive 6 . putPositive 3
putJetBitWord Or16  = putPositive 6 . putPositive 4
putJetBitWord Or32  = putPositive 6 . putPositive 5
putJetBitWord Or64  = putPositive 6 . putPositive 6
putJetBitWord Xor1   = putPositive 7 . putPositive 1
putJetBitWord Xor8   = putPositive 7 . putPositive 3
putJetBitWord Xor16  = putPositive 7 . putPositive 4
putJetBitWord Xor32  = putPositive 7 . putPositive 5
putJetBitWord Xor64  = putPositive 7 . putPositive 6
putJetBitWord Maj1   = putPositive 8 . putPositive 1
putJetBitWord Maj8   = putPositive 8 . putPositive 3
putJetBitWord Maj16  = putPositive 8 . putPositive 4
putJetBitWord Maj32  = putPositive 8 . putPositive 5
putJetBitWord Maj64  = putPositive 8 . putPositive 6
putJetBitWord XorXor1   = putPositive 9 . putPositive 1
putJetBitWord XorXor8   = putPositive 9 . putPositive 3
putJetBitWord XorXor16  = putPositive 9 . putPositive 4
putJetBitWord XorXor32  = putPositive 9 . putPositive 5
putJetBitWord XorXor64  = putPositive 9 . putPositive 6
putJetBitWord Ch1   = putPositive 10 . putPositive 1
putJetBitWord Ch8   = putPositive 10 . putPositive 3
putJetBitWord Ch16  = putPositive 10 . putPositive 4
putJetBitWord Ch32  = putPositive 10 . putPositive 5
putJetBitWord Ch64  = putPositive 10 . putPositive 6
putJetBitWord Some1   = putPositive 11 . putPositive 1
putJetBitWord Some8   = putPositive 11 . putPositive 3
putJetBitWord Some16  = putPositive 11 . putPositive 4
putJetBitWord Some32  = putPositive 11 . putPositive 5
putJetBitWord Some64  = putPositive 11 . putPositive 6
putJetBitWord All8   = putPositive 12 . putPositive 3
putJetBitWord All16  = putPositive 12 . putPositive 4
putJetBitWord All32  = putPositive 12 . putPositive 5
putJetBitWord All64  = putPositive 12 . putPositive 6
putJetBitWord Eq1    = putPositive 13 . putPositive 1
putJetBitWord Eq8    = putPositive 13 . putPositive 3
putJetBitWord Eq16   = putPositive 13 . putPositive 4
putJetBitWord Eq32   = putPositive 13 . putPositive 5
putJetBitWord Eq64   = putPositive 13 . putPositive 6
putJetBitWord Eq256  = putPositive 13 . putPositive 8
putJetBitWord FullLeftShift8_1  = putPositive 14 . putPositive 1 . putPositive 3
putJetBitWord FullLeftShift8_2  = putPositive 14 . putPositive 2 . putPositive 2
putJetBitWord FullLeftShift8_4  = putPositive 14 . putPositive 3 . putPositive 1
putJetBitWord FullLeftShift16_1  = putPositive 14 . putPositive 1 . putPositive 4
putJetBitWord FullLeftShift16_2  = putPositive 14 . putPositive 2 . putPositive 3
putJetBitWord FullLeftShift16_4  = putPositive 14 . putPositive 3 . putPositive 2
putJetBitWord FullLeftShift16_8  = putPositive 14 . putPositive 4 . putPositive 1
putJetBitWord FullLeftShift32_1  = putPositive 14 . putPositive 1 . putPositive 5
putJetBitWord FullLeftShift32_2  = putPositive 14 . putPositive 2 . putPositive 4
putJetBitWord FullLeftShift32_4  = putPositive 14 . putPositive 3 . putPositive 3
putJetBitWord FullLeftShift32_8  = putPositive 14 . putPositive 4 . putPositive 2
putJetBitWord FullLeftShift32_16  = putPositive 14 . putPositive 5 . putPositive 1
putJetBitWord FullLeftShift64_1  = putPositive 14 . putPositive 1 . putPositive 6
putJetBitWord FullLeftShift64_2  = putPositive 14 . putPositive 2 . putPositive 5
putJetBitWord FullLeftShift64_4  = putPositive 14 . putPositive 3 . putPositive 4
putJetBitWord FullLeftShift64_8  = putPositive 14 . putPositive 4 . putPositive 3
putJetBitWord FullLeftShift64_16  = putPositive 14 . putPositive 5 . putPositive 2
putJetBitWord FullLeftShift64_32  = putPositive 14 . putPositive 6 . putPositive 1
putJetBitWord FullRightShift8_1  = putPositive 15 . putPositive 1 . putPositive 3
putJetBitWord FullRightShift8_2  = putPositive 15 . putPositive 2 . putPositive 2
putJetBitWord FullRightShift8_4  = putPositive 15 . putPositive 3 . putPositive 1
putJetBitWord FullRightShift16_1  = putPositive 15 . putPositive 1 . putPositive 4
putJetBitWord FullRightShift16_2  = putPositive 15 . putPositive 2 . putPositive 3
putJetBitWord FullRightShift16_4  = putPositive 15 . putPositive 3 . putPositive 2
putJetBitWord FullRightShift16_8  = putPositive 15 . putPositive 4 . putPositive 1
putJetBitWord FullRightShift32_1  = putPositive 15 . putPositive 1 . putPositive 5
putJetBitWord FullRightShift32_2  = putPositive 15 . putPositive 2 . putPositive 4
putJetBitWord FullRightShift32_4  = putPositive 15 . putPositive 3 . putPositive 3
putJetBitWord FullRightShift32_8  = putPositive 15 . putPositive 4 . putPositive 2
putJetBitWord FullRightShift32_16  = putPositive 15 . putPositive 5 . putPositive 1
putJetBitWord FullRightShift64_1  = putPositive 15 . putPositive 1 . putPositive 6
putJetBitWord FullRightShift64_2  = putPositive 15 . putPositive 2 . putPositive 5
putJetBitWord FullRightShift64_4  = putPositive 15 . putPositive 3 . putPositive 4
putJetBitWord FullRightShift64_8  = putPositive 15 . putPositive 4 . putPositive 3
putJetBitWord FullRightShift64_16  = putPositive 15 . putPositive 5 . putPositive 2
putJetBitWord FullRightShift64_32  = putPositive 15 . putPositive 6 . putPositive 1
putJetBitWord Leftmost8_1  = putPositive 16 . putPositive 1 . putPositive 3
putJetBitWord Leftmost8_2  = putPositive 16 . putPositive 2 . putPositive 2
putJetBitWord Leftmost8_4  = putPositive 16 . putPositive 3 . putPositive 1
putJetBitWord Leftmost16_1  = putPositive 16 . putPositive 1 . putPositive 4
putJetBitWord Leftmost16_2  = putPositive 16 . putPositive 2 . putPositive 3
putJetBitWord Leftmost16_4  = putPositive 16 . putPositive 3 . putPositive 2
putJetBitWord Leftmost16_8  = putPositive 16 . putPositive 4 . putPositive 1
putJetBitWord Leftmost32_1  = putPositive 16 . putPositive 1 . putPositive 5
putJetBitWord Leftmost32_2  = putPositive 16 . putPositive 2 . putPositive 4
putJetBitWord Leftmost32_4  = putPositive 16 . putPositive 3 . putPositive 3
putJetBitWord Leftmost32_8  = putPositive 16 . putPositive 4 . putPositive 2
putJetBitWord Leftmost32_16  = putPositive 16 . putPositive 5 . putPositive 1
putJetBitWord Leftmost64_1  = putPositive 16 . putPositive 1 . putPositive 6
putJetBitWord Leftmost64_2  = putPositive 16 . putPositive 2 . putPositive 5
putJetBitWord Leftmost64_4  = putPositive 16 . putPositive 3 . putPositive 4
putJetBitWord Leftmost64_8  = putPositive 16 . putPositive 4 . putPositive 3
putJetBitWord Leftmost64_16  = putPositive 16 . putPositive 5 . putPositive 2
putJetBitWord Leftmost64_32  = putPositive 16 . putPositive 6 . putPositive 1
putJetBitWord Rightmost8_1  = putPositive 17 . putPositive 1 . putPositive 3
putJetBitWord Rightmost8_2  = putPositive 17 . putPositive 2 . putPositive 2
putJetBitWord Rightmost8_4  = putPositive 17 . putPositive 3 . putPositive 1
putJetBitWord Rightmost16_1  = putPositive 17 . putPositive 1 . putPositive 4
putJetBitWord Rightmost16_2  = putPositive 17 . putPositive 2 . putPositive 3
putJetBitWord Rightmost16_4  = putPositive 17 . putPositive 3 . putPositive 2
putJetBitWord Rightmost16_8  = putPositive 17 . putPositive 4 . putPositive 1
putJetBitWord Rightmost32_1  = putPositive 17 . putPositive 1 . putPositive 5
putJetBitWord Rightmost32_2  = putPositive 17 . putPositive 2 . putPositive 4
putJetBitWord Rightmost32_4  = putPositive 17 . putPositive 3 . putPositive 3
putJetBitWord Rightmost32_8  = putPositive 17 . putPositive 4 . putPositive 2
putJetBitWord Rightmost32_16  = putPositive 17 . putPositive 5 . putPositive 1
putJetBitWord Rightmost64_1  = putPositive 17 . putPositive 1 . putPositive 6
putJetBitWord Rightmost64_2  = putPositive 17 . putPositive 2 . putPositive 5
putJetBitWord Rightmost64_4  = putPositive 17 . putPositive 3 . putPositive 4
putJetBitWord Rightmost64_8  = putPositive 17 . putPositive 4 . putPositive 3
putJetBitWord Rightmost64_16  = putPositive 17 . putPositive 5 . putPositive 2
putJetBitWord Rightmost64_32  = putPositive 17 . putPositive 6 . putPositive 1
putJetBitWord LeftPadLow1_8  = putPositive 18 . putPositive 1 . putPositive 3
putJetBitWord LeftPadLow1_16  = putPositive 18 . putPositive 1 . putPositive 4
putJetBitWord LeftPadLow8_16  = putPositive 18 . putPositive 4 . putPositive 1
putJetBitWord LeftPadLow1_32  = putPositive 18 . putPositive 1 . putPositive 5
putJetBitWord LeftPadLow8_32  = putPositive 18 . putPositive 4 . putPositive 2
putJetBitWord LeftPadLow16_32  = putPositive 18 . putPositive 5 . putPositive 1
putJetBitWord LeftPadLow1_64  = putPositive 18 . putPositive 1 . putPositive 6
putJetBitWord LeftPadLow8_64  = putPositive 18 . putPositive 4 . putPositive 3
putJetBitWord LeftPadLow16_64  = putPositive 18 . putPositive 5 . putPositive 2
putJetBitWord LeftPadLow32_64  = putPositive 18 . putPositive 6 . putPositive 1
putJetBitWord LeftPadHigh1_8  = putPositive 19 . putPositive 1 . putPositive 3
putJetBitWord LeftPadHigh1_16  = putPositive 19 . putPositive 1 . putPositive 4
putJetBitWord LeftPadHigh8_16  = putPositive 19 . putPositive 4 . putPositive 1
putJetBitWord LeftPadHigh1_32  = putPositive 19 . putPositive 1 . putPositive 5
putJetBitWord LeftPadHigh8_32  = putPositive 19 . putPositive 4 . putPositive 2
putJetBitWord LeftPadHigh16_32  = putPositive 19 . putPositive 5 . putPositive 1
putJetBitWord LeftPadHigh1_64  = putPositive 19 . putPositive 1 . putPositive 6
putJetBitWord LeftPadHigh8_64  = putPositive 19 . putPositive 4 . putPositive 3
putJetBitWord LeftPadHigh16_64  = putPositive 19 . putPositive 5 . putPositive 2
putJetBitWord LeftPadHigh32_64  = putPositive 19 . putPositive 6 . putPositive 1
putJetBitWord LeftExtend1_8  = putPositive 20 . putPositive 1 . putPositive 3
putJetBitWord LeftExtend1_16  = putPositive 20 . putPositive 1 . putPositive 4
putJetBitWord LeftExtend8_16  = putPositive 20 . putPositive 4 . putPositive 1
putJetBitWord LeftExtend1_32  = putPositive 20 . putPositive 1 . putPositive 5
putJetBitWord LeftExtend8_32  = putPositive 20 . putPositive 4 . putPositive 2
putJetBitWord LeftExtend16_32  = putPositive 20 . putPositive 5 . putPositive 1
putJetBitWord LeftExtend1_64  = putPositive 20 . putPositive 1 . putPositive 6
putJetBitWord LeftExtend8_64  = putPositive 20 . putPositive 4 . putPositive 3
putJetBitWord LeftExtend16_64  = putPositive 20 . putPositive 5 . putPositive 2
putJetBitWord LeftExtend32_64  = putPositive 20 . putPositive 6 . putPositive 1
putJetBitWord RightPadLow1_8  = putPositive 21 . putPositive 1 . putPositive 3
putJetBitWord RightPadLow1_16  = putPositive 21 . putPositive 1 . putPositive 4
putJetBitWord RightPadLow8_16  = putPositive 21 . putPositive 4 . putPositive 1
putJetBitWord RightPadLow1_32  = putPositive 21 . putPositive 1 . putPositive 5
putJetBitWord RightPadLow8_32  = putPositive 21 . putPositive 4 . putPositive 2
putJetBitWord RightPadLow16_32  = putPositive 21 . putPositive 5 . putPositive 1
putJetBitWord RightPadLow1_64  = putPositive 21 . putPositive 1 . putPositive 6
putJetBitWord RightPadLow8_64  = putPositive 21 . putPositive 4 . putPositive 3
putJetBitWord RightPadLow16_64  = putPositive 21 . putPositive 5 . putPositive 2
putJetBitWord RightPadLow32_64  = putPositive 21 . putPositive 6 . putPositive 1
putJetBitWord RightPadHigh1_8  = putPositive 22 . putPositive 1 . putPositive 3
putJetBitWord RightPadHigh1_16  = putPositive 22 . putPositive 1 . putPositive 4
putJetBitWord RightPadHigh8_16  = putPositive 22 . putPositive 4 . putPositive 1
putJetBitWord RightPadHigh1_32  = putPositive 22 . putPositive 1 . putPositive 5
putJetBitWord RightPadHigh8_32  = putPositive 22 . putPositive 4 . putPositive 2
putJetBitWord RightPadHigh16_32  = putPositive 22 . putPositive 5 . putPositive 1
putJetBitWord RightPadHigh1_64  = putPositive 22 . putPositive 1 . putPositive 6
putJetBitWord RightPadHigh8_64  = putPositive 22 . putPositive 4 . putPositive 3
putJetBitWord RightPadHigh16_64  = putPositive 22 . putPositive 5 . putPositive 2
putJetBitWord RightPadHigh32_64  = putPositive 22 . putPositive 6 . putPositive 1
putJetBitWord RightExtend8_16  = putPositive 23 . putPositive 4 . putPositive 1
putJetBitWord RightExtend8_32  = putPositive 23 . putPositive 4 . putPositive 2
putJetBitWord RightExtend16_32  = putPositive 23 . putPositive 5 . putPositive 1
putJetBitWord RightExtend8_64  = putPositive 23 . putPositive 4 . putPositive 3
putJetBitWord RightExtend16_64  = putPositive 23 . putPositive 5 . putPositive 2
putJetBitWord RightExtend32_64  = putPositive 23 . putPositive 6 . putPositive 1
putJetBitWord LeftShiftWith8   = putPositive 24 . putPositive 3
putJetBitWord LeftShiftWith16  = putPositive 24 . putPositive 4
putJetBitWord LeftShiftWith32  = putPositive 24 . putPositive 5
putJetBitWord LeftShiftWith64  = putPositive 24 . putPositive 6
putJetBitWord RightShiftWith8  = putPositive 25 . putPositive 3
putJetBitWord RightShiftWith16 = putPositive 25 . putPositive 4
putJetBitWord RightShiftWith32 = putPositive 25 . putPositive 5
putJetBitWord RightShiftWith64 = putPositive 25 . putPositive 6
putJetBitWord LeftShift8   = putPositive 26 . putPositive 3
putJetBitWord LeftShift16  = putPositive 26 . putPositive 4
putJetBitWord LeftShift32  = putPositive 26 . putPositive 5
putJetBitWord LeftShift64  = putPositive 26 . putPositive 6
putJetBitWord RightShift8  = putPositive 27 . putPositive 3
putJetBitWord RightShift16 = putPositive 27 . putPositive 4
putJetBitWord RightShift32 = putPositive 27 . putPositive 5
putJetBitWord RightShift64 = putPositive 27 . putPositive 6
putJetBitWord LeftRotate8  = putPositive 28 . putPositive 3
putJetBitWord LeftRotate16 = putPositive 28 . putPositive 4
putJetBitWord LeftRotate32 = putPositive 28 . putPositive 5
putJetBitWord LeftRotate64 = putPositive 28 . putPositive 6
putJetBitWord RightRotate8  = putPositive 29 . putPositive 3
putJetBitWord RightRotate16 = putPositive 29 . putPositive 4
putJetBitWord RightRotate32 = putPositive 29 . putPositive 5
putJetBitWord RightRotate64 = putPositive 29 . putPositive 6

putJetBitArith :: ArithJet a b -> DList Bool
putJetBitArith One8   = putPositive 1 . putPositive 3
putJetBitArith One16  = putPositive 1 . putPositive 4
putJetBitArith One32  = putPositive 1 . putPositive 5
putJetBitArith One64  = putPositive 1 . putPositive 6
putJetBitArith FullAdd8   = putPositive 2 . putPositive 3
putJetBitArith FullAdd16  = putPositive 2 . putPositive 4
putJetBitArith FullAdd32  = putPositive 2 . putPositive 5
putJetBitArith FullAdd64  = putPositive 2 . putPositive 6
putJetBitArith Add8   = putPositive 3 . putPositive 3
putJetBitArith Add16  = putPositive 3 . putPositive 4
putJetBitArith Add32  = putPositive 3 . putPositive 5
putJetBitArith Add64  = putPositive 3 . putPositive 6
putJetBitArith FullIncrement8   = putPositive 4 . putPositive 3
putJetBitArith FullIncrement16  = putPositive 4 . putPositive 4
putJetBitArith FullIncrement32  = putPositive 4 . putPositive 5
putJetBitArith FullIncrement64  = putPositive 4 . putPositive 6
putJetBitArith Increment8   = putPositive 5 . putPositive 3
putJetBitArith Increment16  = putPositive 5 . putPositive 4
putJetBitArith Increment32  = putPositive 5 . putPositive 5
putJetBitArith Increment64  = putPositive 5 . putPositive 6
putJetBitArith FullSubtract8   = putPositive 7 . putPositive 3
putJetBitArith FullSubtract16  = putPositive 7 . putPositive 4
putJetBitArith FullSubtract32  = putPositive 7 . putPositive 5
putJetBitArith FullSubtract64  = putPositive 7 . putPositive 6
putJetBitArith Subtract8   = putPositive 8 . putPositive 3
putJetBitArith Subtract16  = putPositive 8 . putPositive 4
putJetBitArith Subtract32  = putPositive 8 . putPositive 5
putJetBitArith Subtract64  = putPositive 8 . putPositive 6
putJetBitArith Negate8   = putPositive 9 . putPositive 3
putJetBitArith Negate16  = putPositive 9 . putPositive 4
putJetBitArith Negate32  = putPositive 9 . putPositive 5
putJetBitArith Negate64  = putPositive 9 . putPositive 6
putJetBitArith FullDecrement8   = putPositive 10 . putPositive 3
putJetBitArith FullDecrement16  = putPositive 10 . putPositive 4
putJetBitArith FullDecrement32  = putPositive 10 . putPositive 5
putJetBitArith FullDecrement64  = putPositive 10 . putPositive 6
putJetBitArith Decrement8   = putPositive 11 . putPositive 3
putJetBitArith Decrement16  = putPositive 11 . putPositive 4
putJetBitArith Decrement32  = putPositive 11 . putPositive 5
putJetBitArith Decrement64  = putPositive 11 . putPositive 6
putJetBitArith FullMultiply8   = putPositive 12 . putPositive 3
putJetBitArith FullMultiply16  = putPositive 12 . putPositive 4
putJetBitArith FullMultiply32  = putPositive 12 . putPositive 5
putJetBitArith FullMultiply64  = putPositive 12 . putPositive 6
putJetBitArith Multiply8   = putPositive 13 . putPositive 3
putJetBitArith Multiply16  = putPositive 13 . putPositive 4
putJetBitArith Multiply32  = putPositive 13 . putPositive 5
putJetBitArith Multiply64  = putPositive 13 . putPositive 6
putJetBitArith IsZero8   = putPositive 14 . putPositive 3
putJetBitArith IsZero16  = putPositive 14 . putPositive 4
putJetBitArith IsZero32  = putPositive 14 . putPositive 5
putJetBitArith IsZero64  = putPositive 14 . putPositive 6
putJetBitArith IsOne8   = putPositive 15 . putPositive 3
putJetBitArith IsOne16  = putPositive 15 . putPositive 4
putJetBitArith IsOne32  = putPositive 15 . putPositive 5
putJetBitArith IsOne64  = putPositive 15 . putPositive 6
putJetBitArith Le8   = putPositive 16 . putPositive 3
putJetBitArith Le16  = putPositive 16 . putPositive 4
putJetBitArith Le32  = putPositive 16 . putPositive 5
putJetBitArith Le64  = putPositive 16 . putPositive 6
putJetBitArith Lt8   = putPositive 17 . putPositive 3
putJetBitArith Lt16  = putPositive 17 . putPositive 4
putJetBitArith Lt32  = putPositive 17 . putPositive 5
putJetBitArith Lt64  = putPositive 17 . putPositive 6
putJetBitArith Min8   = putPositive 18 . putPositive 3
putJetBitArith Min16  = putPositive 18 . putPositive 4
putJetBitArith Min32  = putPositive 18 . putPositive 5
putJetBitArith Min64  = putPositive 18 . putPositive 6
putJetBitArith Max8   = putPositive 19 . putPositive 3
putJetBitArith Max16  = putPositive 19 . putPositive 4
putJetBitArith Max32  = putPositive 19 . putPositive 5
putJetBitArith Max64  = putPositive 19 . putPositive 6
putJetBitArith Median8   = putPositive 20 . putPositive 3
putJetBitArith Median16  = putPositive 20 . putPositive 4
putJetBitArith Median32  = putPositive 20 . putPositive 5
putJetBitArith Median64  = putPositive 20 . putPositive 6
putJetBitArith DivMod128_64 = putPositive 21 . putPositive 6
putJetBitArith DivMod8   = putPositive 22 . putPositive 3
putJetBitArith DivMod16  = putPositive 22 . putPositive 4
putJetBitArith DivMod32  = putPositive 22 . putPositive 5
putJetBitArith DivMod64  = putPositive 22 . putPositive 6
putJetBitArith Divide8   = putPositive 23 . putPositive 3
putJetBitArith Divide16  = putPositive 23 . putPositive 4
putJetBitArith Divide32  = putPositive 23 . putPositive 5
putJetBitArith Divide64  = putPositive 23 . putPositive 6
putJetBitArith Modulo8   = putPositive 24 . putPositive 3
putJetBitArith Modulo16  = putPositive 24 . putPositive 4
putJetBitArith Modulo32  = putPositive 24 . putPositive 5
putJetBitArith Modulo64  = putPositive 24 . putPositive 6
putJetBitArith Divides8   = putPositive 25 . putPositive 3
putJetBitArith Divides16  = putPositive 25 . putPositive 4
putJetBitArith Divides32  = putPositive 25 . putPositive 5
putJetBitArith Divides64  = putPositive 25 . putPositive 6

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
putJetBitSecp256k1 GejEquiv = putPositive 17
putJetBitSecp256k1 GejGeEquiv = putPositive 18
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
coreJetMap = Map.fromList . fmap mkAssoc $ toList coreCatalogue
 where
  mkAssoc :: SomeArrow CoreJet -> (Hash256, (SomeArrow CoreJet))
  mkAssoc wrapped@(SomeArrow jt) = (identityRoot (specification jt), wrapped)

-- | The costs of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.jetCost' method.
jetCost :: CoreJet a b -> Weight
jetCost (WordJet x) = jetCostWord x
jetCost (ArithJet x) = jetCostArith x
jetCost (HashJet x) = jetCostHash x
jetCost (Secp256k1Jet x) = jetCostSecp256k1 x
jetCost (SignatureJet x) = jetCostSignature x
jetCost (BitcoinJet x) = jetCostBitcoin x

jetCostWord :: WordJet a b -> Weight
jetCostWord Verify = Benchmarks.cost "Verify"
jetCostWord Low1 = Benchmarks.cost "Low1"
jetCostWord Low8 = Benchmarks.cost "Low8"
jetCostWord Low16 = Benchmarks.cost "Low16"
jetCostWord Low32 = Benchmarks.cost "Low32"
jetCostWord Low64 = Benchmarks.cost "Low64"
jetCostWord High1 = Benchmarks.cost "High1"
jetCostWord High8 = Benchmarks.cost "High8"
jetCostWord High16 = Benchmarks.cost "High16"
jetCostWord High32 = Benchmarks.cost "High32"
jetCostWord High64 = Benchmarks.cost "High64"
jetCostWord Complement1 = Benchmarks.cost "Complement1"
jetCostWord Complement8 = Benchmarks.cost "Complement8"
jetCostWord Complement16 = Benchmarks.cost "Complement16"
jetCostWord Complement32 = Benchmarks.cost "Complement32"
jetCostWord Complement64 = Benchmarks.cost "Complement64"
jetCostWord And1 = Benchmarks.cost "And1"
jetCostWord And8 = Benchmarks.cost "And8"
jetCostWord And16 = Benchmarks.cost "And16"
jetCostWord And32 = Benchmarks.cost "And32"
jetCostWord And64 = Benchmarks.cost "And64"
jetCostWord Or1 = Benchmarks.cost "Or1"
jetCostWord Or8 = Benchmarks.cost "Or8"
jetCostWord Or16 = Benchmarks.cost "Or16"
jetCostWord Or32 = Benchmarks.cost "Or32"
jetCostWord Or64 = Benchmarks.cost "Or64"
jetCostWord Xor1 = Benchmarks.cost "Xor1"
jetCostWord Xor8 = Benchmarks.cost "Xor8"
jetCostWord Xor16 = Benchmarks.cost "Xor16"
jetCostWord Xor32 = Benchmarks.cost "Xor32"
jetCostWord Xor64 = Benchmarks.cost "Xor64"
jetCostWord Maj1 = Benchmarks.cost "Maj1"
jetCostWord Maj8 = Benchmarks.cost "Maj8"
jetCostWord Maj16 = Benchmarks.cost "Maj16"
jetCostWord Maj32 = Benchmarks.cost "Maj32"
jetCostWord Maj64 = Benchmarks.cost "Maj64"
jetCostWord XorXor1 = Benchmarks.cost "XorXor1"
jetCostWord XorXor8 = Benchmarks.cost "XorXor8"
jetCostWord XorXor16 = Benchmarks.cost "XorXor16"
jetCostWord XorXor32 = Benchmarks.cost "XorXor32"
jetCostWord XorXor64 = Benchmarks.cost "XorXor64"
jetCostWord Ch1 = Benchmarks.cost "Ch1"
jetCostWord Ch8 = Benchmarks.cost "Ch8"
jetCostWord Ch16 = Benchmarks.cost "Ch16"
jetCostWord Ch32 = Benchmarks.cost "Ch32"
jetCostWord Ch64 = Benchmarks.cost "Ch64"
jetCostWord Some1 = Benchmarks.cost "Some1"
jetCostWord Some8 = Benchmarks.cost "Some8"
jetCostWord Some16 = Benchmarks.cost "Some16"
jetCostWord Some32 = Benchmarks.cost "Some32"
jetCostWord Some64 = Benchmarks.cost "Some64"
jetCostWord All8 = Benchmarks.cost "All8"
jetCostWord All16 = Benchmarks.cost "All16"
jetCostWord All32 = Benchmarks.cost "All32"
jetCostWord All64 = Benchmarks.cost "All64"
jetCostWord Eq1 = Benchmarks.cost "Eq1"
jetCostWord Eq8 = Benchmarks.cost "Eq8"
jetCostWord Eq16 = Benchmarks.cost "Eq16"
jetCostWord Eq32 = Benchmarks.cost "Eq32"
jetCostWord Eq64 = Benchmarks.cost "Eq64"
jetCostWord Eq256 = Benchmarks.cost "Eq256"
jetCostWord FullLeftShift8_1 = Benchmarks.cost "FullLeftShift8_1"
jetCostWord FullLeftShift8_2 = Benchmarks.cost "FullLeftShift8_2"
jetCostWord FullLeftShift8_4 = Benchmarks.cost "FullLeftShift8_4"
jetCostWord FullLeftShift16_1 = Benchmarks.cost "FullLeftShift16_1"
jetCostWord FullLeftShift16_2 = Benchmarks.cost "FullLeftShift16_2"
jetCostWord FullLeftShift16_4 = Benchmarks.cost "FullLeftShift16_4"
jetCostWord FullLeftShift16_8 = Benchmarks.cost "FullLeftShift16_8"
jetCostWord FullLeftShift32_1 = Benchmarks.cost "FullLeftShift32_1"
jetCostWord FullLeftShift32_2 = Benchmarks.cost "FullLeftShift32_2"
jetCostWord FullLeftShift32_4 = Benchmarks.cost "FullLeftShift32_4"
jetCostWord FullLeftShift32_8 = Benchmarks.cost "FullLeftShift32_8"
jetCostWord FullLeftShift32_16 = Benchmarks.cost "FullLeftShift32_16"
jetCostWord FullLeftShift64_1 = Benchmarks.cost "FullLeftShift64_1"
jetCostWord FullLeftShift64_2 = Benchmarks.cost "FullLeftShift64_2"
jetCostWord FullLeftShift64_4 = Benchmarks.cost "FullLeftShift64_4"
jetCostWord FullLeftShift64_8 = Benchmarks.cost "FullLeftShift64_8"
jetCostWord FullLeftShift64_16 = Benchmarks.cost "FullLeftShift64_16"
jetCostWord FullLeftShift64_32 = Benchmarks.cost "FullLeftShift64_32"
jetCostWord FullRightShift8_1 = Benchmarks.cost "FullRightShift8_1"
jetCostWord FullRightShift8_2 = Benchmarks.cost "FullRightShift8_2"
jetCostWord FullRightShift8_4 = Benchmarks.cost "FullRightShift8_4"
jetCostWord FullRightShift16_1 = Benchmarks.cost "FullRightShift16_1"
jetCostWord FullRightShift16_2 = Benchmarks.cost "FullRightShift16_2"
jetCostWord FullRightShift16_4 = Benchmarks.cost "FullRightShift16_4"
jetCostWord FullRightShift16_8 = Benchmarks.cost "FullRightShift16_8"
jetCostWord FullRightShift32_1 = Benchmarks.cost "FullRightShift32_1"
jetCostWord FullRightShift32_2 = Benchmarks.cost "FullRightShift32_2"
jetCostWord FullRightShift32_4 = Benchmarks.cost "FullRightShift32_4"
jetCostWord FullRightShift32_8 = Benchmarks.cost "FullRightShift32_8"
jetCostWord FullRightShift32_16 = Benchmarks.cost "FullRightShift32_16"
jetCostWord FullRightShift64_1 = Benchmarks.cost "FullRightShift64_1"
jetCostWord FullRightShift64_2 = Benchmarks.cost "FullRightShift64_2"
jetCostWord FullRightShift64_4 = Benchmarks.cost "FullRightShift64_4"
jetCostWord FullRightShift64_8 = Benchmarks.cost "FullRightShift64_8"
jetCostWord FullRightShift64_16 = Benchmarks.cost "FullRightShift64_16"
jetCostWord FullRightShift64_32 = Benchmarks.cost "FullRightShift64_32"
jetCostWord Leftmost8_1 = Benchmarks.cost "Leftmost8_1"
jetCostWord Leftmost8_2 = Benchmarks.cost "Leftmost8_2"
jetCostWord Leftmost8_4 = Benchmarks.cost "Leftmost8_4"
jetCostWord Leftmost16_1 = Benchmarks.cost "Leftmost16_1"
jetCostWord Leftmost16_2 = Benchmarks.cost "Leftmost16_2"
jetCostWord Leftmost16_4 = Benchmarks.cost "Leftmost16_4"
jetCostWord Leftmost16_8 = Benchmarks.cost "Leftmost16_8"
jetCostWord Leftmost32_1 = Benchmarks.cost "Leftmost32_1"
jetCostWord Leftmost32_2 = Benchmarks.cost "Leftmost32_2"
jetCostWord Leftmost32_4 = Benchmarks.cost "Leftmost32_4"
jetCostWord Leftmost32_8 = Benchmarks.cost "Leftmost32_8"
jetCostWord Leftmost32_16 = Benchmarks.cost "Leftmost32_16"
jetCostWord Leftmost64_1 = Benchmarks.cost "Leftmost64_1"
jetCostWord Leftmost64_2 = Benchmarks.cost "Leftmost64_2"
jetCostWord Leftmost64_4 = Benchmarks.cost "Leftmost64_4"
jetCostWord Leftmost64_8 = Benchmarks.cost "Leftmost64_8"
jetCostWord Leftmost64_16 = Benchmarks.cost "Leftmost64_16"
jetCostWord Leftmost64_32 = Benchmarks.cost "Leftmost64_32"
jetCostWord Rightmost8_1 = Benchmarks.cost "Rightmost8_1"
jetCostWord Rightmost8_2 = Benchmarks.cost "Rightmost8_2"
jetCostWord Rightmost8_4 = Benchmarks.cost "Rightmost8_4"
jetCostWord Rightmost16_1 = Benchmarks.cost "Rightmost16_1"
jetCostWord Rightmost16_2 = Benchmarks.cost "Rightmost16_2"
jetCostWord Rightmost16_4 = Benchmarks.cost "Rightmost16_4"
jetCostWord Rightmost16_8 = Benchmarks.cost "Rightmost16_8"
jetCostWord Rightmost32_1 = Benchmarks.cost "Rightmost32_1"
jetCostWord Rightmost32_2 = Benchmarks.cost "Rightmost32_2"
jetCostWord Rightmost32_4 = Benchmarks.cost "Rightmost32_4"
jetCostWord Rightmost32_8 = Benchmarks.cost "Rightmost32_8"
jetCostWord Rightmost32_16 = Benchmarks.cost "Rightmost32_16"
jetCostWord Rightmost64_1 = Benchmarks.cost "Rightmost64_1"
jetCostWord Rightmost64_2 = Benchmarks.cost "Rightmost64_2"
jetCostWord Rightmost64_4 = Benchmarks.cost "Rightmost64_4"
jetCostWord Rightmost64_8 = Benchmarks.cost "Rightmost64_8"
jetCostWord Rightmost64_16 = Benchmarks.cost "Rightmost64_16"
jetCostWord Rightmost64_32 = Benchmarks.cost "Rightmost64_32"
jetCostWord LeftPadLow1_8 = Benchmarks.cost "LeftPadLow1_8"
jetCostWord LeftPadLow1_16 = Benchmarks.cost "LeftPadLow1_16"
jetCostWord LeftPadLow8_16 = Benchmarks.cost "LeftPadLow8_16"
jetCostWord LeftPadLow1_32 = Benchmarks.cost "LeftPadLow1_32"
jetCostWord LeftPadLow8_32 = Benchmarks.cost "LeftPadLow8_32"
jetCostWord LeftPadLow16_32 = Benchmarks.cost "LeftPadLow16_32"
jetCostWord LeftPadLow1_64 = Benchmarks.cost "LeftPadLow1_64"
jetCostWord LeftPadLow8_64 = Benchmarks.cost "LeftPadLow8_64"
jetCostWord LeftPadLow16_64 = Benchmarks.cost "LeftPadLow16_64"
jetCostWord LeftPadLow32_64 = Benchmarks.cost "LeftPadLow32_64"
jetCostWord LeftPadHigh1_8 = Benchmarks.cost "LeftPadHigh1_8"
jetCostWord LeftPadHigh1_16 = Benchmarks.cost "LeftPadHigh1_16"
jetCostWord LeftPadHigh8_16 = Benchmarks.cost "LeftPadHigh8_16"
jetCostWord LeftPadHigh1_32 = Benchmarks.cost "LeftPadHigh1_32"
jetCostWord LeftPadHigh8_32 = Benchmarks.cost "LeftPadHigh8_32"
jetCostWord LeftPadHigh16_32 = Benchmarks.cost "LeftPadHigh16_32"
jetCostWord LeftPadHigh1_64 = Benchmarks.cost "LeftPadHigh1_64"
jetCostWord LeftPadHigh8_64 = Benchmarks.cost "LeftPadHigh8_64"
jetCostWord LeftPadHigh16_64 = Benchmarks.cost "LeftPadHigh16_64"
jetCostWord LeftPadHigh32_64 = Benchmarks.cost "LeftPadHigh32_64"
jetCostWord LeftExtend1_8 = Benchmarks.cost "LeftExtend1_8"
jetCostWord LeftExtend1_16 = Benchmarks.cost "LeftExtend1_16"
jetCostWord LeftExtend8_16 = Benchmarks.cost "LeftExtend8_16"
jetCostWord LeftExtend1_32 = Benchmarks.cost "LeftExtend1_32"
jetCostWord LeftExtend8_32 = Benchmarks.cost "LeftExtend8_32"
jetCostWord LeftExtend16_32 = Benchmarks.cost "LeftExtend16_32"
jetCostWord LeftExtend1_64 = Benchmarks.cost "LeftExtend1_64"
jetCostWord LeftExtend8_64 = Benchmarks.cost "LeftExtend8_64"
jetCostWord LeftExtend16_64 = Benchmarks.cost "LeftExtend16_64"
jetCostWord LeftExtend32_64 = Benchmarks.cost "LeftExtend32_64"
jetCostWord RightPadLow1_8 = Benchmarks.cost "RightPadLow1_8"
jetCostWord RightPadLow1_16 = Benchmarks.cost "RightPadLow1_16"
jetCostWord RightPadLow8_16 = Benchmarks.cost "RightPadLow8_16"
jetCostWord RightPadLow1_32 = Benchmarks.cost "RightPadLow1_32"
jetCostWord RightPadLow8_32 = Benchmarks.cost "RightPadLow8_32"
jetCostWord RightPadLow16_32 = Benchmarks.cost "RightPadLow16_32"
jetCostWord RightPadLow1_64 = Benchmarks.cost "RightPadLow1_64"
jetCostWord RightPadLow8_64 = Benchmarks.cost "RightPadLow8_64"
jetCostWord RightPadLow16_64 = Benchmarks.cost "RightPadLow16_64"
jetCostWord RightPadLow32_64 = Benchmarks.cost "RightPadLow32_64"
jetCostWord RightPadHigh1_8 = Benchmarks.cost "RightPadHigh1_8"
jetCostWord RightPadHigh1_16 = Benchmarks.cost "RightPadHigh1_16"
jetCostWord RightPadHigh8_16 = Benchmarks.cost "RightPadHigh8_16"
jetCostWord RightPadHigh1_32 = Benchmarks.cost "RightPadHigh1_32"
jetCostWord RightPadHigh8_32 = Benchmarks.cost "RightPadHigh8_32"
jetCostWord RightPadHigh16_32 = Benchmarks.cost "RightPadHigh16_32"
jetCostWord RightPadHigh1_64 = Benchmarks.cost "RightPadHigh1_64"
jetCostWord RightPadHigh8_64 = Benchmarks.cost "RightPadHigh8_64"
jetCostWord RightPadHigh16_64 = Benchmarks.cost "RightPadHigh16_64"
jetCostWord RightPadHigh32_64 = Benchmarks.cost "RightPadHigh32_64"
jetCostWord RightExtend8_16 = Benchmarks.cost "RightExtend8_16"
jetCostWord RightExtend8_32 = Benchmarks.cost "RightExtend8_32"
jetCostWord RightExtend16_32 = Benchmarks.cost "RightExtend16_32"
jetCostWord RightExtend8_64 = Benchmarks.cost "RightExtend8_64"
jetCostWord RightExtend16_64 = Benchmarks.cost "RightExtend16_64"
jetCostWord RightExtend32_64 = Benchmarks.cost "RightExtend32_64"
jetCostWord LeftShiftWith8 = Benchmarks.cost "LeftShiftWith8"
jetCostWord LeftShiftWith16 = Benchmarks.cost "LeftShiftWith16"
jetCostWord LeftShiftWith32 = Benchmarks.cost "LeftShiftWith32"
jetCostWord LeftShiftWith64 = Benchmarks.cost "LeftShiftWith64"
jetCostWord LeftShift8 = Benchmarks.cost "LeftShift8"
jetCostWord LeftShift16 = Benchmarks.cost "LeftShift16"
jetCostWord LeftShift32 = Benchmarks.cost "LeftShift32"
jetCostWord LeftShift64 = Benchmarks.cost "LeftShift64"
jetCostWord RightShiftWith8 = Benchmarks.cost "RightShiftWith8"
jetCostWord RightShiftWith16 = Benchmarks.cost "RightShiftWith16"
jetCostWord RightShiftWith32 = Benchmarks.cost "RightShiftWith32"
jetCostWord RightShiftWith64 = Benchmarks.cost "RightShiftWith64"
jetCostWord RightShift8 = Benchmarks.cost "RightShift8"
jetCostWord RightShift16 = Benchmarks.cost "RightShift16"
jetCostWord RightShift32 = Benchmarks.cost "RightShift32"
jetCostWord RightShift64 = Benchmarks.cost "RightShift64"
jetCostWord LeftRotate8 = Benchmarks.cost "LeftRotate8"
jetCostWord LeftRotate16 = Benchmarks.cost "LeftRotate16"
jetCostWord LeftRotate32 = Benchmarks.cost "LeftRotate32"
jetCostWord LeftRotate64 = Benchmarks.cost "LeftRotate64"
jetCostWord RightRotate8 = Benchmarks.cost "RightRotate8"
jetCostWord RightRotate16 = Benchmarks.cost "RightRotate16"
jetCostWord RightRotate32 = Benchmarks.cost "RightRotate32"
jetCostWord RightRotate64 = Benchmarks.cost "RightRotate64"

jetCostArith :: ArithJet a b -> Weight
jetCostArith One8 = Benchmarks.cost "One8"
jetCostArith One16 = Benchmarks.cost "One16"
jetCostArith One32 = Benchmarks.cost "One32"
jetCostArith One64 = Benchmarks.cost "One64"
jetCostArith FullAdd8 = Benchmarks.cost "FullAdd8"
jetCostArith FullAdd16 = Benchmarks.cost "FullAdd16"
jetCostArith FullAdd32 = Benchmarks.cost "FullAdd32"
jetCostArith FullAdd64 = Benchmarks.cost "FullAdd64"
jetCostArith Add8 = Benchmarks.cost "Add8"
jetCostArith Add16 = Benchmarks.cost "Add16"
jetCostArith Add32 = Benchmarks.cost "Add32"
jetCostArith Add64 = Benchmarks.cost "Add64"
jetCostArith FullIncrement8 = Benchmarks.cost "FullIncrement8"
jetCostArith FullIncrement16 = Benchmarks.cost "FullIncrement16"
jetCostArith FullIncrement32 = Benchmarks.cost "FullIncrement32"
jetCostArith FullIncrement64 = Benchmarks.cost "FullIncrement64"
jetCostArith Increment8 = Benchmarks.cost "Increment8"
jetCostArith Increment16 = Benchmarks.cost "Increment16"
jetCostArith Increment32 = Benchmarks.cost "Increment32"
jetCostArith Increment64 = Benchmarks.cost "Increment64"
jetCostArith FullSubtract8 = Benchmarks.cost "FullSubtract8"
jetCostArith FullSubtract16 = Benchmarks.cost "FullSubtract16"
jetCostArith FullSubtract32 = Benchmarks.cost "FullSubtract32"
jetCostArith FullSubtract64 = Benchmarks.cost "FullSubtract64"
jetCostArith Subtract8 = Benchmarks.cost "Subtract8"
jetCostArith Subtract16 = Benchmarks.cost "Subtract16"
jetCostArith Subtract32 = Benchmarks.cost "Subtract32"
jetCostArith Subtract64 = Benchmarks.cost "Subtract64"
jetCostArith Negate8 = Benchmarks.cost "Negate8"
jetCostArith Negate16 = Benchmarks.cost "Negate16"
jetCostArith Negate32 = Benchmarks.cost "Negate32"
jetCostArith Negate64 = Benchmarks.cost "Negate64"
jetCostArith FullDecrement8 = Benchmarks.cost "FullDecrement8"
jetCostArith FullDecrement16 = Benchmarks.cost "FullDecrement16"
jetCostArith FullDecrement32 = Benchmarks.cost "FullDecrement32"
jetCostArith FullDecrement64 = Benchmarks.cost "FullDecrement64"
jetCostArith Decrement8 = Benchmarks.cost "Decrement8"
jetCostArith Decrement16 = Benchmarks.cost "Decrement16"
jetCostArith Decrement32 = Benchmarks.cost "Decrement32"
jetCostArith Decrement64 = Benchmarks.cost "Decrement64"
jetCostArith Multiply8 = Benchmarks.cost "Multiply8"
jetCostArith Multiply16 = Benchmarks.cost "Multiply16"
jetCostArith Multiply32 = Benchmarks.cost "Multiply32"
jetCostArith Multiply64 = Benchmarks.cost "Multiply64"
jetCostArith FullMultiply8 = Benchmarks.cost "FullMultiply8"
jetCostArith FullMultiply16 = Benchmarks.cost "FullMultiply16"
jetCostArith FullMultiply32 = Benchmarks.cost "FullMultiply32"
jetCostArith FullMultiply64 = Benchmarks.cost "FullMultiply64"
jetCostArith IsZero8 = Benchmarks.cost "IsZero8"
jetCostArith IsZero16 = Benchmarks.cost "IsZero16"
jetCostArith IsZero32 = Benchmarks.cost "IsZero32"
jetCostArith IsZero64 = Benchmarks.cost "IsZero64"
jetCostArith IsOne8 = Benchmarks.cost "IsOne8"
jetCostArith IsOne16 = Benchmarks.cost "IsOne16"
jetCostArith IsOne32 = Benchmarks.cost "IsOne32"
jetCostArith IsOne64 = Benchmarks.cost "IsOne64"
jetCostArith Le8 = Benchmarks.cost "Le8"
jetCostArith Le16 = Benchmarks.cost "Le16"
jetCostArith Le32 = Benchmarks.cost "Le32"
jetCostArith Le64 = Benchmarks.cost "Le64"
jetCostArith Lt8 = Benchmarks.cost "Lt8"
jetCostArith Lt16 = Benchmarks.cost "Lt16"
jetCostArith Lt32 = Benchmarks.cost "Lt32"
jetCostArith Lt64 = Benchmarks.cost "Lt64"
jetCostArith Min8 = Benchmarks.cost "Min8"
jetCostArith Min16 = Benchmarks.cost "Min16"
jetCostArith Min32 = Benchmarks.cost "Min32"
jetCostArith Min64 = Benchmarks.cost "Min64"
jetCostArith Max8 = Benchmarks.cost "Max8"
jetCostArith Max16 = Benchmarks.cost "Max16"
jetCostArith Max32 = Benchmarks.cost "Max32"
jetCostArith Max64 = Benchmarks.cost "Max64"
jetCostArith Median8 = Benchmarks.cost "Median8"
jetCostArith Median16 = Benchmarks.cost "Median16"
jetCostArith Median32 = Benchmarks.cost "Median32"
jetCostArith Median64 = Benchmarks.cost "Median64"
jetCostArith DivMod128_64 = Benchmarks.cost "DivMod128_64"
jetCostArith DivMod8 = Benchmarks.cost "DivMod8"
jetCostArith DivMod16 = Benchmarks.cost "DivMod16"
jetCostArith DivMod32 = Benchmarks.cost "DivMod32"
jetCostArith DivMod64 = Benchmarks.cost "DivMod64"
jetCostArith Divide8 = Benchmarks.cost "Divide8"
jetCostArith Divide16 = Benchmarks.cost "Divide16"
jetCostArith Divide32 = Benchmarks.cost "Divide32"
jetCostArith Divide64 = Benchmarks.cost "Divide64"
jetCostArith Modulo8 = Benchmarks.cost "Modulo8"
jetCostArith Modulo16 = Benchmarks.cost "Modulo16"
jetCostArith Modulo32 = Benchmarks.cost "Modulo32"
jetCostArith Modulo64 = Benchmarks.cost "Modulo64"
jetCostArith Divides8 = Benchmarks.cost "Divides8"
jetCostArith Divides16 = Benchmarks.cost "Divides16"
jetCostArith Divides32 = Benchmarks.cost "Divides32"
jetCostArith Divides64 = Benchmarks.cost "Divides64"

jetCostHash :: HashJet a b -> Weight
jetCostHash Sha256Block = Benchmarks.cost "Sha256Block"
jetCostHash Sha256Iv = Benchmarks.cost "Sha256Iv"
jetCostHash Sha256Ctx8Add1 = Benchmarks.cost "Sha256Ctx8Add1"
jetCostHash Sha256Ctx8Add2 = Benchmarks.cost "Sha256Ctx8Add2"
jetCostHash Sha256Ctx8Add4 = Benchmarks.cost "Sha256Ctx8Add4"
jetCostHash Sha256Ctx8Add8 = Benchmarks.cost "Sha256Ctx8Add8"
jetCostHash Sha256Ctx8Add16 = Benchmarks.cost "Sha256Ctx8Add16"
jetCostHash Sha256Ctx8Add32 = Benchmarks.cost "Sha256Ctx8Add32"
jetCostHash Sha256Ctx8Add64 = Benchmarks.cost "Sha256Ctx8Add64"
jetCostHash Sha256Ctx8Add128 = Benchmarks.cost "Sha256Ctx8Add128"
jetCostHash Sha256Ctx8Add256 = Benchmarks.cost "Sha256Ctx8Add256"
jetCostHash Sha256Ctx8Add512 = Benchmarks.cost "Sha256Ctx8Add512"
jetCostHash Sha256Ctx8AddBuffer511 = Benchmarks.cost "Sha256Ctx8AddBuffer511"
jetCostHash Sha256Ctx8Finalize = Benchmarks.cost "Sha256Ctx8Finalize"
jetCostHash Sha256Ctx8Init = Benchmarks.cost "Sha256Ctx8Init"

jetCostSecp256k1 :: Secp256k1Jet a b -> Weight
jetCostSecp256k1 FeNormalize = Benchmarks.cost "FeNormalize"
jetCostSecp256k1 FeNegate = Benchmarks.cost "FeNegate"
jetCostSecp256k1 FeAdd = Benchmarks.cost "FeAdd"
jetCostSecp256k1 FeSquare = Benchmarks.cost "FeSquare"
jetCostSecp256k1 FeMultiply = Benchmarks.cost "FeMultiply"
jetCostSecp256k1 FeMultiplyBeta = Benchmarks.cost "FeMultiplyBeta"
jetCostSecp256k1 FeInvert = Benchmarks.cost "FeInvert"
jetCostSecp256k1 FeSquareRoot = Benchmarks.cost "FeSquareRoot"
jetCostSecp256k1 FeIsZero = Benchmarks.cost "FeIsZero"
jetCostSecp256k1 FeIsOdd = Benchmarks.cost "FeIsOdd"
jetCostSecp256k1 ScalarNormalize = Benchmarks.cost "ScalarNormalize"
jetCostSecp256k1 ScalarNegate = Benchmarks.cost "ScalarNegate"
jetCostSecp256k1 ScalarAdd = Benchmarks.cost "ScalarAdd"
jetCostSecp256k1 ScalarSquare = Benchmarks.cost "ScalarSquare"
jetCostSecp256k1 ScalarMultiply = Benchmarks.cost "ScalarMultiply"
jetCostSecp256k1 ScalarMultiplyLambda = Benchmarks.cost "ScalarMultiplyLambda"
jetCostSecp256k1 ScalarInvert = Benchmarks.cost "ScalarInvert"
jetCostSecp256k1 ScalarIsZero = Benchmarks.cost "ScalarIsZero"
jetCostSecp256k1 GejInfinity = Benchmarks.cost "GejInfinity"
jetCostSecp256k1 GejNormalize = Benchmarks.cost "GejNormalize"
jetCostSecp256k1 GejNegate = Benchmarks.cost "GejNegate"
jetCostSecp256k1 GeNegate = Benchmarks.cost "GeNegate"
jetCostSecp256k1 GejDouble = Benchmarks.cost "GejDouble"
jetCostSecp256k1 GejAdd = Benchmarks.cost "GejAdd"
jetCostSecp256k1 GejGeAddEx = Benchmarks.cost "GejGeAddEx"
jetCostSecp256k1 GejGeAdd = Benchmarks.cost "GejGeAdd"
jetCostSecp256k1 GejRescale = Benchmarks.cost "GejRescale"
jetCostSecp256k1 GejIsInfinity = Benchmarks.cost "GejIsInfinity"
jetCostSecp256k1 GejEquiv = Benchmarks.cost "GejEquiv"
jetCostSecp256k1 GejGeEquiv = Benchmarks.cost "GejGeEquiv"
jetCostSecp256k1 GejXEquiv = Benchmarks.cost "GejXEquiv"
jetCostSecp256k1 GejYIsOdd = Benchmarks.cost "GejYIsOdd"
jetCostSecp256k1 GejIsOnCurve = Benchmarks.cost "GejIsOnCurve"
jetCostSecp256k1 GeIsOnCurve = Benchmarks.cost "GeIsOnCurve"
jetCostSecp256k1 Generate = Benchmarks.cost "Generate"
jetCostSecp256k1 Scale = Benchmarks.cost "Scale"
jetCostSecp256k1 LinearCombination1 = Benchmarks.cost "LinearCombination1"
jetCostSecp256k1 LinearVerify1 = Benchmarks.cost "LinearVerify1"
jetCostSecp256k1 PointVerify1 = Benchmarks.cost "PointVerify1"
jetCostSecp256k1 Decompress = Benchmarks.cost "Decompress"

jetCostSignature :: SignatureJet a b -> Weight
jetCostSignature CheckSigVerify = Benchmarks.cost "CheckSigVerify"
jetCostSignature Bip0340Verify = Benchmarks.cost "Bip0340Verify"

jetCostBitcoin :: BitcoinJet a b -> Weight
jetCostBitcoin ParseLock = Benchmarks.cost "ParseLock"
jetCostBitcoin ParseSequence = Benchmarks.cost "ParseSequence"

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
instance Show SomeConstWordContent where
  show (SomeConstWordContent cwc) = show cwc

-- | Returns the specification of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
specificationConstWord :: (Core term, TyC b) => ConstWordContent b -> term () b
specificationConstWord (ConstWordContent w v) = scribe (toWord w v)

-- | Returns an implementation of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
implementationConstWord :: ConstWordContent b -> () -> Maybe b
implementationConstWord (ConstWordContent w v) _ = Just (toWord w v)

-- | Returns the cost of a constant word jet corresponding to the contents of a given 'ConstWordContent'.
costConstWord :: ConstWordContent b -> Weight
costConstWord (ConstWordContent w _) = milli (wordSize w)

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
putConstWordBit cwc@(ConstWordContent w v) = putPositive (1 + depth w) . (putConstWordValueBit cwc ++)
 where
  depth :: Word b -> Integer
  depth (SingleV) = 0
  depth (DoubleV w) = 1 + depth w

-- | Given a 'ConstWordContent' of some type, output the serialization of that value.
putConstWordValueBit :: ConstWordContent b -> [Bool]
putConstWordValueBit (ConstWordContent w v) | 0 <= v && v < 2^(wordSize w) =
  List.reverse . List.take (wordSize w) $ List.unfoldr (\i -> Just (odd i, i `div` 2)) v

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

median x y z = List.sort [x,y,z] !! 1
