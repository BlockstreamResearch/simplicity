-- | A little program that can be used to make a test network transactions on liquid testnet or other regtest networks.
-- See <https://asciinema.org/a/684459> for a walkthrogh on how to use it.
module TestnetTransaction where

import Control.Monad (guard)
import qualified Data.Array as Arr
import Data.Bits (Bits, testBit, unsafeShiftL, unsafeShiftR, xor, (.&.), (.|.))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Char8 as BSC
import Data.Char (toLower, toUpper)
import Data.Foldable (foldl')
import Data.Functor.Identity (Identity, runIdentity)
import Data.Ix (Ix (..))
import Data.Word (Word8)

import Data.List (intercalate)
import Data.String (fromString)
import Data.Serialize (decode, encode, runPut)
import Data.Vector (fromList)
import Numeric (readHex, showHex)
import Lens.Family2 ((^.), review, over)
import System.IO (BufferMode(NoBuffering), hSetBuffering, stdin, stdout)
import System.Entropy (getEntropy)
import Simplicity.Digest (Hash256, le256, be256, bsHash, integerHash256)
import Simplicity.LibSecp256k1.Spec ( PubKey(PubKey), GE(GE), Point(Point), Sig(Sig)
                                    , g, gej_normalize, gej_ge_add_ex, scale, scalar
                                    , pubkey_unpack, decompress, groupOrder, fe_pack, fe_is_odd
                                    , linear_combination_1, ge_to_gej
                                    )
import Simplicity.Word (Word256)
import Simplicity.MerkleRoot (CommitmentRoot, commitmentRoot)
import Simplicity.Programs.Generic (scribe)
import Simplicity.Programs.CheckSig.Lib (checkSigVerify')
import Simplicity.Serialization (putBitStream)
import Simplicity.Elements.Jets (jetSubst, pruneSubst, fastEval, unwrap, putTermLengthCode)
import Simplicity.Elements.Programs.SigHash.Lib (sigAllHash)
import Simplicity.Elements.DataTypes ( Asset, asset, Amount, amount, clearAssetPrf
                                     , Nonce(Nonce), Confidential(Explicit), Outpoint(Outpoint)
                                     , UTXO(..), SigTxInput(..), TxOutput(..), SigTx(..)
                                     , TapEnv(..)
                                     )
import Simplicity.Elements.Primitive (primEnv)
import qualified Simplicity.Ty.Word

import Data.List (sort)

-- # Bech 32
-- Adapted from https://github.com/sipa/bech32/blob/842b49701067c585762a7b6550439d2d5f4918ad/ref/haskell/src/Codec/Binary/Bech32.hs
-- Copyright (c) 2017 Marko Bencun
--
-- Permission is hereby granted, free of charge, to any person obtaining a copy
-- of this software and associated documentation files (the "Software"), to deal
-- in the Software without restriction, including without limitation the rights
-- to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the Software is
-- furnished to do so, subject to the following conditions:
--
-- The above copyright notice and this permission notice shall be included in
-- all copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
-- FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
-- AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
-- LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
-- OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
-- THE SOFTWARE.

type HRP = BS.ByteString
type Data = [Word8]

(.>>.), (.<<.) :: Bits a => a -> Int -> a
(.>>.) = unsafeShiftR
(.<<.) = unsafeShiftL

newtype Word5 = UnsafeWord5 Word8
              deriving (Eq, Ord, Show)

instance Ix Word5 where
  range (UnsafeWord5 m, UnsafeWord5 n) = map UnsafeWord5 $ range (m, n)
  index (UnsafeWord5 m, UnsafeWord5 n) (UnsafeWord5 i) = index (m, n) i
  inRange (m,n) i = m <= i && i <= n

word5 :: Integral a => a -> Word5
word5 x = UnsafeWord5 ((fromIntegral x) .&. 31)
{-# INLINE word5 #-}
{-# SPECIALIZE INLINE word5 :: Word8 -> Word5 #-}

fromWord5 :: Num a => Word5 -> a
fromWord5 (UnsafeWord5 x) = fromIntegral x
{-# INLINE fromWord5 #-}
{-# SPECIALIZE INLINE fromWord5 :: Word5 -> Word8 #-}

charset :: Arr.Array Word5 Char
charset = Arr.listArray (UnsafeWord5 0, UnsafeWord5 31) "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

charsetMap :: Char -> Maybe Word5
charsetMap c | inRange (Arr.bounds inv) upperC = inv Arr.! upperC
             | otherwise = Nothing
  where
    upperC = toUpper c
    inv = Arr.listArray ('0', 'Z') (repeat Nothing) Arr.// (map swap (Arr.assocs charset))
    swap (a, b) = (toUpper b, Just a)

bech32Polymod :: [Word5] -> Word
bech32Polymod values = foldl' go 1 values .&. 0x3fffffff
  where
    go chk value = foldl' xor chk' [g | (g, i) <- zip generator [25..], testBit chk i]
      where
        generator = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
        chk' = chk .<<. 5 `xor` (fromWord5 value)

bech32HRPExpand :: HRP -> [Word5]
bech32HRPExpand hrp = map (UnsafeWord5 . (.>>. 5)) (BS.unpack hrp) ++ [UnsafeWord5 0] ++ map word5 (BS.unpack hrp)

bech32CreateChecksum :: Word -> HRP -> [Word5] -> [Word5]
bech32CreateChecksum spec hrp dat = [word5 (polymod .>>. i) | i <- [25,20..0]]
  where
    values = bech32HRPExpand hrp ++ dat
    polymod = bech32Polymod (values ++ map UnsafeWord5 [0, 0, 0, 0, 0, 0]) `xor` spec

bech32VerifyChecksum :: HRP -> [Word5] -> Word
bech32VerifyChecksum hrp dat = bech32Polymod (bech32HRPExpand hrp ++ dat)

data EncodeError =
      ResultStringLengthExceeded
    | InvalidHumanReadablePart
    deriving (Show, Eq)

bech32Encode :: Word -> HRP -> [Word5] -> Either EncodeError BS.ByteString
bech32Encode spec hrp dat = do
    verify InvalidHumanReadablePart $ validHRP hrp
    let dat' = dat ++ bech32CreateChecksum spec hrp dat
        rest = map (charset Arr.!) dat'
        result = BSC.concat [BSC.map toLower hrp, BSC.pack "1", BSC.pack rest]
    verify ResultStringLengthExceeded $ BS.length result <= 90
    return result

validHRP :: BS.ByteString -> Bool
validHRP hrp = not (BS.null hrp) && BS.all (\char -> char >= 33 && char <= 126) hrp

data DecodeError =
    Bech32StringLengthExceeded
  | CaseInconsistency
  | TooShortDataPart
  | InvalidHRP
  | ChecksumVerificationFail
  | InvalidCharsetMap
  deriving (Show, Eq)

bech32Decode :: BS.ByteString -> Either DecodeError (Word, HRP, [Word5])
bech32Decode bech32 = do
    verify Bech32StringLengthExceeded $ BS.length bech32 <= 90
    verify CaseInconsistency $ validCase bech32
    let (hrp, dat) = BSC.breakEnd (== '1') $ BSC.map toLower bech32
    verify TooShortDataPart $ BS.length dat >= 6
    hrp' <- maybeToRight InvalidHRP $ BSC.stripSuffix (BSC.pack "1") hrp
    verify InvalidHRP $ validHRP hrp'
    dat' <- maybeToRight InvalidCharsetMap . mapM charsetMap $ BSC.unpack dat
    let spec = bech32VerifyChecksum hrp' dat'
    return (spec, hrp', take (BS.length dat - 6) dat')
      where
        validCase :: BS.ByteString -> Bool
        validCase b32 = BSC.map toUpper b32 == b32 || BSC.map toLower b32 == b32

type Pad f = Int -> Int -> Word -> [[Word]] -> f [[Word]]

yesPadding :: Pad Identity
yesPadding _ 0 _ result        = return result
yesPadding _ _ padValue result = return $ [padValue] : result
{-# INLINE yesPadding #-}

noPadding :: Pad Maybe
noPadding frombits bits padValue result = do
    guard $ bits < frombits && padValue == 0
    return result
{-# INLINE noPadding #-}

-- Big endian conversion of a bytestring from base 2^frombits to base 2^tobits.
-- frombits and twobits must be positive and 2^frombits and 2^tobits must be smaller than the size of Word.
-- Every value in dat must be strictly smaller than 2^frombits.
convertBits :: Functor f => [Word] -> Int -> Int -> Pad f -> f [Word]
convertBits dat frombits tobits pad = fmap (concat . reverse) $ go dat 0 0 []
  where
    go [] acc bits result =
        let padValue = (acc .<<. (tobits - bits)) .&. maxv
        in pad frombits bits padValue result
    go (value:dat') acc bits result = go dat' acc' (bits' `rem` tobits) (result':result)
      where
        acc' = (acc .<<. frombits) .|. fromIntegral value
        bits' = bits + frombits
        result' = [(acc' .>>. b) .&. maxv | b <- [bits'-tobits,bits'-2*tobits..0]]
    maxv = (1 .<<. tobits) - 1
{-# INLINE convertBits #-}

toBase32 :: [Word8] -> [Word5]
toBase32 dat = map word5 $ runIdentity $ convertBits (map fromIntegral dat) 8 5 yesPadding

toBase256 :: [Word5] -> Maybe [Word8]
toBase256 dat = fmap (map fromIntegral) $ convertBits (map fromWord5 dat) 5 8 noPadding

segwitCheck :: Word8 -> Data -> Maybe Word
segwitCheck witver witprog = do
    guard $ witver <= 16
    if witver == 0
    then guard (length witprog == 20 || length witprog == 32) >> return 1
    else guard (length witprog >= 2 && length witprog <= 40) >> return bech32mConst
 where
  bech32mConst = 0x2bc830a3

segwitDecode :: HRP -> BS.ByteString -> Maybe (Word8, Data)
segwitDecode hrp addr = do
    (spec', hrp', dat) <- rightToMaybe $ bech32Decode addr
    guard $ (hrp == hrp') && not (null dat)
    let (UnsafeWord5 witver : datBase32) = dat
    decoded <- toBase256 datBase32
    spec <- segwitCheck witver decoded
    guard $ spec == spec'
    return (witver, decoded)

segwitEncode :: HRP -> Word8 -> Data -> Maybe BS.ByteString
segwitEncode hrp witver witprog = do
    spec <- segwitCheck witver witprog
    rightToMaybe $ bech32Encode spec hrp $ UnsafeWord5 witver : toBase32 witprog

rightToMaybe :: Either l r -> Maybe r
rightToMaybe = either (const Nothing) Just

maybeToRight :: l -> Maybe r -> Either l r
maybeToRight l = maybe (Left l) Right

verify :: a -> Bool -> Either a ()
verify _ True  = Right ()
verify v False = Left v

-- Construct an Elements regtest non-blinded address for a segwit program
texScriptPubKey :: Word8 -> Data -> BSL.ByteString
texScriptPubKey segver prog | 2 <= len && len <= 40 = BSL.singleton encver <> BSL.singleton len <> (BSL.pack prog)
 where
  len = fromIntegral (length prog)
  encver | segver == 0 = 0
         | segver <= 16 = 80 + segver

-- # Taproot constructions

-- Construct a tapleaf hash for a given "script" for a given leaf version.
tapleafHash :: Word8 -> BS.ByteString -> Hash256
tapleafHash leafver script | even leafver = bsHash
                                         $ encode tag <> encode tag
                                        <> BS.singleton leafver <> compactSize script <> script
 where
  tag = bsHash (fromString "TapLeaf/elements")
  compactSize str | size < 0xfd = BS.singleton (fromIntegral size)
   where
    size = BS.length str

-- TapPath contains the data relevant for a taproot address supporting a single tapleaf program.
-- It contains the taproot output key, the control block connecting to the leaf, and the script at that leaf
data TapPath = TapPath { outputKey :: PubKey
                       , controlBlock :: BS.ByteString
                       , script :: BS.ByteString
                       }

-- Create a TapPath for a taproot program.
tapPath ::  Word8 -> BS.ByteString -> [Hash256] -> PubKey -> Maybe TapPath
tapPath leafver script path internalKey | even leafver = do
  pt <- pubkey_unpack internalKey
  p <- decompress pt
  guard (tweak < groupOrder)
  let Just ge = (do s <- scale (scalar tweak) g
                    gej_normalize (snd (gej_ge_add_ex s p)))
  let Point b x = compress ge
  let cb = BS.singleton (leafver .|. if b then 1 else 0) <> encode internalKey <> foldMap encode path
  return $ TapPath { outputKey = PubKey (fe_pack x), controlBlock = cb, script = script }
 where
  leafHash = tapleafHash leafver script
  branch h1 h2 = bsHash $ encode branchtag <> encode branchtag <> encode a <> encode b
   where
    branchtag = bsHash (fromString "TapBranch/elements")
    [a,b] = sort [h1, h2]
  rootHash = foldl branch leafHash path
  tag = bsHash (fromString "TapTweak/elements")
  tweak = integerHash256 . bsHash $ encode tag <> encode tag <> encode internalKey <> encode rootHash
  compress (GE x y) = Point (fe_is_odd y) x

-- # Misc.

hexString :: BS.ByteString -> String
hexString str = (\s -> replicate (2-length s) '0' ++ s) . flip showHex "" =<< BS.unpack str

getHexLine :: (Show a, Integral a) => String -> Int -> Maybe a -> IO a
getHexLine prompt digits mdef = do
  putStr (showString prompt . maybe id (\def -> showString " " . showParen True (showHex def)) mdef $ "? ")
  str <- getLine
  case (str, mdef) of
    ("", Just x) -> return x
    otherwise -> do
      guard $ digits == length str
      let [(x,"")] = readHex str
      return x

getIntLine :: (Read a, Integral a) => String -> IO a
getIntLine prompt = do
  putStr $ prompt ++ "? "
  readLn

getStrLine :: String -> String -> IO String
getStrLine prompt def = do
  putStr $ prompt ++ " (" ++ def ++ ")? "
  str <- getLine
  return $ if null str then def else str

-- This is an standard unspendable public key with no known private key as defined in BIP-0341.
unspendablePubKey tweak = PubKey (fe_pack x)
 where
  Just unspendable = pubkey_unpack (PubKey 0x50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0) >>= decompress
  Just (GE x _) = linear_combination_1 (scalar 1) (ge_to_gej unspendable) tweak >>= gej_normalize

-- This is an example Pubkey.  It has a well know private key.  DO NOT USE for anything but testing.
insecurePubKey = PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63

-- DO NOT USE!
-- This is for testing purposes only.
-- Do not even copy this function and try to "fix it" to make it work.
-- It is insecure.  It uses an insecure nonce; it signs only for insecurePubKey.
-- DO NOT USE!
-- For production purposes you need to use proper bindings to <https://github.com/bitcoin-core/secp256k1>.
insecureSign :: Hash256 -> Sig
insecureSign msg = Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
                       (fromInteger ((k * (1 + e)) `mod` order))
 where
  order = groupOrder
  k = 1 + fromInteger order `div` 2
  tag = encode . Simplicity.Digest.bsHash $ Data.String.fromString "BIP0340/challenge"
  e = integerHash256 . bsHash $ tag <> tag <> encode insecurePubKey <> encode insecurePubKey <> encode msg

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering

  -- Randomize the taproot internal key for privacy.
  Right randomTweak <- decode <$> getEntropy 32
  tweak <- scalar <$> getHexLine "Random privacy tweak" 64 (Just (toInteger (randomTweak :: Word256)))
  let internalKey = unspendablePubKey tweak
  putStr "Internal " >> print internalKey

  -- A generic checksig program written in Simplicity, optimized with jets.
  -- Works on an arbitrary sighash function.  Requires a public key and a signature.
  -- This program is the standard single key Simpliciy program.
  let optCheckSig sighash sig pubkey = jetSubst $ checkSigVerify' sighash pubkey sig

  -- Compute the commitment Merkle root (CMR) of this standard program.
  -- We need to fill in a dummy sighash an a dummy signature,
  -- but the CMR only depends on the pubkey.
  let standardCMR pubkey = let { dummySig = Sig 0 0
                               ; dummySigHash = scribe (Simplicity.Ty.Word.toWord256 0)
                               }
                            in commitmentRoot . unwrap $ optCheckSig dummySigHash dummySig pubkey
  let path = review (over be256) <$> [{-path goes here-}]
  -- Compute a taproot for this standard program.
  -- 0xbe is the tapleaf version we have chosen for Simplicity.
  let standardTR pubkey = tapPath 0xbe (encode (standardCMR pubkey)) path internalKey

  -- In our example we will be using "insecurePubKey" as our public key.
  let p = insecurePubKey

  putStr "Simplicity " >> print p

  -- Compute the CMR of the standard program for our chosen key.
  let cmrP = standardCMR p

  -- Compute the taproot for the standard program for our chosen key.
  let Just trP = standardTR p

  -- compute the address for our standard program for our chosen key.
  let Just simplicityAddress = segwitEncode (fromString "tex") 0x01 (BS.unpack . encode $ outputKey trP)

  putStr "Example simplicity address: " >> BSC.putStrLn simplicityAddress
  putStrLn "Press ⏎ to continue."
  getLine

  -- When funds are send to this address we will want to spend this.
  -- In this spending example the entire funds in a UTXO are send to another address, less fees.
  -- We could sign with the taproot key path; that does not require the use of Simplicity.
  -- However, in this example we will show how to use the Simplicity spending path to redeem funds.

  -- To spend funds we need to choose a sighash algorithm.
  -- Unlike Bitcoin script there is no fixed choice; we can program any sighash function we want.
  -- In this example we will be using Simplicity's version similar to sigAllHash.
  -- Optimize the sigAllHash program with jets.
  let optSigAllHash = jetSubst sigAllHash

  -- By default use Liquid testnet's genesis hash
  genesisHash <- review (over le256) <$> getHexLine "Chain's Genesis Hash" 64 (Just 0xa771da8e52ee6ad581ed1e9a99825e5b3b7992225534eaa2ae23244fe26ab1c1)
  -- To spend funds we need the UTXO data, including the txid, vout, asset id and amount.
  inputTxid <- getHexLine "Input's TXID" 64 Nothing
  inputVout <- getIntLine "Input's vout"
  -- By default use Liquid testnet's tl-btc asset
  assetId <- review (over asset) . Explicit . review (over le256) <$> getHexLine "Input's asset ID" 64 (Just 0x144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49)
  inputAmount <- getIntLine "Input's value in sats"
  let inputUtxo = UTXO { utxoAsset = clearAssetPrf assetId
                       , utxoAmount = review (over amount) . Explicit $ inputAmount
                       , utxoScript = texScriptPubKey 1 (BS.unpack . encode $ outputKey trP)
                       }

  -- By default use Liquid testnet's faucet as the (unblinded) output address
  outputAddress <- getStrLine "Output's address" "tex1qyh6tyhspd9w8jhqee8a2uzvyk9lnwp2n8ssur0"
  let Just outputScript = uncurry texScriptPubKey <$> segwitDecode (fromString "tex") (fromString outputAddress)
  fee <- getIntLine "fee in sats"
  let outputAmount = inputAmount-fee
  guard (0 < outputAmount)
  -- Construct the output script from the given address.

  -- Construct the transaction data, including inputs and outputs, including the explicit fee required by Elements.
  -- We assume a standard sequence number.
  let inputSequence = 0xfffffffe
  let input0 = SigTxInput { sigTxiAnnex = Nothing
                          , sigTxiPegin = Nothing
                          , sigTxiPreviousOutpoint = Outpoint (review (over le256) inputTxid) inputVout
                          , sigTxiTxo = inputUtxo
                          , sigTxiSequence = inputSequence
                          , sigTxiIssuance = Nothing
                          , sigTxiScriptSig = mempty
                          }
  let output0 = TxOutput { txoAsset = assetId
                         , txoAmount = review (over amount) . Explicit $ outputAmount
                         , txoNonce = Nothing
                         , txoScript = outputScript
                         }
  let output1 = TxOutput { txoAsset = assetId
                         , txoAmount = review (over amount) . Explicit $ fee
                         , txoNonce = Nothing
                         , txoScript = mempty
                         }
  let tx = SigTx { sigTxVersion = 0x00000002
                 , sigTxIn = fromList [input0]
                 , sigTxOut = fromList [output0, output1]
                 , sigTxLock = 0
                 }

  -- Define our taproot environment.
  let tapEnv = TapEnv
         { tapleafVersion = 0xbe
         , tapInternalKey = internalKey
         , tappath = path
         , tapScriptCMR = cmrP
         }

  -- The signing environment includes the transaction data and which input we are signing for.
  let ix = 0
  let Just env = primEnv tx ix tapEnv genesisHash

  -- Run our optimized sigAllHash function in this environment to compute the transaction hash we are going to be signing.
  let Just txSigAllHash = fromInteger . Simplicity.Ty.Word.fromWord256 <$> fastEval (unwrap optSigAllHash) env () :: Maybe Word256

  -- Our message is a tagged hash that covers both the CMR of our chosen sighash algorithm, and the output of that algorithm.
  let msg = let tag = bsHash (fromString "Simplicity\USSignature")
             in bsHash $ encode tag <> encode tag
                      <> encode (commitmentRoot . unwrap $ optSigAllHash)
                      <> encode (txSigAllHash :: Word256)

  -- Create a BIP-0340 signature for our insecure pubkey using an insecure signing algorithm.
  -- This is for demonstration purposes only.  DO NOT USE!
  let sig = insecureSign msg

  -- Create our optimized checkSig simplicity program with our chosen hash algorithm and the signature we computed.
  -- Encode this program in Simplicity's binary format.
  let Just (bin,wit) = putTermLengthCode . unwrap <$> pruneSubst (checkSigVerify' (unwrap optSigAllHash) p sig) env
  let binary = runPut . putBitStream $ bin
  let witness = runPut . putBitStream $ wit

  -- The witness stack consists of (1) the binary program (2) the CMR of our program, and (3) the taproot control block.
  putStrLn $ "--final-script-witness " ++ intercalate "," (hexString <$> [witness, binary, script trP, controlBlock trP])
