-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.Elements.FFI.Jets
 ( version
 , lock_time
 , input_is_pegin
 , input_prev_outpoint
 , input_asset
 , input_amount
 , input_script_hash
 , input_sequence
 , input_reissuance_blinding
 , input_new_issuance_contract
 , input_reissuance_entropy
 , input_issuance_asset_amt
 , input_issuance_token_amt
 , input_issuance_asset_proof
 , input_issuance_token_proof
 , output_asset
 , output_amount
 , output_nonce
 , output_script_hash
 , output_null_datum
 , output_surjection_proof
 , output_range_proof
 , script_cmr
 , current_index
 , current_is_pegin
 , current_prev_outpoint
 , current_asset
 , current_amount
 , current_script_hash
 , current_sequence
 , current_reissuance_blinding
 , current_new_issuance_contract
 , current_reissuance_entropy
 , current_issuance_asset_amt
 , current_issuance_token_amt
 , current_issuance_asset_proof
 , current_issuance_token_proof
 , tapleaf_version
 , tapbranch
 , internal_key
 , annex_hash
 , inputs_hash
 , outputs_hash
 , num_inputs
 , num_outputs
 , tx_is_final
 , tx_lock_height
 , tx_lock_time
 , tx_lock_distance
 , tx_lock_duration
 , check_lock_height
 , check_lock_time
 , check_lock_distance
 , check_lock_duration
 , calculate_issuance_entropy
 , calculate_asset
 , calculate_explicit_token
 , calculate_confidential_token
 , input_issuance
 , input_issuance_entropy
 , input_issuance_asset
 , input_issuance_token
 ) where

import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..))

import Simplicity.Elements.FFI.Env
import Simplicity.Elements.Primitive
import Simplicity.FFI.Frame
import Simplicity.Programs.Elements
import Simplicity.Programs.LibSecp256k1
import Simplicity.Ty
import Simplicity.Ty.Word

-- | This cannot be used with jets that access global variables.
unsafeLocalJet :: (TyC a, TyC b) => (Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool) -> PrimEnv -> a -> Maybe b
unsafeLocalJet jet env = unsafeLocalCoreJet (\dst src -> withPrimEnv env (jet dst src))

foreign import ccall unsafe "" c_version :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_is_pegin :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_prev_outpoint :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_asset :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_amount :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_sequence :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_reissuance_blinding :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_new_issuance_contract :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_reissuance_entropy :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_asset_amt :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_token_amt :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_asset_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_token_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_asset :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_amount :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_nonce :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_null_datum :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_surjection_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_output_range_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_script_cmr :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_index :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_is_pegin :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_prev_outpoint :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_asset :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_amount :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_sequence :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_reissuance_blinding :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_new_issuance_contract :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_reissuance_entropy :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_issuance_asset_amt :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_issuance_token_amt :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_issuance_asset_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_current_issuance_token_proof :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tapleaf_version :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tapbranch :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_internal_key :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_annex_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_inputs_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_outputs_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_num_inputs :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_num_outputs :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tx_is_final :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tx_lock_height :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tx_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tx_lock_distance :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_tx_lock_duration :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_check_lock_height :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_check_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_check_lock_distance :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_check_lock_duration :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_calculate_issuance_entropy :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_calculate_asset :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_calculate_explicit_token :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_calculate_confidential_token :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_input_issuance :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_entropy :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_asset :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_input_issuance_token :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool

version :: PrimEnv -> () -> Maybe Word32
version = unsafeLocalJet c_version

lock_time :: PrimEnv -> () -> Maybe Word32
lock_time = unsafeLocalJet c_lock_time

inputs_hash :: PrimEnv -> () -> Maybe Word256
inputs_hash = unsafeLocalJet c_inputs_hash

outputs_hash :: PrimEnv -> () -> Maybe Word256
outputs_hash = unsafeLocalJet c_outputs_hash

num_inputs :: PrimEnv -> () -> Maybe Word32
num_inputs = unsafeLocalJet c_num_inputs

input_is_pegin :: PrimEnv -> Word32 -> Maybe (S Bit)
input_is_pegin = unsafeLocalJet c_input_is_pegin

input_prev_outpoint :: PrimEnv -> Word32 -> Maybe (S (Word256, Word32))
input_prev_outpoint = unsafeLocalJet c_input_prev_outpoint

input_asset :: PrimEnv -> Word32 -> Maybe (S (Conf Word256))
input_asset = unsafeLocalJet c_input_asset

input_amount :: PrimEnv -> Word32 -> Maybe (S (Conf Word64))
input_amount = unsafeLocalJet c_input_amount

input_script_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
input_script_hash = unsafeLocalJet c_input_script_hash

input_sequence :: PrimEnv -> Word32 -> Maybe (S Word32)
input_sequence = unsafeLocalJet c_input_sequence

input_reissuance_blinding :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_reissuance_blinding = unsafeLocalJet c_input_reissuance_blinding

input_new_issuance_contract :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_new_issuance_contract = unsafeLocalJet c_input_new_issuance_contract

input_reissuance_entropy :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_reissuance_entropy = unsafeLocalJet c_input_reissuance_entropy

input_issuance_asset_amt :: PrimEnv -> Word32 -> Maybe (S (S (Conf Word64)))
input_issuance_asset_amt = unsafeLocalJet c_input_issuance_asset_amt

input_issuance_token_amt :: PrimEnv -> Word32 -> Maybe (S (S (Conf Word64)))
input_issuance_token_amt = unsafeLocalJet c_input_issuance_token_amt

input_issuance_asset_proof :: PrimEnv -> Word32 -> Maybe (S Word256)
input_issuance_asset_proof = unsafeLocalJet c_input_issuance_asset_proof

input_issuance_token_proof :: PrimEnv -> Word32 -> Maybe (S Word256)
input_issuance_token_proof = unsafeLocalJet c_input_issuance_token_proof

current_index :: PrimEnv -> () -> Maybe Word32
current_index = unsafeLocalJet c_current_index

current_is_pegin :: PrimEnv -> () -> Maybe Bit
current_is_pegin = unsafeLocalJet c_current_is_pegin

current_prev_outpoint :: PrimEnv -> () -> Maybe (Word256, Word32)
current_prev_outpoint = unsafeLocalJet c_current_prev_outpoint

current_asset :: PrimEnv -> () -> Maybe (Conf Word256)
current_asset = unsafeLocalJet c_current_asset

current_amount :: PrimEnv -> () -> Maybe (Conf Word64)
current_amount = unsafeLocalJet c_current_amount

current_script_hash :: PrimEnv -> () -> Maybe Word256
current_script_hash = unsafeLocalJet c_current_script_hash

current_sequence :: PrimEnv -> () -> Maybe Word32
current_sequence = unsafeLocalJet c_current_sequence

current_reissuance_blinding :: PrimEnv -> () -> Maybe (S Word256)
current_reissuance_blinding = unsafeLocalJet c_current_reissuance_blinding

current_new_issuance_contract :: PrimEnv -> () -> Maybe (S Word256)
current_new_issuance_contract = unsafeLocalJet c_current_new_issuance_contract

current_reissuance_entropy :: PrimEnv -> () -> Maybe (S Word256)
current_reissuance_entropy = unsafeLocalJet c_current_reissuance_entropy

current_issuance_asset_amt :: PrimEnv -> () -> Maybe (S (Conf Word64))
current_issuance_asset_amt = unsafeLocalJet c_current_issuance_asset_amt

current_issuance_token_amt :: PrimEnv -> () -> Maybe (S (Conf Word64))
current_issuance_token_amt = unsafeLocalJet c_current_issuance_token_amt

current_issuance_asset_proof :: PrimEnv -> () -> Maybe Word256
current_issuance_asset_proof = unsafeLocalJet c_current_issuance_asset_proof

current_issuance_token_proof :: PrimEnv -> () -> Maybe Word256
current_issuance_token_proof = unsafeLocalJet c_current_issuance_token_proof

tapleaf_version :: PrimEnv -> () -> Maybe Word8
tapleaf_version = unsafeLocalJet c_tapleaf_version

tapbranch :: PrimEnv -> Word8 -> Maybe (S Word256)
tapbranch = unsafeLocalJet c_tapbranch

internal_key :: PrimEnv -> () -> Maybe PubKey
internal_key = unsafeLocalJet c_internal_key

annex_hash :: PrimEnv -> () -> Maybe (S Word256)
annex_hash = unsafeLocalJet c_annex_hash

num_outputs :: PrimEnv -> () -> Maybe Word32
num_outputs = unsafeLocalJet c_num_outputs

output_asset :: PrimEnv -> Word32 -> Maybe (S (Conf Word256))
output_asset = unsafeLocalJet c_output_asset

output_amount :: PrimEnv -> Word32 -> Maybe (S (Conf Word64))
output_amount = unsafeLocalJet c_output_amount

output_nonce :: PrimEnv -> Word32 -> Maybe (S (S (Conf Word256)))
output_nonce = unsafeLocalJet c_output_nonce

output_script_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
output_script_hash = unsafeLocalJet c_output_script_hash

output_null_datum :: PrimEnv -> (Word32,Word32) -> Maybe (S (S (Either (Word2, Word256) (Either Bit Word4))))
output_null_datum = unsafeLocalJet c_output_null_datum

output_surjection_proof :: PrimEnv -> Word32 -> Maybe (S Word256)
output_surjection_proof = unsafeLocalJet c_output_surjection_proof

output_range_proof :: PrimEnv -> Word32 -> Maybe (S Word256)
output_range_proof = unsafeLocalJet c_output_range_proof

-- fee :: PrimEnv -> Word256 -> Maybe Word64

script_cmr :: PrimEnv -> () -> Maybe Word256
script_cmr = unsafeLocalJet c_script_cmr

tx_is_final :: PrimEnv -> () -> Maybe Bit
tx_is_final = unsafeLocalJet c_tx_is_final

tx_lock_height :: PrimEnv -> () -> Maybe Word32
tx_lock_height = unsafeLocalJet c_tx_lock_height

tx_lock_time :: PrimEnv -> () -> Maybe Word32
tx_lock_time = unsafeLocalJet c_tx_lock_time

tx_lock_distance :: PrimEnv -> () -> Maybe Word16
tx_lock_distance  = unsafeLocalJet c_tx_lock_distance

tx_lock_duration :: PrimEnv -> () -> Maybe Word16
tx_lock_duration  = unsafeLocalJet c_tx_lock_duration

check_lock_height :: PrimEnv -> Word32 -> Maybe ()
check_lock_height = unsafeLocalJet c_check_lock_height

check_lock_time :: PrimEnv -> Word32 -> Maybe ()
check_lock_time = unsafeLocalJet c_check_lock_time

check_lock_distance :: PrimEnv -> Word16 -> Maybe ()
check_lock_distance  = unsafeLocalJet c_check_lock_distance

check_lock_duration :: PrimEnv -> Word16 -> Maybe ()
check_lock_duration  = unsafeLocalJet c_check_lock_duration

calculate_issuance_entropy :: ((Word256, Word32), Word256) -> Maybe Word256
calculate_issuance_entropy = unsafeLocalCoreJet c_calculate_issuance_entropy

calculate_asset :: Word256 -> Maybe Word256
calculate_asset = unsafeLocalCoreJet c_calculate_asset

calculate_explicit_token :: Word256 -> Maybe Word256
calculate_explicit_token = unsafeLocalCoreJet c_calculate_explicit_token

calculate_confidential_token :: Word256 -> Maybe Word256
calculate_confidential_token = unsafeLocalCoreJet c_calculate_confidential_token

input_issuance :: PrimEnv -> Word32 -> Maybe (S (S Bit))
input_issuance = unsafeLocalJet c_input_issuance

input_issuance_entropy :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_issuance_entropy = unsafeLocalJet c_input_issuance_entropy

input_issuance_asset :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_issuance_asset = unsafeLocalJet c_input_issuance_asset

input_issuance_token :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_issuance_token = unsafeLocalJet c_input_issuance_token
