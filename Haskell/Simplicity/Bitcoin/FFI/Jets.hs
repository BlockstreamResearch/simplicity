-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.Bitcoin.FFI.Jets
 ( version
 , lock_time
 , input_prev_outpoint
 , input_value
 , input_script_hash
 , input_sequence
 , input_annex_hash
 , input_script_sig_hash
 , output_value
 , output_script_hash
 , script_cmr
 , transaction_id
 , current_index
 , current_prev_outpoint
 , current_value
 , current_script_hash
 , current_sequence
 , current_annex_hash
 , current_script_sig_hash
 , tapleaf_version
 , tappath
 , internal_key
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
 , outpoint_hash
 , annex_hash
 , build_tapleaf_simplicity
 , build_tapbranch
 , build_taptweak
 , output_values_hash
 , output_scripts_hash
 , outputs_hash
 , output_hash
 , total_output_value
 , input_outpoints_hash
 , input_values_hash
 , input_scripts_hash
 , input_utxos_hash
 , input_utxo_hash
 , input_sequences_hash
 , input_annexes_hash
 , input_script_sigs_hash
 , inputs_hash
 , input_hash
 , total_input_value
 , fee
 , tx_hash
 , tapleaf_hash
 , tappath_hash
 , tap_env_hash
 , sig_all_hash
 ) where

import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..))

import Simplicity.Bitcoin.FFI.Env
import Simplicity.Bitcoin.Primitive
import Simplicity.FFI.Frame
import Simplicity.Programs.Elements
import Simplicity.Programs.LibSecp256k1
import Simplicity.Ty
import Simplicity.Ty.Word

-- | This cannot be used with jets that access global variables.
unsafeLocalJet :: (TyC a, TyC b) => (Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool) -> PrimEnv -> a -> Maybe b
unsafeLocalJet jet env = unsafeLocalCoreJet (\dst src -> withPrimEnv env (jet dst src))

foreign import ccall unsafe "" c_bitcoin_version :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_prev_outpoint :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_value :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_sequence :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_annex_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_script_sig_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_value :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_script_cmr :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_transaction_id :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_index :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_prev_outpoint :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_value :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_script_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_sequence :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_annex_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_current_script_sig_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tapleaf_version :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tappath :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_internal_key :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_num_inputs :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_num_outputs :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_is_final :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_lock_height :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_lock_distance :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_lock_duration :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_check_lock_height :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_check_lock_time :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_check_lock_distance :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_check_lock_duration :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_outpoint_hash :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bitcoin_annex_hash :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bitcoin_build_tapleaf_simplicity :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bitcoin_build_tapbranch :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bitcoin_build_taptweak :: Ptr FrameItem -> Ptr FrameItem -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_values_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_nonces_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_scripts_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_outputs_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_output_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_total_output_value :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_outpoints_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_values_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_scripts_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_utxos_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_utxo_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_sequences_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_annexes_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_script_sigs_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_inputs_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_input_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_total_input_value :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_fee :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tx_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tapleaf_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tappath_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_tap_env_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool
foreign import ccall unsafe "" c_bitcoin_sig_all_hash :: Ptr FrameItem -> Ptr FrameItem -> Ptr CTxEnv -> IO CBool

version :: PrimEnv -> () -> Maybe Word32
version = unsafeLocalJet c_bitcoin_version

lock_time :: PrimEnv -> () -> Maybe Word32
lock_time = unsafeLocalJet c_bitcoin_lock_time

num_inputs :: PrimEnv -> () -> Maybe Word32
num_inputs = unsafeLocalJet c_bitcoin_num_inputs

input_prev_outpoint :: PrimEnv -> Word32 -> Maybe (S (Word256, Word32))
input_prev_outpoint = unsafeLocalJet c_bitcoin_input_prev_outpoint

input_value :: PrimEnv -> Word32 -> Maybe (S Word64)
input_value = unsafeLocalJet c_bitcoin_input_value

input_script_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
input_script_hash = unsafeLocalJet c_bitcoin_input_script_hash

input_sequence :: PrimEnv -> Word32 -> Maybe (S Word32)
input_sequence = unsafeLocalJet c_bitcoin_input_sequence

input_annex_hash :: PrimEnv -> Word32 -> Maybe (S (S Word256))
input_annex_hash = unsafeLocalJet c_bitcoin_input_annex_hash

input_script_sig_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
input_script_sig_hash = unsafeLocalJet c_bitcoin_input_script_sig_hash

current_index :: PrimEnv -> () -> Maybe Word32
current_index = unsafeLocalJet c_bitcoin_current_index

current_prev_outpoint :: PrimEnv -> () -> Maybe (Word256, Word32)
current_prev_outpoint = unsafeLocalJet c_bitcoin_current_prev_outpoint

current_value :: PrimEnv -> () -> Maybe Word64
current_value = unsafeLocalJet c_bitcoin_current_value

current_script_hash :: PrimEnv -> () -> Maybe Word256
current_script_hash = unsafeLocalJet c_bitcoin_current_script_hash

current_sequence :: PrimEnv -> () -> Maybe Word32
current_sequence = unsafeLocalJet c_bitcoin_current_sequence

current_annex_hash :: PrimEnv -> () -> Maybe (S Word256)
current_annex_hash = unsafeLocalJet c_bitcoin_current_annex_hash

current_script_sig_hash :: PrimEnv -> () -> Maybe Word256
current_script_sig_hash = unsafeLocalJet c_bitcoin_current_script_sig_hash

tapleaf_version :: PrimEnv -> () -> Maybe Word8
tapleaf_version = unsafeLocalJet c_bitcoin_tapleaf_version

tappath :: PrimEnv -> Word8 -> Maybe (S Word256)
tappath = unsafeLocalJet c_bitcoin_tappath

internal_key :: PrimEnv -> () -> Maybe PubKey
internal_key = unsafeLocalJet c_bitcoin_internal_key

num_outputs :: PrimEnv -> () -> Maybe Word32
num_outputs = unsafeLocalJet c_bitcoin_num_outputs

output_value :: PrimEnv -> Word32 -> Maybe (S Word64)
output_value = unsafeLocalJet c_bitcoin_output_value

output_script_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
output_script_hash = unsafeLocalJet c_bitcoin_output_script_hash

script_cmr :: PrimEnv -> () -> Maybe Word256
script_cmr = unsafeLocalJet c_bitcoin_script_cmr

transaction_id :: PrimEnv -> () -> Maybe Word256
transaction_id = unsafeLocalJet c_bitcoin_transaction_id

tx_is_final :: PrimEnv -> () -> Maybe Bit
tx_is_final = unsafeLocalJet c_bitcoin_tx_is_final

tx_lock_height :: PrimEnv -> () -> Maybe Word32
tx_lock_height = unsafeLocalJet c_bitcoin_tx_lock_height

tx_lock_time :: PrimEnv -> () -> Maybe Word32
tx_lock_time = unsafeLocalJet c_bitcoin_tx_lock_time

tx_lock_distance :: PrimEnv -> () -> Maybe Word16
tx_lock_distance  = unsafeLocalJet c_bitcoin_tx_lock_distance

tx_lock_duration :: PrimEnv -> () -> Maybe Word16
tx_lock_duration  = unsafeLocalJet c_bitcoin_tx_lock_duration

check_lock_height :: PrimEnv -> Word32 -> Maybe ()
check_lock_height = unsafeLocalJet c_bitcoin_check_lock_height

check_lock_time :: PrimEnv -> Word32 -> Maybe ()
check_lock_time = unsafeLocalJet c_bitcoin_check_lock_time

check_lock_distance :: PrimEnv -> Word16 -> Maybe ()
check_lock_distance  = unsafeLocalJet c_bitcoin_check_lock_distance

check_lock_duration :: PrimEnv -> Word16 -> Maybe ()
check_lock_duration  = unsafeLocalJet c_bitcoin_check_lock_duration

outpoint_hash :: (Ctx8, (Word256, Word32)) -> Maybe Ctx8
outpoint_hash = unsafeLocalCoreJet c_bitcoin_outpoint_hash

annex_hash :: (Ctx8, S Word256) -> Maybe Ctx8
annex_hash = unsafeLocalCoreJet c_bitcoin_annex_hash

build_tapleaf_simplicity :: Word256 -> Maybe Word256
build_tapleaf_simplicity = unsafeLocalCoreJet c_bitcoin_build_tapleaf_simplicity

build_tapbranch :: (Word256, Word256) -> Maybe Word256
build_tapbranch = unsafeLocalCoreJet c_bitcoin_build_tapbranch

build_taptweak :: (Word256, Word256) -> Maybe Word256
build_taptweak = unsafeLocalCoreJet c_bitcoin_build_taptweak

output_values_hash :: PrimEnv -> () -> Maybe Word256
output_values_hash = unsafeLocalJet c_bitcoin_output_values_hash

output_scripts_hash :: PrimEnv -> () -> Maybe Word256
output_scripts_hash = unsafeLocalJet c_bitcoin_output_scripts_hash

outputs_hash :: PrimEnv -> () -> Maybe Word256
outputs_hash = unsafeLocalJet c_bitcoin_outputs_hash

output_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
output_hash = unsafeLocalJet c_bitcoin_output_hash

total_output_value :: PrimEnv -> () -> Maybe Word64
total_output_value = unsafeLocalJet c_bitcoin_total_output_value

input_outpoints_hash :: PrimEnv -> () -> Maybe Word256
input_outpoints_hash = unsafeLocalJet c_bitcoin_input_outpoints_hash

input_values_hash :: PrimEnv -> () -> Maybe Word256
input_values_hash = unsafeLocalJet c_bitcoin_input_values_hash

input_scripts_hash :: PrimEnv -> () -> Maybe Word256
input_scripts_hash = unsafeLocalJet c_bitcoin_input_scripts_hash

input_utxos_hash :: PrimEnv -> () -> Maybe Word256
input_utxos_hash = unsafeLocalJet c_bitcoin_input_utxos_hash

input_utxo_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
input_utxo_hash = unsafeLocalJet c_bitcoin_input_utxo_hash

input_sequences_hash :: PrimEnv -> () -> Maybe Word256
input_sequences_hash = unsafeLocalJet c_bitcoin_input_sequences_hash

input_annexes_hash :: PrimEnv -> () -> Maybe Word256
input_annexes_hash = unsafeLocalJet c_bitcoin_input_annexes_hash

input_script_sigs_hash :: PrimEnv -> () -> Maybe Word256
input_script_sigs_hash = unsafeLocalJet c_bitcoin_input_script_sigs_hash

inputs_hash :: PrimEnv -> () -> Maybe Word256
inputs_hash = unsafeLocalJet c_bitcoin_inputs_hash

input_hash :: PrimEnv -> Word32 -> Maybe (S Word256)
input_hash = unsafeLocalJet c_bitcoin_input_hash

total_input_value :: PrimEnv -> () -> Maybe Word64
total_input_value = unsafeLocalJet c_bitcoin_total_input_value

fee :: PrimEnv -> () -> Maybe Word64
fee = unsafeLocalJet c_bitcoin_fee

tx_hash :: PrimEnv -> () -> Maybe Word256
tx_hash = unsafeLocalJet c_bitcoin_tx_hash

tapleaf_hash :: PrimEnv -> () -> Maybe Word256
tapleaf_hash = unsafeLocalJet c_bitcoin_tapleaf_hash

tappath_hash :: PrimEnv -> () -> Maybe Word256
tappath_hash = unsafeLocalJet c_bitcoin_tappath_hash

tap_env_hash :: PrimEnv -> () -> Maybe Word256
tap_env_hash = unsafeLocalJet c_bitcoin_tap_env_hash

sig_all_hash :: PrimEnv -> () -> Maybe Word256
sig_all_hash = unsafeLocalJet c_bitcoin_sig_all_hash
