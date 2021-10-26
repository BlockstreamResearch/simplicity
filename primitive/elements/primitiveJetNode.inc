/* This file has been automatically generated. */
[MULTIPLY_32] =
{ .tag = JET
, .jet = multiply_32
, .sourceIx = ty_w64
, .targetIx = ty_w64
}
,[FULL_ADD_32] =
{ .tag = JET
, .jet = full_add_32
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
}
,[FULL_SUBTRACT_32] =
{ .tag = JET
, .jet = full_subtract_32
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
}
,[FULL_MULTIPLY_32] =
{ .tag = JET
, .jet = full_multiply_32
, .sourceIx = ty_w128
, .targetIx = ty_w64
}
,[SHA_256_BLOCK] =
{ .tag = JET
, .jet = sha_256_block
, .sourceIx = ty_pw256w512
, .targetIx = ty_w256
}
,[ADD_32] =
{ .tag = JET
, .jet = add_32
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
}
,[SUBTRACT_32] =
{ .tag = JET
, .jet = subtract_32
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
}
,[VERSION] =
{ .tag = JET
, .jet = version
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[LOCK_TIME] =
{ .tag = JET
, .jet = lock_time
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[INPUT_IS_PEGIN] =
{ .tag = JET
, .jet = input_is_pegin
, .sourceIx = ty_w32
, .targetIx = ty_mb
}
,[INPUT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = input_prev_outpoint
, .sourceIx = ty_w32
, .targetIx = ty_mpw256w32
}
,[INPUT_ASSET] =
{ .tag = JET
, .jet = input_asset
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
}
,[INPUT_AMOUNT] =
{ .tag = JET
, .jet = input_amount
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w64
}
,[INPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = input_script_hash
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[INPUT_SEQUENCE] =
{ .tag = JET
, .jet = input_sequence
, .sourceIx = ty_w32
, .targetIx = ty_mw32
}
,[INPUT_ISSUANCE_BLINDING] =
{ .tag = JET
, .jet = input_issuance_blinding
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[INPUT_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = input_issuance_contract
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[INPUT_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = input_issuance_entropy
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[INPUT_ISSUANCE_ASSET_AMT] =
{ .tag = JET
, .jet = input_issuance_asset_amt
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[INPUT_ISSUANCE_TOKEN_AMT] =
{ .tag = JET
, .jet = input_issuance_token_amt
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[OUTPUT_ASSET] =
{ .tag = JET
, .jet = output_asset
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
}
,[OUTPUT_AMOUNT] =
{ .tag = JET
, .jet = output_amount
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w64
}
,[OUTPUT_NONCE] =
{ .tag = JET
, .jet = output_nonce
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w256
}
,[OUTPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = output_script_hash
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[OUTPUT_NULL_DATUM] =
{ .tag = JET
, .jet = output_null_datum
, .sourceIx = ty_w64
, .targetIx = ty_mmspw2w256sbw4
}
,[SCRIPT_CMR] =
{ .tag = JET
, .jet = script_cmr
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_INDEX] =
{ .tag = JET
, .jet = current_index
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[CURRENT_IS_PEGIN] =
{ .tag = JET
, .jet = current_is_pegin
, .sourceIx = ty_u
, .targetIx = ty_b
}
,[CURRENT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = current_prev_outpoint
, .sourceIx = ty_u
, .targetIx = ty_pw256w32
}
,[CURRENT_ASSET] =
{ .tag = JET
, .jet = current_asset
, .sourceIx = ty_u
, .targetIx = ty_spbw256w256
}
,[CURRENT_AMOUNT] =
{ .tag = JET
, .jet = current_amount
, .sourceIx = ty_u
, .targetIx = ty_spbw256w64
}
,[CURRENT_SCRIPT_HASH] =
{ .tag = JET
, .jet = current_script_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_SEQUENCE] =
{ .tag = JET
, .jet = current_sequence
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[CURRENT_ISSUANCE_BLINDING] =
{ .tag = JET
, .jet = current_issuance_blinding
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = current_issuance_contract
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = current_issuance_entropy
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_ISSUANCE_ASSET_AMT] =
{ .tag = JET
, .jet = current_issuance_asset_amt
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
}
,[CURRENT_ISSUANCE_TOKEN_AMT] =
{ .tag = JET
, .jet = current_issuance_token_amt
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
}
,[INPUTS_HASH] =
{ .tag = JET
, .jet = inputs_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[OUTPUTS_HASH] =
{ .tag = JET
, .jet = outputs_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[NUM_INPUTS] =
{ .tag = JET
, .jet = num_inputs
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[NUM_OUTPUTS] =
{ .tag = JET
, .jet = num_outputs
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[FEE] =
{ .tag = JET
, .jet = fee
, .sourceIx = ty_w256
, .targetIx = ty_w64
}
