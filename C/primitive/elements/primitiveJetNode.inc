/* This file has been automatically generated. */
[ADD_32] =
{ .tag = JET
, .jet = add_32
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
}
,[BIP_0340_VERIFY] =
{ .tag = JET
, .jet = bip_0340_verify
, .sourceIx = ty_w1024
, .targetIx = ty_u
}
,[CALCULATE_ASSET] =
{ .tag = JET
, .jet = calculate_asset
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[CALCULATE_CONFIDENTIAL_TOKEN] =
{ .tag = JET
, .jet = calculate_confidential_token
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[CALCULATE_EXPLICIT_TOKEN] =
{ .tag = JET
, .jet = calculate_explicit_token
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[CALCULATE_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = calculate_issuance_entropy
, .sourceIx = ty_ppw256w32w256
, .targetIx = ty_w256
}
,[CHECK_LOCK_DISTANCE] =
{ .tag = JET
, .jet = check_lock_distance
, .sourceIx = ty_w16
, .targetIx = ty_u
}
,[CHECK_LOCK_DURATION] =
{ .tag = JET
, .jet = check_lock_duration
, .sourceIx = ty_w16
, .targetIx = ty_u
}
,[CHECK_LOCK_HEIGHT] =
{ .tag = JET
, .jet = check_lock_height
, .sourceIx = ty_w32
, .targetIx = ty_u
}
,[CHECK_LOCK_TIME] =
{ .tag = JET
, .jet = check_lock_time
, .sourceIx = ty_w32
, .targetIx = ty_u
}
,[CURRENT_ANNEX_HASH] =
{ .tag = JET
, .jet = current_annex_hash
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_ASSET] =
{ .tag = JET
, .jet = current_asset
, .sourceIx = ty_u
, .targetIx = ty_spbw256w256
}
,[CURRENT_ASSET_AMOUNT] =
{ .tag = JET
, .jet = current_asset_amount
, .sourceIx = ty_u
, .targetIx = ty_pspbw256w256spbw256w64
}
,[CURRENT_INDEX] =
{ .tag = JET
, .jet = current_index
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[CURRENT_ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_asset_amount
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
}
,[CURRENT_ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = current_issuance_asset_proof
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_token_amount
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
}
,[CURRENT_ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = current_issuance_token_proof
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = current_new_issuance_contract
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_PEGIN] =
{ .tag = JET
, .jet = current_pegin
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = current_prev_outpoint
, .sourceIx = ty_u
, .targetIx = ty_pw256w32
}
,[CURRENT_REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = current_reissuance_blinding
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = current_reissuance_entropy
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_SCRIPT_HASH] =
{ .tag = JET
, .jet = current_script_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = current_script_sig_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[CURRENT_SEQUENCE] =
{ .tag = JET
, .jet = current_sequence
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[DECOMPRESS] =
{ .tag = JET
, .jet = decompress
, .sourceIx = ty_pbw256
, .targetIx = ty_mw512
}
,[EQ_32] =
{ .tag = JET
, .jet = eq_32
, .sourceIx = ty_w64
, .targetIx = ty_b
}
,[FE_ADD] =
{ .tag = JET
, .jet = fe_add
, .sourceIx = ty_w512
, .targetIx = ty_w256
}
,[FE_INVERT] =
{ .tag = JET
, .jet = fe_invert
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[FE_IS_ODD] =
{ .tag = JET
, .jet = fe_is_odd
, .sourceIx = ty_w256
, .targetIx = ty_b
}
,[FE_IS_ZERO] =
{ .tag = JET
, .jet = fe_is_zero
, .sourceIx = ty_w256
, .targetIx = ty_b
}
,[FE_MULTIPLY] =
{ .tag = JET
, .jet = fe_multiply
, .sourceIx = ty_w512
, .targetIx = ty_w256
}
,[FE_MULTIPLY_BETA] =
{ .tag = JET
, .jet = fe_multiply_beta
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[FE_NEGATE] =
{ .tag = JET
, .jet = fe_negate
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[FE_NORMALIZE] =
{ .tag = JET
, .jet = fe_normalize
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[FE_SQUARE] =
{ .tag = JET
, .jet = fe_square
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[FE_SQUARE_ROOT] =
{ .tag = JET
, .jet = fe_square_root
, .sourceIx = ty_w256
, .targetIx = ty_mw256
}
,[FULL_ADD_32] =
{ .tag = JET
, .jet = full_add_32
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
}
,[FULL_MULTIPLY_32] =
{ .tag = JET
, .jet = full_multiply_32
, .sourceIx = ty_w128
, .targetIx = ty_w64
}
,[FULL_SUBTRACT_32] =
{ .tag = JET
, .jet = full_subtract_32
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
}
,[GE_IS_ON_CURVE] =
{ .tag = JET
, .jet = ge_is_on_curve
, .sourceIx = ty_w512
, .targetIx = ty_b
}
,[GE_NEGATE] =
{ .tag = JET
, .jet = ge_negate
, .sourceIx = ty_w512
, .targetIx = ty_w512
}
,[GEJ_ADD] =
{ .tag = JET
, .jet = gej_add
, .sourceIx = ty_ppw512w256pw512w256
, .targetIx = ty_pw512w256
}
,[GEJ_DOUBLE] =
{ .tag = JET
, .jet = gej_double
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
}
,[GEJ_GE_ADD] =
{ .tag = JET
, .jet = gej_ge_add
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw512w256
}
,[GEJ_GE_ADD_EX] =
{ .tag = JET
, .jet = gej_ge_add_ex
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw256pw512w256
}
,[GEJ_INFINITY] =
{ .tag = JET
, .jet = gej_infinity
, .sourceIx = ty_u
, .targetIx = ty_pw512w256
}
,[GEJ_IS_INFINITY] =
{ .tag = JET
, .jet = gej_is_infinity
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
}
,[GEJ_IS_ON_CURVE] =
{ .tag = JET
, .jet = gej_is_on_curve
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
}
,[GEJ_NEGATE] =
{ .tag = JET
, .jet = gej_negate
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
}
,[GEJ_NORMALIZE] =
{ .tag = JET
, .jet = gej_normalize
, .sourceIx = ty_pw512w256
, .targetIx = ty_mw512
}
,[GEJ_RESCALE] =
{ .tag = JET
, .jet = gej_rescale
, .sourceIx = ty_ppw512w256w256
, .targetIx = ty_pw512w256
}
,[GEJ_X_EQUIV] =
{ .tag = JET
, .jet = gej_x_equiv
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_b
}
,[GEJ_Y_IS_ODD] =
{ .tag = JET
, .jet = gej_y_is_odd
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
}
,[GENERATE] =
{ .tag = JET
, .jet = generate
, .sourceIx = ty_w256
, .targetIx = ty_pw512w256
}
,[GENESIS_BLOCK_HASH] =
{ .tag = JET
, .jet = genesis_block_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[INPUT_ANNEX_HASH] =
{ .tag = JET
, .jet = input_annex_hash
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[INPUT_ASSET] =
{ .tag = JET
, .jet = input_asset
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
}
,[INPUT_ASSET_AMOUNT] =
{ .tag = JET
, .jet = input_asset_amount
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
}
,[INPUT_PEGIN] =
{ .tag = JET
, .jet = input_pegin
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[INPUT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = input_prev_outpoint
, .sourceIx = ty_w32
, .targetIx = ty_mpw256w32
}
,[INPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = input_script_hash
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[INPUT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = input_script_sig_hash
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[INPUT_SEQUENCE] =
{ .tag = JET
, .jet = input_sequence
, .sourceIx = ty_w32
, .targetIx = ty_mw32
}
,[INTERNAL_KEY] =
{ .tag = JET
, .jet = internal_key
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[ISSUANCE] =
{ .tag = JET
, .jet = issuance
, .sourceIx = ty_w32
, .targetIx = ty_mmb
}
,[ISSUANCE_ASSET] =
{ .tag = JET
, .jet = issuance_asset
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = issuance_asset_amount
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = issuance_asset_proof
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = issuance_entropy
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[ISSUANCE_TOKEN] =
{ .tag = JET
, .jet = issuance_token
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = issuance_token_amount
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = issuance_token_proof
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[LINEAR_COMBINATION_1] =
{ .tag = JET
, .jet = linear_combination_1
, .sourceIx = ty_ppw256pw512w256w256
, .targetIx = ty_pw512w256
}
,[LINEAR_VERIFY_1] =
{ .tag = JET
, .jet = linear_verify_1
, .sourceIx = ty_pppw256w512w256w512
, .targetIx = ty_u
}
,[LOCK_TIME] =
{ .tag = JET
, .jet = lock_time
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[LOW_32] =
{ .tag = JET
, .jet = low_32
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[MULTIPLY_32] =
{ .tag = JET
, .jet = multiply_32
, .sourceIx = ty_w64
, .targetIx = ty_w64
}
,[NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = new_issuance_contract
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
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
,[ONE_32] =
{ .tag = JET
, .jet = one_32
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[OUTPUT_ASSET] =
{ .tag = JET
, .jet = output_asset
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
}
,[OUTPUT_ASSET_AMOUNT] =
{ .tag = JET
, .jet = output_asset_amount
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
}
,[OUTPUT_NONCE] =
{ .tag = JET
, .jet = output_nonce
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w256
}
,[OUTPUT_NULL_DATUM] =
{ .tag = JET
, .jet = output_null_datum
, .sourceIx = ty_w64
, .targetIx = ty_mmspw2w256sbw4
}
,[OUTPUT_RANGE_PROOF] =
{ .tag = JET
, .jet = output_range_proof
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[OUTPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = output_script_hash
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[OUTPUT_SURJECTION_PROOF] =
{ .tag = JET
, .jet = output_surjection_proof
, .sourceIx = ty_w32
, .targetIx = ty_mw256
}
,[PARSE_LOCK] =
{ .tag = JET
, .jet = parse_lock
, .sourceIx = ty_w32
, .targetIx = ty_sw32w32
}
,[PARSE_SEQUENCE] =
{ .tag = JET
, .jet = parse_sequence
, .sourceIx = ty_w32
, .targetIx = ty_msw16w16
}
,[POINT_VERIFY_1] =
{ .tag = JET
, .jet = point_verify_1
, .sourceIx = ty_pppw256pbw256w256pbw256
, .targetIx = ty_u
}
,[REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = reissuance_blinding
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = reissuance_entropy
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
}
,[SCALAR_ADD] =
{ .tag = JET
, .jet = scalar_add
, .sourceIx = ty_w512
, .targetIx = ty_w256
}
,[SCALAR_INVERT] =
{ .tag = JET
, .jet = scalar_invert
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[SCALAR_IS_ZERO] =
{ .tag = JET
, .jet = scalar_is_zero
, .sourceIx = ty_w256
, .targetIx = ty_b
}
,[SCALAR_MULTIPLY] =
{ .tag = JET
, .jet = scalar_multiply
, .sourceIx = ty_w512
, .targetIx = ty_w256
}
,[SCALAR_MULTIPLY_LAMBDA] =
{ .tag = JET
, .jet = scalar_multiply_lambda
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[SCALAR_NEGATE] =
{ .tag = JET
, .jet = scalar_negate
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[SCALAR_NORMALIZE] =
{ .tag = JET
, .jet = scalar_normalize
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[SCALAR_SQUARE] =
{ .tag = JET
, .jet = scalar_square
, .sourceIx = ty_w256
, .targetIx = ty_w256
}
,[SCALE] =
{ .tag = JET
, .jet = scale
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_pw512w256
}
,[SCRIPT_CMR] =
{ .tag = JET
, .jet = script_cmr
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[SHA_256_BLOCK] =
{ .tag = JET
, .jet = sha_256_block
, .sourceIx = ty_pw256w512
, .targetIx = ty_w256
}
,[SHA_256_CTX_8_ADD_1] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_1
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_128] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_128
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w1024
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_16] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_16
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w128
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_2] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_2
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_256] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_256
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w2048
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_32] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_32
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_4] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_4
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_512] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_512
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w4096
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_64] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_64
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_8] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_8
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_ADD_BUFFER_511] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_buffer_511
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw2048pmw1024pmw512pmw256pmw128pmw64pmw32pmw16mw8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_CTX_8_FINALIZE] =
{ .tag = JET
, .jet = sha_256_ctx_8_finalize
, .sourceIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .targetIx = ty_w256
}
,[SHA_256_CTX_8_INIT] =
{ .tag = JET
, .jet = sha_256_ctx_8_init
, .sourceIx = ty_u
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
}
,[SHA_256_IV] =
{ .tag = JET
, .jet = sha_256_iv
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[SUBTRACT_32] =
{ .tag = JET
, .jet = subtract_32
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
}
,[TAPBRANCH] =
{ .tag = JET
, .jet = tapbranch
, .sourceIx = ty_w8
, .targetIx = ty_mw256
}
,[TAPLEAF_VERSION] =
{ .tag = JET
, .jet = tapleaf_version
, .sourceIx = ty_u
, .targetIx = ty_w8
}
,[TX_IS_FINAL] =
{ .tag = JET
, .jet = tx_is_final
, .sourceIx = ty_u
, .targetIx = ty_b
}
,[TX_LOCK_DISTANCE] =
{ .tag = JET
, .jet = tx_lock_distance
, .sourceIx = ty_u
, .targetIx = ty_w16
}
,[TX_LOCK_DURATION] =
{ .tag = JET
, .jet = tx_lock_duration
, .sourceIx = ty_u
, .targetIx = ty_w16
}
,[TX_LOCK_HEIGHT] =
{ .tag = JET
, .jet = tx_lock_height
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[TX_LOCK_TIME] =
{ .tag = JET
, .jet = tx_lock_time
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[VERSION] =
{ .tag = JET
, .jet = version
, .sourceIx = ty_u
, .targetIx = ty_w32
}
,[ANNEX_HASH] =
{ .tag = JET
, .jet = annex_hash
, .sourceIx = ty_u
, .targetIx = ty_mw256
}
,[CURRENT_AMOUNT] =
{ .tag = JET
, .jet = current_amount
, .sourceIx = ty_u
, .targetIx = ty_spbw256w64
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
,[FEE] =
{ .tag = JET
, .jet = fee
, .sourceIx = ty_w256
, .targetIx = ty_w64
}
,[INPUT_AMOUNT] =
{ .tag = JET
, .jet = input_amount
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w64
}
,[INPUTS_HASH] =
{ .tag = JET
, .jet = inputs_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
,[ISSUANCE_ASSET_AMT] =
{ .tag = JET
, .jet = issuance_asset_amt
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[ISSUANCE_TOKEN_AMT] =
{ .tag = JET
, .jet = issuance_token_amt
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
}
,[OUTPUT_AMOUNT] =
{ .tag = JET
, .jet = output_amount
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w64
}
,[OUTPUTS_HASH] =
{ .tag = JET
, .jet = outputs_hash
, .sourceIx = ty_u
, .targetIx = ty_w256
}
