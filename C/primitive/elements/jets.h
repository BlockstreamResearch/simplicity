/* This module defines primitives and jets that are specific to the Elements application for Simplicity.
 */
#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H

#include "../../jets.h"

/* Primitives for the Elements application of Simplicity. */
bool version(frameItem* dst, frameItem src, const txEnv* env);
bool lock_time(frameItem* dst, frameItem src, const txEnv* env);
bool input_is_pegin(frameItem* dst, frameItem src, const txEnv* env);
bool input_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env);
bool input_asset(frameItem* dst, frameItem src, const txEnv* env);
bool input_amount(frameItem* dst, frameItem src, const txEnv* env);
bool input_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_sequence(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_blinding(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_contract(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_asset_amt(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_token_amt(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env);
bool input_issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env);
bool output_asset(frameItem* dst, frameItem src, const txEnv* env);
bool output_amount(frameItem* dst, frameItem src, const txEnv* env);
bool output_nonce(frameItem* dst, frameItem src, const txEnv* env);
bool output_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_null_datum(frameItem* dst, frameItem src, const txEnv* env);
bool output_surjection_proof(frameItem* dst, frameItem src, const txEnv* env);
bool output_range_proof(frameItem* dst, frameItem src, const txEnv* env);
bool script_cmr(frameItem* dst, frameItem src, const txEnv* env);
bool current_index(frameItem* dst, frameItem src, const txEnv* env);
bool current_is_pegin(frameItem* dst, frameItem src, const txEnv* env);
bool current_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env);
bool current_asset(frameItem* dst, frameItem src, const txEnv* env);
bool current_amount(frameItem* dst, frameItem src, const txEnv* env);
bool current_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool current_sequence(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_blinding(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_contract(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_asset_amt(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_token_amt(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env);
bool tapleaf_version(frameItem* dst, frameItem src, const txEnv* env);
bool tapbranch(frameItem* dst, frameItem src, const txEnv* env);
bool internal_key(frameItem* dst, frameItem src, const txEnv* env);
bool annex_hash(frameItem* dst, frameItem src, const txEnv* env);
bool inputs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool outputs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool num_inputs(frameItem* dst, frameItem src, const txEnv* env);
bool num_outputs(frameItem* dst, frameItem src, const txEnv* env);

/* :TODO: Not yet implemented. */
#define fee NULL

#endif
