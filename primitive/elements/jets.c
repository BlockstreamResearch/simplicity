#include "jets.h"

#include "ops.h"
#include "primitive.h"
#include "../../unreachable.h"

/* Write a 256-bit hash value to the 'dst' frame, advancing the cursor 256 cells.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 *               NULL != h;
 */
static void writeHash(frameItem* dst, const sha256_midstate* h) {
  write32s(dst, h->s, 8);
}

/* Write an outpoint value to the 'dst' frame, advancing the cursor 288 cells.
 *
 * Precondition: '*dst' is a valid write frame for 288 more cells;
 *               NULL != op;
 */
static void prevOutpoint(frameItem* dst, const outpoint* op) {
  writeHash(dst, &op->txid);
  write32(dst, op->ix);
}

/* Write an confidential asset to the 'dst' frame, advancing the cursor 258 cells, unless 'asset->prefix == NONE'.
 * Returns 'asset->prefix != NONE'.
 *
 * Precondition: '*dst' is a valid write frame for 258 more cells;
 *               NULL != asset;
 */
static bool asset(frameItem* dst, const confidential* asset) {
  if (NONE == asset->prefix) return false;

  if (writeBit(dst, EXPLICIT == asset->prefix)) {
    skipBits(dst, 1);
  } else {
    writeBit(dst, ODD_Y == asset->prefix);
  }
  writeHash(dst, &asset->data);
  return true;
}

/* Write an confidential amount to the 'dst' frame, advancing the cursor 258 cells.
 * Writes an explicit amount of 0 when 'amt->prefix' is NONE.
 *
 * Precondition: '*dst' is a valid write frame for 258 more cells;
 *               NULL != amt;
 */
static void amt(frameItem* dst, const confAmount* amt) {
  if (writeBit(dst, NONE == amt->prefix || EXPLICIT == amt->prefix)) {
    skipBits(dst, 1 + 256 - 64);
    write64(dst, EXPLICIT == amt->prefix ? amt->explicit : 0);
  } else {
    writeBit(dst, ODD_Y == amt->prefix);
    writeHash(dst, &amt->confidential);
  }
}

/* Write an optional confidential nonce to the 'dst' frame, advancing the cursor 259 cells.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != nonce;
 */
static void nonce(frameItem* dst, const confidential* nonce) {
  if (writeBit(dst, NONE != nonce->prefix)) {
    if (writeBit(dst, EXPLICIT == nonce->prefix)) {
      skipBits(dst, 1);
    } else {
      writeBit(dst, ODD_Y == nonce->prefix);
    }
    writeHash(dst, &nonce->data);
  } else {
    skipBits(dst, 1+1+256);
  }
}

/* Write an optional 'blindingNonce' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void reissuanceBlinding(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, REISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->blindingNonce);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional 'contractHash' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void newIssuanceContract(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NEW_ISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->contractHash);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional 'entropy' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void reissuanceEntropy(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, REISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->entropy);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional confidential asset amount from an 'assetIssuance' to the 'dst' frame, advancing the cursor 259 cells.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != issuance;
 */
static void issuanceAssetAmt(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NO_ISSUANCE != issuance->type)) {
    amt(dst, &issuance->assetAmt);
  } else {
    skipBits(dst, 258);
  }
}

/* Write an optional confidential token amount from an 'assetIssuance' to the 'dst' frame, advancing the cursor.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != issuance;
 */
static void issuanceTokenAmt(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NO_ISSUANCE != issuance->type)) {
    amt(dst, NEW_ISSUANCE == issuance->type ? &issuance->tokenAmt : &(confAmount){ .prefix = EXPLICIT, .explicit = 0});
  } else {
    skipBits(dst, 258);
  }
}

static uint_fast32_t lockHeight(const transaction* tx) {
  return !tx->isFinal && tx->lockTime < 500000000U ? tx->lockTime : 0;
}

static uint_fast32_t lockTime(const transaction* tx) {
  return !tx->isFinal && 500000000U <= tx->lockTime ? tx->lockTime : 0;
}

static uint_fast16_t lockDistance(const transaction* tx) {
  return 2 <= tx->version ? tx->lockDistance : 0;
}

static uint_fast16_t lockDuration(const transaction* tx) {
  return 2 <= tx->version ? (uint_fast32_t)tx->lockDuration : 0;
}

/* version : ONE |- TWO^32 */
bool version(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->version);
  return true;
}

/* lock_time : ONE |- TWO^32 */
bool lock_time(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->lockTime);
  return true;
}

/* input_is_pegin : TWO^32 |- S TWO */
bool input_is_pegin(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    writeBit(dst, env->tx->input[i].isPegin);
  } else {
    skipBits(dst, 1);
  }
  return true;
}

/* input_prev_outpoint : TWO^32 |- S (TWO^256 * TWO^32) */
bool input_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    prevOutpoint(dst, &env->tx->input[i].prevOutpoint);
  } else {
    skipBits(dst, 288);
  }
  return true;
}

/* input_asset : TWO^32 |- S (Conf TWO^256) */
bool input_asset(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    return asset(dst, &env->tx->input[i].txo.asset);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* input_amount : TWO^32 |- S (Conf TWO^64) */
bool input_amount(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    amt(dst, &env->tx->input[i].txo.amt);
  } else {
    skipBits(dst, 258);
  }
  return true;
}

/* input_script_hash : TWO^32 |- S TWO^256 */
bool input_script_hash(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    writeHash(dst, &env->tx->input[i].txo.scriptPubKey);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* input_sequence : TWO^32 |- S TWO^32 */
bool input_sequence(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    write32(dst, env->tx->input[i].sequence);
  } else {
    skipBits(dst, 32);
  }
  return true;
}

/* input_reissuance_blinding : TWO^32 |- S (S TWO^256) */
bool input_reissuance_blinding(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    reissuanceBlinding(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* input_new_issuance_contract : TWO^32 |- S (S TWO^256) */
bool input_new_issuance_contract(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    newIssuanceContract(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* input_reissuance_entropy : TWO^32 |- S (S TWO^256) */
bool input_reissuance_entropy(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    reissuanceEntropy(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* input_issuance_asset_amt : TWO^32 |- S (S (Conf TWO^64)) */
bool input_issuance_asset_amt(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceAssetAmt(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* input_issuance_token_amt : TWO^32 |- S (S (Conf TWO^64)) */
bool input_issuance_token_amt(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceTokenAmt(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* input_issuance_asset_proof : TWO^32 |- S TWO^256 */
bool input_issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    writeHash(dst, &env->tx->input[i].issuance.assetRangeProofHash);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* input_issuance_token_proof : TWO^32 |- S TWO^256 */
bool input_issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    writeHash(dst, &env->tx->input[i].issuance.tokenRangeProofHash);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* output_asset : TWO^32 |- S (Conf TWO^256) */
bool output_asset(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    return asset(dst, &env->tx->output[i].asset);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* output_amount : TWO^32 |- S (Conf TWO^64) */
bool output_amount(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    amt(dst, &env->tx->output[i].amt);
  } else {
    skipBits(dst, 258);
  }
  return true;
}

/* output_nonce : TWO^32 |- S (S (Conf TWO^256)) */
bool output_nonce(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    nonce(dst, &env->tx->output[i].nonce);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* output_script_hash : TWO^32 |- S TWO^256 */
bool output_script_hash(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    writeHash(dst, &env->tx->output[i].scriptPubKey);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* output_null_datum : TWO^32 * TWO^32 |- S (S (TWO^2 * TWO^256 + (TWO + TWO^4)))  */
bool output_null_datum(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs && env->tx->output[i].isNullData)) {
    uint_fast32_t j = read32(&src);
    if (writeBit(dst, j < env->tx->output[i].pnd.len)) {
      if (writeBit(dst, OP_PUSHDATA4 < env->tx->output[i].pnd.op[j].code)) {
        skipBits(dst, 2 + 256 - 5);
        if (writeBit(dst, OP_1 <= env->tx->output[i].pnd.op[j].code)) {
          switch (env->tx->output[i].pnd.op[j].code) {
            case OP_1 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_2 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_3 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_4 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_5 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_6 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_7 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_8 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_9 : writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_10: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_11: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_12: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_13: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_14: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_15: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_16: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            default: assert(false); UNREACHABLE;
          }
        } else {
          assert(OP_RESERVED == env->tx->output[i].pnd.op[j].code ||
                 OP_1NEGATE == env->tx->output[i].pnd.op[j].code);
          skipBits(dst, 3);
          writeBit(dst, OP_RESERVED == env->tx->output[i].pnd.op[j].code);
        }
      } else {
        switch (env->tx->output[i].pnd.op[j].code) {
          case OP_IMMEDIATE: writeBit(dst, 0); writeBit(dst, 0); break;
          case OP_PUSHDATA: writeBit(dst, 0); writeBit(dst, 1); break;
          case OP_PUSHDATA2: writeBit(dst, 1); writeBit(dst, 0); break;
          case OP_PUSHDATA4: writeBit(dst, 1); writeBit(dst, 1); break;
          default: assert(false); UNREACHABLE;
        }
        writeHash(dst, &env->tx->output[i].pnd.op[j].dataHash);
      }
    } else {
      skipBits(dst, 1 + 2 + 256);
    }
  } else {
    skipBits(dst, 1 + 1 + 2 + 256);
  }
  return true;
}

/* output_surjection_proof : TWO^32 |- S TWO^256 */
bool output_surjection_proof(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    writeHash(dst, &env->tx->output[i].surjectionProofHash);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* output_range_proof : TWO^32 |- S TWO^256 */
bool output_range_proof(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    writeHash(dst, &env->tx->output[i].rangeProofHash);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* script_cmr : ONE |- TWO^256 */
bool script_cmr(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32s(dst, env->scriptCMR, 8);
  return true;
}

/* current_index : ONE |- TWO^32 */
bool current_index(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->ix);
  return true;
}

/* current_is_pegin : ONE |- TWO */
bool current_is_pegin(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  writeBit(dst, env->tx->input[env->ix].isPegin);
  return true;
}

/* current_prev_outpoint : ONE |- TWO^256 * TWO^32 */
bool current_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  prevOutpoint(dst, &env->tx->input[env->ix].prevOutpoint);
  return true;
}

/* current_asset : ONE |- Conf TWO^256 */
bool current_asset(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  return asset(dst, &env->tx->input[env->ix].txo.asset);
}

/* current_amount : ONE |- Conf TWO^64 */
bool current_amount(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  amt(dst, &env->tx->input[env->ix].txo.amt);
  return true;
}

/* current_script_hash : ONE |- TWO^256 */
bool current_script_hash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  writeHash(dst, &env->tx->input[env->ix].txo.scriptPubKey);
  return true;
}

/* current_sequence : ONE |- TWO^32 */
bool current_sequence(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  write32(dst, env->tx->input[env->ix].sequence);
  return true;
}

/* current_reissuance_blinding : ONE |- S (Conf TWO^256) */
bool current_reissuance_blinding(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  reissuanceBlinding(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* current_new_issuance_contract : ONE |- S (Conf TWO^256) */
bool current_new_issuance_contract(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  newIssuanceContract(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* current_reissuance_entropy : ONE |- S (Conf TWO^256) */
bool current_reissuance_entropy(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  reissuanceEntropy(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* current_issuance_asset_amt : ONE |- S (Conf TWO^64) */
bool current_issuance_asset_amt(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceAssetAmt(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* current_issuance_token_amt : ONE |- S (Conf TWO^64) */
bool current_issuance_token_amt(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceTokenAmt(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* current_issuance_asset_proof : ONE |- TWO^256 */
bool current_issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  writeHash(dst, &env->tx->input[env->ix].issuance.assetRangeProofHash);
  return true;
}

/* current_issuance_token_proof : ONE |- TWO^256 */
bool current_issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  writeHash(dst, &env->tx->input[env->ix].issuance.tokenRangeProofHash);
  return true;
}

/* tapleaf_version : ONE |- TWO^8 */
bool tapleaf_version(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write8(dst, env->taproot->leafVersion);
  return true;
}

/* tapbranch : TWO^8 |- S (TWO^256) */
bool tapbranch(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast8_t i = read8(&src);
  if (writeBit(dst, i < env->taproot->branchLen)) {
    writeHash(dst, &env->taproot->branch[i]);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* internal_key : ONE |- TWO^256 */
bool internal_key(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  writeHash(dst, &env->taproot->internalKey);
  return true;
}

/* annex_hash : ONE |- S (TWO^256) */
bool annex_hash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (writeBit(dst, env->taproot->annexHash)) {
    writeHash(dst, env->taproot->annexHash);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* inputs_hash : ONE |- TWO^256 */
bool inputs_hash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  writeHash(dst, &env->tx->inputsHash);
  return true;
}

/* outputs_hash : ONE |- TWO^256 */
bool outputs_hash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  writeHash(dst, &env->tx->outputsHash);
  return true;
}

/* num_inputs : ONE |- TWO^32 */
bool num_inputs(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->numInputs);
  return true;
}

/* num_outputs : ONE |- TWO^32 */
bool num_outputs(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->numOutputs);
  return true;
}

/* tx_is_final : ONE |- TWO */
bool tx_is_final(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  writeBit(dst, env->tx->isFinal);
  return true;
}

/* tx_lock_height : ONE |- TWO^32 */
bool tx_lock_height(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, lockHeight(env->tx));
  return true;
}

/* tx_lock_time : ONE |- TWO^32 */
bool tx_lock_time(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, lockTime(env->tx));
  return true;
}

/* tx_lock_distance : ONE |- TWO^16 */
bool tx_lock_distance(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write16(dst, lockDistance(env->tx));
  return true;
}

/* tx_lock_duration : ONE |- TWO^16 */
bool tx_lock_duration(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write16(dst, lockDuration(env->tx));
  return true;
}

/* check_lock_height : TWO^32 |- ONE */
bool check_lock_height(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  uint_fast32_t x = read32(&src);
  return x <= lockHeight(env->tx);
}

/* check_lock_time : TWO^32 |- ONE */
bool check_lock_time(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  uint_fast32_t x = read32(&src);
  return x <= lockTime(env->tx);
}

/* check_lock_distance : TWO^16 |- ONE */
bool check_lock_distance(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  uint_fast16_t x = read16(&src);
  return x <= lockDistance(env->tx);
}

/* check_lock_duration : TWO^16 |- ONE */
bool check_lock_duration(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  uint_fast16_t x = read16(&src);
  return x <= lockDuration(env->tx);
}

/* calculate_issuance_entropy : TWO^256 * TWO^32 * TWO^256 |- TWO^256 */
bool calculate_issuance_entropy(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused.
  outpoint op;
  sha256_midstate contract;
  sha256_midstate result;

  read32s(op.txid.s, 8, &src);
  op.ix = read32(&src);
  read32s(contract.s, 8, &src);

  result = generateIssuanceEntropy(&op, &contract);
  writeHash(dst, &result);
  return true;
}

/* calculate_asset : TWO^256 |- TWO^256 */
bool calculate_asset(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused.
  sha256_midstate entropy;
  sha256_midstate result;

  read32s(entropy.s, 8, &src);
  result = calculateAsset(&entropy);

  writeHash(dst, &result);
  return true;
}

/* calculate_explicit_token : TWO^256 |- TWO^256 */
bool calculate_explicit_token(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused.
  sha256_midstate entropy;
  sha256_midstate result;

  read32s(entropy.s, 8, &src);
  result = calculateToken(&entropy, EXPLICIT);

  writeHash(dst, &result);
  return true;
}

/* calculate_confidential_token : TWO^256 |- TWO^256 */
bool calculate_confidential_token(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused.
  sha256_midstate entropy;
  sha256_midstate result;

  read32s(entropy.s, 8, &src);
  result = calculateToken(&entropy, EVEN_Y /* ODD_Y would also work. */);

  writeHash(dst, &result);
  return true;
}

/* input_issuance : TWO^256 |- S (S TWO) */
bool input_issuance(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    const sigInput* input = &env->tx->input[i];
    if (writeBit(dst, NO_ISSUANCE != input->issuance.type)) {
      writeBit(dst, REISSUANCE == input->issuance.type);
    } else {
      skipBits(dst, 1);
    }
  } else {
    skipBits(dst, 2);
  }
  return true;
}

/* input_issuance_entropy : TWO^256 |- S (S TWO^256) */
bool input_issuance_entropy(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    const sigInput* input = &env->tx->input[i];
    if (writeBit(dst, NO_ISSUANCE != input->issuance.type)) {
      writeHash(dst, &input->issuance.entropy);
    } else {
      skipBits(dst, 256);
    }
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* input_issuance_asset : TWO^256 |- S (S TWO^256) */
bool input_issuance_asset(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    const sigInput* input = &env->tx->input[i];
    if (writeBit(dst, NO_ISSUANCE != input->issuance.type)) {
      writeHash(dst, &input->issuance.assetId);
    } else {
      skipBits(dst, 256);
    }
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* input_issuance_token : TWO^256 |- S (S TWO^256) */
bool input_issuance_token(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    const sigInput* input = &env->tx->input[i];
    if (writeBit(dst, NO_ISSUANCE != input->issuance.type)) {
      writeHash(dst, &input->issuance.tokenId);
    } else {
      skipBits(dst, 256);
    }
  } else {
    skipBits(dst, 257);
  }
  return true;
}
