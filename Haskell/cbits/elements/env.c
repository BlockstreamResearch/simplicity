#include <stdlib.h>
#include "simplicity/elements/env.h"
#include "primitive/elements/primitive.h"

const size_t c_sizeof_rawBuffer = sizeof(rawBuffer);
const size_t c_sizeof_rawOutput = sizeof(rawOutput);
const size_t c_sizeof_rawInput = sizeof(rawInput);
const size_t c_sizeof_rawTransaction = sizeof(rawTransaction);
const size_t c_sizeof_rawTapEnv = sizeof(rawTapEnv);
const size_t c_sizeof_txEnv = sizeof(txEnv);

void c_set_rawBuffer(rawBuffer* result, const char* buf, unsigned int len) {
  *result = (rawBuffer){ .buf = buf, .len = len };
}

void c_set_rawOutput(rawOutput* result, const char* asset, const char* value, const char* nonce, const rawBuffer* scriptPubKey,
                                        const rawBuffer* surjectionProof, const rawBuffer* rangeProof) {
  *result = (rawOutput){ .asset = asset
                       , .value = value
                       , .nonce = nonce
                       , .scriptPubKey = *scriptPubKey
                       , .surjectionProof = *surjectionProof
                       , .rangeProof = *rangeProof };
}

void c_set_rawInput(rawInput* result, bool isPegin,
                                      const char* prevTxid, unsigned int prevIx,
                                      const char* asset, const char* value, const rawBuffer* scriptPubKey,
                                      unsigned int sequence,
                                      const char* blindingNonce, const char* assetEntropy, const char* amount, const char* inflationKeys,
                                      const rawBuffer* amountRangePrf, const rawBuffer* inflationKeysRangePrf) {
  *result = (rawInput){ .prevTxid = prevTxid
                      , .issuance = { .blindingNonce = blindingNonce
                                    , .assetEntropy = assetEntropy
                                    , .amount = amount
                                    , .inflationKeys = inflationKeys
                                    , .amountRangePrf = *amountRangePrf
                                    , .inflationKeysRangePrf = *inflationKeysRangePrf
                                    }
                      , .txo = {.asset = asset, .value = value, .scriptPubKey = *scriptPubKey}
                      , .prevIx = prevIx
                      , .sequence = sequence
                      , .isPegin = isPegin
                      };
}

void c_set_rawTransaction(rawTransaction* result, unsigned int version,
                                                  const rawInput* input, unsigned int numInputs,
                                                  const rawOutput* output, unsigned int numOutputs,
                                                  unsigned int lockTime) {
  *result = (rawTransaction){ .version = version
                            , .input = input, .numInputs = numInputs
                            , .output = output, .numOutputs = numOutputs
                            , .lockTime = lockTime,
                            };
}

void c_set_rawTapEnv(rawTapEnv* result, const rawBuffer* annex, const char* controlBlock, unsigned char branchLen) {
  *result = (rawTapEnv){ .annex = annex, .controlBlock = controlBlock, .branchLen = branchLen };
}

void c_set_txEnv(txEnv* result, const transaction* tx, const tapEnv* taproot, const unsigned int* scriptCMR, unsigned int ix) {
  *result = (txEnv){ .tx = tx, .taproot = taproot, .scriptCMR = scriptCMR, .ix = ix };
}

void c_free_tapEnv(tapEnv* env) {
  free(env);
}

void c_free_transaction(transaction* tx) {
  free(tx);
}
