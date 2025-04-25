#include "simplicity_alloc.h"
#include "simplicity/elements/env.h"
#include "elements/txEnv.h"

const size_t c_sizeof_rawElementsBuffer = sizeof(rawElementsBuffer);
const size_t c_sizeof_rawElementsOutput = sizeof(rawElementsOutput);
const size_t c_sizeof_rawElementsInput = sizeof(rawElementsInput);
const size_t c_sizeof_rawElementsTransaction = sizeof(rawElementsTransaction);
const size_t c_sizeof_rawElementsTapEnv = sizeof(rawElementsTapEnv);
const size_t c_sizeof_txEnv = sizeof(txEnv);

void c_set_rawElementsBuffer(rawElementsBuffer* result, const char* buf, unsigned int len) {
  *result = (rawElementsBuffer){ .buf = buf, .len = len };
}

void c_set_rawElementsOutput(rawElementsOutput* result, const char* asset, const char* value, const char* nonce, const rawElementsBuffer* scriptPubKey,
                                        const rawElementsBuffer* surjectionProof, const rawElementsBuffer* rangeProof) {
  *result = (rawElementsOutput){ .asset = asset
                       , .value = value
                       , .nonce = nonce
                       , .scriptPubKey = *scriptPubKey
                       , .surjectionProof = *surjectionProof
                       , .rangeProof = *rangeProof };
}

void c_set_rawElementsInput(rawElementsInput* result, const rawElementsBuffer* annex, const char* pegin, const rawElementsBuffer* scriptSig,
                                      const char* prevTxid, unsigned int prevIx,
                                      const char* asset, const char* value, const rawElementsBuffer* scriptPubKey,
                                      unsigned int sequence,
                                      const char* blindingNonce, const char* assetEntropy, const char* amount, const char* inflationKeys,
                                      const rawElementsBuffer* amountRangePrf, const rawElementsBuffer* inflationKeysRangePrf) {
  *result = (rawElementsInput){ .annex = annex
                      , .scriptSig = *scriptSig
                      , .prevTxid = prevTxid
                      , .pegin = pegin
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
                      };
}

void c_set_rawElementsTransaction(rawElementsTransaction* result, const unsigned char* txid, unsigned int version,
                                                  const rawElementsInput* input, unsigned int numInputs,
                                                  const rawElementsOutput* output, unsigned int numOutputs,
                                                  unsigned int lockTime) {
  *result = (rawElementsTransaction){ .txid = txid
                            , .version = version
                            , .input = input, .numInputs = numInputs
                            , .output = output, .numOutputs = numOutputs
                            , .lockTime = lockTime,
                            };
}

void c_set_rawElementsTapEnv(rawElementsTapEnv* result, const char* controlBlock, unsigned char pathLen, const char* scriptCMR) {
  *result = (rawElementsTapEnv){ .controlBlock = controlBlock, .pathLen = pathLen, .scriptCMR = scriptCMR };
}

void c_set_txEnv(txEnv* result, const elementsTransaction* tx, const elementsTapEnv* taproot, const char* genesisHash, unsigned int ix) {
  sha256_midstate genesis;
  sha256_toMidstate(genesis.s, genesisHash);
  *result = simplicity_elements_build_txEnv(tx, taproot, &genesis, ix);
}
