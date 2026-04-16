#include "simplicity_alloc.h"
#include "simplicity/bitcoin/env.h"
#include "bitcoin/txEnv.h"

const size_t c_sizeof_rawBitcoinBuffer = sizeof(rawBitcoinBuffer);
const size_t c_sizeof_rawBitcoinOutput = sizeof(rawBitcoinOutput);
const size_t c_sizeof_rawBitcoinInput = sizeof(rawBitcoinInput);
const size_t c_sizeof_rawBitcoinTransaction = sizeof(rawBitcoinTransaction);
const size_t c_sizeof_rawBitcoinTapEnv = sizeof(rawBitcoinTapEnv);
const size_t c_bitcoin_sizeof_txEnv = sizeof(txEnv);

void c_set_rawBitcoinBuffer(rawBitcoinBuffer* result, const char* buf, unsigned int len) {
  *result = (rawBitcoinBuffer){ .buf = buf, .len = len };
}

void c_set_rawBitcoinOutput(rawBitcoinOutput* result, unsigned long value, const rawBitcoinBuffer* scriptPubKey) {
  *result = (rawBitcoinOutput){ .value = value
                              , .scriptPubKey = *scriptPubKey
                              };
}

void c_set_rawBitcoinInput(rawBitcoinInput* result, const rawBitcoinBuffer* annex, const rawBitcoinBuffer* scriptSig,
                                   const char* prevTxid, unsigned int prevIx,
                                   unsigned long value, const rawBitcoinBuffer* scriptPubKey,
                                   unsigned int sequence) {
  *result = (rawBitcoinInput){ .annex = annex
                             , .scriptSig = *scriptSig
                             , .prevTxid = prevTxid
                             , .txo = {.value = value, .scriptPubKey = *scriptPubKey}
                             , .prevIx = prevIx
                             , .sequence = sequence
                             };
}

void c_set_rawBitcoinTransaction(rawBitcoinTransaction* result, const unsigned char* txid, unsigned int version,
                                         const rawBitcoinInput* input, unsigned int numInputs,
                                         const rawBitcoinOutput* output, unsigned int numOutputs,
                                         unsigned int lockTime) {
  *result = (rawBitcoinTransaction){ .txid = txid
                                   , .version = version
                                   , .input = input, .numInputs = numInputs
                                   , .output = output, .numOutputs = numOutputs
                                   , .lockTime = lockTime,
                                   };
}

void c_set_rawBitcoinTapEnv(rawBitcoinTapEnv* result, const char* controlBlock, unsigned char pathLen, const char* scriptCMR) {
  *result = (rawBitcoinTapEnv){ .controlBlock = controlBlock, .pathLen = pathLen, .scriptCMR = scriptCMR };
}

void c_bitcoin_set_txEnv(txEnv* result, const bitcoinTransaction* tx, const bitcoinTapEnv* taproot, unsigned int ix) {
  *result = simplicity_bitcoin_build_txEnv(tx, taproot, ix);
}
