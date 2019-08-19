#ifndef SIMPLICITY_ELEMENTS_H
#define SIMPLICITY_ELEMENTS_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

/* This section builds the 'rawTransaction' structure which is the transaction data needed to build an Elements 'txEnv' environment
 * for evaluating Simplicity expressions within.
 * The 'rawTransaction' is copied into an opaque 'transaction' structure that can be reused within evaluating Simplicity on multiple
 * inputs within the same transaction.
 */

/* A type for a Bitcoin script with its length.
 *
 * Invariant: unsigned char code[len]
 */
typedef struct rawScript {
  const unsigned char* code;
  uint32_t len;
} rawScript;

/* A structure representing data for one output from an Elements transaction.
 *
 * Invariant: unsigned char asset[asset[0] == 0 ? 1 : 33];
 *            unsigned char value[value[0] == 0 ? 1 :
 *                                value[0] == 1 ? 9 : 33];
 *            unsigned char nonce[nonce[0] == 0 ? 1 : 33];
 */
typedef struct rawOutput {
  const unsigned char* asset;
  const unsigned char* value;
  const unsigned char* nonce;
  rawScript scriptPubKey;
} rawOutput;

/* A structure representing data for one input from an Elements transaction, plus the TXO data of the output being redeemed.
 *
 * Invariant: uint8_t prevTxid[32];
 *            uint8_t issuance.blindingNonce[32];
 *            uint8_t issuance.assetEntropy[32];
 *            unsigned char issuance.amount[issuance.amount[0] == 0 ? 1 :
 *                                          issuance.amount[0] == 1 ? 9 : 33];
 *            unsigned char issuance.inflationKeys[issuance.inflationKeys[0] == 0 ? 1 :
 *                                                 issuance.inflaitonKeys[0] == 1 ? 9 : 33];
 *            unsigned char txo.asset[txo.asset[0] == 0 ? 1 : 33];
 *            unsigned char txo.value[txo.value[0] == 0 ? 1 :
 *                                    txo.value[0] == 1 ? 9 : 33];
 */
typedef struct rawInput {
  const uint8_t* prevTxid;
  struct {
    const uint8_t* blindingNonce;
    const uint8_t* assetEntropy;
    const unsigned char* amount;
    const unsigned char* inflationKeys;
  } issuance;
  struct {
    const unsigned char* asset;
    const unsigned char* value;
    rawScript scriptPubKey;
  } txo;
  uint32_t prevIx;
  uint32_t sequence;
  bool isPegin;
} rawInput;

/* A structure representing data for an Elements transaction, including the TXO data of each output being redeemed.
 *
 * Invariant: rawInput input[numInputs];
 *            rawOutput output[numOutputs];
 */
typedef struct rawTransaction {
  const rawInput* input;
  const rawOutput* output;
  uint32_t numInputs;
  uint32_t numOutputs;
  uint32_t version;
  uint32_t lockTime;
} rawTransaction;

/* A forward declaration for the structure containing a copy (and digest) of the rawTransaction data */
typedef struct transaction transaction;

/* Allocate and initialize a 'transaction' from a 'rawOuput', copying or hashing the data as needed.
 * Returns NULL if malloc fails (or if malloc cannot be called because we require an allocation larger than SIZE_MAX).
 *
 * Precondition: NULL != rawTx
 */
extern transaction* elements_simplicity_mallocTransaction(const rawTransaction* rawTx);

/* Deserialize a Simplicity program from 'file' and execute it in the environment of the 'ix'th input of 'tx'.
 * If the file isn't a proper encoding of a Simplicity program, '*success' is set to false.
 * If EOF isn't encountered at the end of decoding, '*success' is set to false.
 * If 'cmr != NULL' and the commitment Merkle root of the decoded expression doesn't match 'cmr' then '*success' is set to false.
 * If 'wmr != NULL' and the witness Merkle root of the decoded expression doesn't match 'wmr' then '*success' is set to false.
 * Otherwise evaluation proceeds and '*success' is set to the result of evaluation.
 *
 * If at any time there is a transient error, such as malloc failing or an I/O error reading from 'file'
 * then 'false' is returned, and 'success' and 'file' may be modified.
 * Otherwise, 'true' is returned.
 *
 * Precondition: NULL != success;
 *               NULL != tx;
 *               NULL != cmr implies uint32_t cmr[8]
 *               NULL != wmr implies uint32_t wmr[8]
 *               NULL != file;
 */
extern bool elements_simplicity_execSimplicity(bool* success, const transaction* tx, uint_fast32_t ix,
                                               const uint32_t* cmr, const uint32_t* wmr, FILE* file);
#endif
