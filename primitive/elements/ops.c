#include "ops.h"

/* Compute an Element's entropy value from a prevoutpoint and a contract hash.
 * A reimplementation of GenerateAssetEntropy from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != op;
 *               NULL != contract;
 */
sha256_midstate generateIssuanceEntropy(const outpoint* op, const sha256_midstate* contract) {
  uint32_t block[16];
  unsigned char buf[32];
  sha256_midstate result;

  /* First hash the outpoint data. */
  {
    sha256_context ctx = sha256_init(result.s);
    sha256_fromMidstate(buf, op->txid.s);
    sha256_uchars(&ctx, buf, 32);
    sha256_u32le(&ctx, op->ix);
    sha256_finalize(&ctx);
  }
  /* Fill in the first half of the block with the double hashed outpoint data. */
  {
    sha256_context ctx = sha256_init(&block[0]);
    sha256_fromMidstate(buf, result.s);
    sha256_uchars(&ctx, buf, 32);
    sha256_finalize(&ctx);
  }

  memcpy(&block[8], contract->s, sizeof(contract->s));
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}

/* Compute an Element's issuance Asset ID value from an entropy value.
 * A reimplementation of CalculateAsset from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != entropy;
 */
sha256_midstate calculateAsset(const sha256_midstate* entropy) {
  uint32_t block[16] = {0};
  sha256_midstate result;

  memcpy(&block[0], entropy->s, sizeof(entropy->s));
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}

/* Compute an Element's issuance Token ID value from an entropy value and an amount prefix.
 * A reimplementation of CalculateReissuanceToken from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != entropy;
 */
sha256_midstate calculateToken(const sha256_midstate* entropy, confPrefix prefix) {
  uint32_t block[16] = {0};
  sha256_midstate result;

  memcpy(&block[0], entropy->s, sizeof(entropy->s));
  block[8] = is_confidential(prefix) ? 0x02000000 : 0x01000000;
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}
