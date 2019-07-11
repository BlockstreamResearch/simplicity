#ifndef SHA256_H
#define SHA256_H

#include <stdint.h>
#include "bitstring.h"

/* A struct holding the 256-bit array of a SHA-256 hash or midstate.
 */
typedef struct sha256_midstate {
  uint32_t s[8];
} sha256_midstate;

/* Compute the SHA-256 hash, 'h', of the bitstring represented by 's'.
 *
 * Precondition: uint32_t h[8];
 *               '*s' is a valid bitstring;
 */
void sha256_bitstring(uint32_t* h, const bitstring* s);

#endif
