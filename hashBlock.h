#ifndef HASHBLOCK_H
#define HASHBLOCK_H

#include <stddef.h>

/* A length-prefixed encoding of the SHA-256 compression function written in Simplicity.
 *
 * Invariant: unsigned char hashBlock[sizeof_hashBlock]
 */
extern const unsigned char hashBlock[];
extern const size_t sizeof_hashBlock;

#endif
