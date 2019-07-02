#ifndef PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H
#define PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *       (Simplicity.Elements.Programs.CheckSigHashAll.pkwCheckSigHashAll
 *         (PubKey True 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)
 *         (Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
 *              0xa72598dbf49f8174e103896c4c63e74d5b60971ad2ec11f4822861522cb1c7dc
 *       ) )
 */
extern const unsigned char elementsCheckSigHashAllTx1[];
extern const size_t sizeof_elementsCheckSigHashAllTx1;


/* The commitment Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_cmr[];

/* The witness Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_wmr[];

#endif
