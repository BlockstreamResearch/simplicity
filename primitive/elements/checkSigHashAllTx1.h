#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *     Simplicity.Programs.CheckSig.Lib.checkSigVerify' Simplicity.Elements.Programs.SigHash.Lib.sigAllHash
 *     (Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)
 *     (Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
 *                                       0x1bc38bb0d7bd75ea36b31f11b2e96ff11125aaa6d3ddd6c31c70efc01c02d82b)
 * with jets.
 */
extern const unsigned char elementsCheckSigHashAllTx1[];
extern const size_t sizeof_elementsCheckSigHashAllTx1;

/* The commitment Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_cmr[];

/* The identity Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_imr[];

/* The annotated Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_amr[];

#endif