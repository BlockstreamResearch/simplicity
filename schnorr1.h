#ifndef SCHNORR1_H
#define SCHNORR1_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *       ((false &&& scribe (toWord256 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)) &&& zero word256) &&&
 *       witness (toWord512 0x787A848E71043D280C50470E8E1532B2DD5D20EE912A45DBDD2BD1DFBF187EF67031A98831859DC34DFFEEDDA86831842CCD0079E1F92AF177F7F22CC1DCED05) >>>
 *     schnorrAssert
 */
extern const unsigned char schnorr1[];
extern const size_t sizeof_schnorr1;

/* The commitment Merkle root of the above schnorr1 Simplicity expression. */
extern const uint32_t schnorr1_cmr[];

/* The witness Merkle root of the above schnorr1 Simplicity expression. */
extern const uint32_t schnorr1_wmr[];

#endif
