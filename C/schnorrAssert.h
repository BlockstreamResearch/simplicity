#ifndef SCHNORRASSERT_H
#define SCHNORRASSERT_H

#include <stddef.h>

/* A length-prefixed encoding of the schnorr signature verification function written in Simplicity.
 *
 * Invariant: unsigned char schnorrAssert[sizeof_schnorrAssert]
 */
extern const unsigned char schnorrAssert[];
extern const size_t sizeof_schnorrAssert;

#endif
