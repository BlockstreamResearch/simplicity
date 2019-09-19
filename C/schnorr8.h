#ifndef SCHNORR8_H
#define SCHNORR8_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *       ((false &&& scribe (toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)) &&& zero word256) &&&
 *       witness (toWord512 0x2A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1DFA16AEE06609280A19B67A24E1977E4697712B5FD2943914ECD5F730901B4AB7) >>>
 *     schnorrAssert
 */
extern const unsigned char schnorr8[];
extern const size_t sizeof_schnorr8;

/* The commitment Merkle root of the above schnorr8 Simplicity expression. */
extern const uint32_t schnorr8_cmr[];

/* The witness Merkle root of the above schnorr8 Simplicity expression. */
extern const uint32_t schnorr8_wmr[];

#endif
