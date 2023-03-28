#include "schnorr6.h"

/* A length-prefixed encoding of the following Simplicity program:
 *     (scribe (toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) &&&
 *      scribe (toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)) &&&
 *      witness (toWord512 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2) >>>
 *     Simplicity.Programs.LibSecp256k1.Lib.bip_0340_verify
 * with jets.
 */
const unsigned char schnorr6[] = {
  0xc6, 0xd5, 0xbf, 0xe3, 0xae, 0xfe, 0x54, 0xce, 0x38, 0xbe, 0x6c, 0x30, 0x6e, 0x4d, 0xb6, 0x46, 0x83, 0x7c, 0xb1, 0xfd,
  0x5c, 0x3b, 0x45, 0xbd, 0x9d, 0xb0, 0x86, 0x48, 0x1e, 0xf6, 0xa0, 0x57, 0x4c, 0xb2, 0xbc, 0x5a, 0xb1, 0xb1, 0x67, 0x79,
  0xbe, 0x35, 0x75, 0xbd, 0x8f, 0x05, 0x20, 0xa9, 0xf2, 0x1b, 0xb5, 0x30, 0x0b, 0x55, 0x6a, 0xd8, 0xee, 0x66, 0x60, 0x49,
  0x73, 0xa1, 0x4a, 0x11, 0x6e, 0xb8, 0xe2, 0x8d, 0x8c, 0x04, 0x7a, 0x40, 0x1f, 0xff, 0x2f, 0x7a, 0xae, 0xab, 0xdd, 0xd4,
  0x84, 0x08, 0xa7, 0x42, 0x86, 0xaa, 0x46, 0xba, 0x70, 0x5e, 0xc8, 0xe5, 0xf0, 0xad, 0x14, 0x31, 0x65, 0xe0, 0xaf, 0x42,
  0x8c, 0x05, 0x2e, 0xaa, 0xc7, 0x98, 0x4f, 0x28, 0x8c, 0x81, 0x58, 0xc0, 0xf9, 0xa2, 0x0f, 0x5c, 0x21, 0x24, 0x7b, 0x3d,
  0xef, 0x4e, 0x78, 0xc8, 0x7c, 0x2c, 0xd7, 0xcb, 0xd7, 0xd5, 0xf4, 0x69, 0x63, 0x58, 0xaa, 0x7c, 0x40
};

const size_t sizeof_schnorr6 = sizeof(schnorr6);

/* The commitment Merkle root of the above schnorr6 Simplicity expression. */
const uint32_t schnorr6_cmr[] = {
  0x77814ff8u, 0x11b80ad9u, 0xb6b7f172u, 0xaa11ad6au, 0x2b2b6335u, 0xcfe4de42u, 0xe991a545u, 0x97ca5c5du
};

/* The identity Merkle root of the above schnorr6 Simplicity expression. */
const uint32_t schnorr6_imr[] = {
  0x467137a4u, 0xb61bdb0cu, 0xf8ae388eu, 0x77628c6du, 0xe731639cu, 0xc588c526u, 0x139bfbdcu, 0xe072d7a2u
};

/* The annotated Merkle root of the above schnorr6 Simplicity expression. */
const uint32_t schnorr6_amr[] = {
  0xcd11f8adu, 0xd83967e4u, 0x4fbb1197u, 0x88e40e74u, 0xe88a842fu, 0x8211592eu, 0xac98e6c7u, 0xb5b3814cu
};