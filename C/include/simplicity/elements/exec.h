#ifndef SIMPLICITY_ELEMENTS_EXEC_H
#define SIMPLICITY_ELEMENTS_EXEC_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "env.h"

/* Deserialize a Simplicity program from 'file' and execute it in the environment of the 'ix'th input of 'tx'.
 * If the file isn't a proper encoding of a Simplicity program, '*success' is set to false.
 * If EOF isn't encountered at the end of decoding, '*success' is set to false.
 * If 'amr != NULL' and the annotated Merkle root of the decoded expression doesn't match 'amr' then '*success' is set to false.
 * Otherwise evaluation proceeds and '*success' is set to the result of evaluation.
 * If 'imr != NULL' and '*success' is set to true, then the identity Merkle root of the decoded expression is written to 'imr'.
 * Otherwise if 'imr != NULL' then 'imr' may or may not be written to.
 *
 * If at any time there is a transient error, such as malloc failing or an I/O error reading from 'file'
 * then 'false' is returned, and 'success' and 'file' may be modified.
 * Otherwise, 'true' is returned.
 *
 * Precondition: NULL != success;
 *               NULL != imr implies unsigned char imr[32]
 *               NULL != tx;
 *               unsigned char genesisBlockHash[32]
 *               NULL != amr implies unsigned char amr[32]
 *               NULL != file;
 */
extern bool elements_simplicity_execSimplicity( bool* success, unsigned char* imr
                                              , const transaction* tx, uint_fast32_t ix, const tapEnv* taproot
                                              , const unsigned char* genesisBlockHash
                                              , const unsigned char* amr, FILE* file);
#endif
