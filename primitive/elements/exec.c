#include <simplicity/elements/exec.h>

#include <stdlib.h>
#include <stdalign.h>
#include <string.h>
#include "primitive.h"
#include "../../deserialize.h"
#include "../../eval.h"
#include "../../typeInference.h"

/* Deserialize a Simplicity program from 'file' and execute it in the environment of the 'ix'th input of 'tx'.
 * If the file isn't a proper encoding of a Simplicity program, '*success' is set to false.
 * If EOF isn't encountered at the end of decoding, '*success' is set to false.
 * If 'cmr != NULL' and the commitment Merkle root of the decoded expression doesn't match 'cmr' then '*success' is set to false.
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
 *               NULL != taproot;
 *               unsigned char genesisBlockHash[32]
 *               NULL != cmr implies unsigned char cmr[32]
 *               NULL != amr implies unsigned char amr[32]
 *               NULL != file;
 */
extern bool elements_simplicity_execSimplicity( bool* success, unsigned char* imr
                                              , const transaction* tx, uint_fast32_t ix, const tapEnv* taproot
                                              , const unsigned char* genesisBlockHash
                                              , const unsigned char* cmr, const unsigned char* amr, FILE* file) {
  if (!success || !tx || !taproot || !file) return false;

  bool result;
  combinator_counters census;
  dag_node* dag;
  void* witnessAlloc = NULL;
  bitstring witness;
  int32_t len;
  sha256_midstate cmr_hash, amr_hash, genesis_hash;

  if (cmr) sha256_toMidstate(cmr_hash.s, cmr);
  if (amr) sha256_toMidstate(amr_hash.s, amr);
  sha256_toMidstate(genesis_hash.s, genesisBlockHash);

  {
    bitstream stream = initializeBitstream(file);
    len = decodeMallocDag(&dag, &census, &stream);
    if (len < 0) {
      *success = false;
      return PERMANENT_FAILURE(len);
    }

    int32_t err = decodeMallocWitnessData(&witnessAlloc, &witness, &stream);
    if (err < 0) {
      *success = false;
      result = PERMANENT_FAILURE(err);
    } else if (EOF != getc(file)) { /* Check that we hit the end of 'file' */
      *success = false;
      result = !ferror(file);
    } else {
      *success = result = !ferror(file);
    }
  }

  if (*success) {
    *success = !cmr || 0 == memcmp(cmr_hash.s, dag[len-1].cmr.s, sizeof(uint32_t[8]));
    if (*success) {
      type* type_dag;
      result = mallocTypeInference(&type_dag, dag, (size_t)len, &census);
      *success = result && type_dag && 0 == dag[len-1].sourceType && 0 == dag[len-1].targetType
              && fillWitnessData(dag, type_dag, (size_t)len, witness);
      if (*success) {
        sha256_midstate* imr_buf = (size_t)len <= SIZE_MAX / sizeof(sha256_midstate)
                                 ? malloc((size_t)len * sizeof(sha256_midstate))
                                 : NULL;
        bool noDupsCheck;
        result = imr_buf && verifyNoDuplicateIdentityRoots(&noDupsCheck, imr_buf, dag, type_dag, (size_t)len);
        *success = result && noDupsCheck;
        if (*success && imr) sha256_fromMidstate(imr, imr_buf[len-1].s);
        free(imr_buf);
      }
      if (*success && amr) {
        analyses *analysis = (size_t)len <= SIZE_MAX / sizeof(analyses)
                           ? malloc((size_t)len * sizeof(analyses))
                           : NULL;
        if (analysis) {
          computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)len);
          *success = 0 == memcmp(amr_hash.s, analysis[len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
        } else {
          /* malloc failed which counts as a transient error. */
          *success = result = false;
        }
        free(analysis);
      }
      if (*success) {
        txEnv env = build_txEnv(tx, taproot, &genesis_hash, &dag[len-1].cmr, ix);
        result = evalTCOProgram(success, dag, type_dag, (size_t)len, &env);
      }
      free(type_dag);
    }
  }

  free(dag);
  free(witnessAlloc);
  return result;
}
