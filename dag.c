#include "dag.h"

#include <stdbool.h>
#include "tag.h"

/* Prepends the Simplicity CMR tag prefix to a string literal 's'. */
#define COMMITMENT_TAG(s) "Simplicity\x1F" "Commitment\x1F" s

/* Given a tag for a core or witness expression node, return the SHA-256 hash of its assocaited CMR tag.
 * This is the "initial value" for computing the commitment Merkle root for that expression.
 *
 * Precondition: 'tag' is a valid tag;
 *               HIDDEN != 'tag'
 */
static sha256_midstate cmrIV(int32_t tag) {
  /* Cache the initial values for all the tags. */
  static bool static_initialized = false;
  static sha256_midstate compIV,
                         caseIV,
                         pairIV,
                         disconnectIV,
                         injlIV,
                         injrIV,
                         takeIV,
                         dropIV,
                         idenIV,
                         unitIV,
                         witnessIV;
  if (!static_initialized) {
    MK_TAG(compIV.s, COMMITMENT_TAG("comp"));
    MK_TAG(caseIV.s, COMMITMENT_TAG("case"));
    MK_TAG(pairIV.s, COMMITMENT_TAG("pair"));
    MK_TAG(disconnectIV.s, COMMITMENT_TAG("disconnect"));
    MK_TAG(injlIV.s, COMMITMENT_TAG("injl"));
    MK_TAG(injrIV.s, COMMITMENT_TAG("injr"));
    MK_TAG(takeIV.s, COMMITMENT_TAG("take"));
    MK_TAG(dropIV.s, COMMITMENT_TAG("drop"));
    MK_TAG(idenIV.s, COMMITMENT_TAG("iden"));
    MK_TAG(unitIV.s, COMMITMENT_TAG("unit"));
    MK_TAG(witnessIV.s, COMMITMENT_TAG("witness"));
    static_initialized = true;
  }

  switch (tag) {
   case COMP: return compIV;
   case CASE: return caseIV;
   case PAIR: return pairIV;
   case DISCONNECT: return disconnectIV;
   case INJL: return injlIV;
   case INJR: return injrIV;
   case TAKE: return takeIV;
   case DROP: return dropIV;
   case IDEN: return idenIV;
   case UNIT: return unitIV;
   case WITNESS: return witnessIV;
  }
  /* Precondition violated. */
  return (sha256_midstate){0};
}

/* Given a well-formed dag representing a Simplicity expression, compute the commitment Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis'['i'].'commitmentMerkleRoot' will be the CMR of the subexpression denoted by the slice ('dag_nodes'['i' + 1])('dag').
 * The CMR of the overall expression will be 'analysis'['len' - 1].'commitmentMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len];
 *               'dag' is well-formed.
 */
void computeCommitmentMerkleRoot(analyses* analysis, const dag_node* dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    if (HIDDEN == dag[i].tag) {
      analysis[i].commitmentMerkleRoot = dag[i].hash;
    } else {
      analysis[i].commitmentMerkleRoot = cmrIV(dag[i].tag);

      /* Hash the child sub-expression's CMRs (if there are any children). */
      uint32_t block[16] = {0};
      size_t j = 8;
      switch (dag[i].tag) {
       case COMP:
       case CASE:
       case PAIR:
        memcpy(block + j, analysis[dag[i].child[1]].commitmentMerkleRoot.s, sizeof(uint32_t[8]));
        j = 0;
        /* Fall through. */
       case DISCONNECT: /* Only the first child is used in the CMR. */
       case INJL:
       case INJR:
       case TAKE:
       case DROP:
        memcpy(block + j, analysis[dag[i].child[0]].commitmentMerkleRoot.s, sizeof(uint32_t[8]));
        sha256_compression(analysis[i].commitmentMerkleRoot.s, block);
      }
    }
  }
}
