#include "dag.h"

#include <stdbool.h>
#include <string.h>
#include "sha256/compression.h"

/* The length of a string literal is one less than its sizeof due to the terminating 'NULL' character. */
#define LENGTH_OF(s) (sizeof("" s) - 1)

/* The number of bytes that fits in a single SHA-256 block is 55 bytes.
 * This leaves one byte for the '0x80' terminator and eight bytes for the 64-bit length field.
 */
#define MAX_TAG_LEN 55

/* Compute the SHA-256 value (with padding) of a 'tagName' and return the SHA-256 midstate for that hash.
 * The 'tagName' must fit into a single SHA-256 block meaning it cannot exceed 55 ('MAX_TAG_LEN') bytes.
 * The 'tagName' is not expected to be 'NULL' terminated.
 * This function should only be called through the 'MK_TAG' macro.
 *
 * Precondition: uint32 midstate[8];
 *               uint8_t tagName[len];
 *               len <= MAX_TAG_LEN (= 55)
 */
static void mkTag(uint32_t* midstate, const uint8_t* tagName, const size_t len) {
  uint8_t block[64] = {0};

  memcpy(block, tagName, sizeof(uint8_t[len]));
  block[len] = 0x80;
  /* The length of tag (in bits) is guarenteed to fit within two bytes. */
  block[63] = (len << 3) & 0xff;
  block[62] = len >> 5;

  sha256_iv(midstate);
  sha256_compression(midstate, block);
}

/* TAG_NAME(s) takes a string literal, verifies its length is less than 'MAX_TAG_LEN', and removes the trailing NULL character. */
#define TAG_NAME(s) (((struct { const uint8_t name[LENGTH_OF(s)]; _Static_assert(LENGTH_OF(s) <= MAX_TAG_LEN, "Tag Name too long: " s); }){ .name = "" s }).name)

/* MK_TAG(midstate, s) takes a string literal, 's', and fills in the 'tag' and 'len' arguments of 'mkTag' appropriately. */
#define MK_TAG(midstate, s) (mkTag((midstate), TAG_NAME(s), LENGTH_OF(s)))

/* Prepends the Simplicity CMR tag prefix to a string literal 's'. */
#define COMMITMENT_TAG(s) "Simplicity\x1F" "Commitment\x1F" s

typedef struct sha256_midstate {
  uint32_t s[8];
} sha256_midstate;

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
      memcpy(analysis[i].commitmentMerkleRoot, dag[i].hash, sizeof(uint8_t[32]));
    } else {
      sha256_midstate cmr = cmrIV(dag[i].tag);

      /* Hash the child sub-expression's CMRs (if there are any children). */
      uint8_t block[64] = {0};
      size_t j = 32;
      switch (dag[i].tag) {
       case COMP:
       case CASE:
       case PAIR:
        memcpy(block + j, analysis[dag[i].child[1]].commitmentMerkleRoot, sizeof(uint8_t[32]));
        j = 0;
        /* Fall through. */
       case DISCONNECT: /* Only the first child is used in the CMR. */
       case INJL:
       case INJR:
       case TAKE:
       case DROP:
        memcpy(block + j, analysis[dag[i].child[0]].commitmentMerkleRoot, sizeof(uint8_t[32]));
        sha256_compression(cmr.s, block);
      }
      sha256_fromMidstate(analysis[i].commitmentMerkleRoot, cmr.s);
    }
  }
}
