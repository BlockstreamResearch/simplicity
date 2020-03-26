#include "dag.h"

#include <assert.h>
#include <stdbool.h>
#include "bounded.h"
#include "callonce.h"
#include "tag.h"
#include "sha256.h"
#include "uword.h"
#include "unreachable.h"

/* Prepends Simplicity tag prefixes to a string literal 's'. */
#define COMMITMENT_TAG(s) "Simplicity\x1F" "Commitment\x1F" s
#define WITNESS_TAG(s) "Simplicity\x1F" "Witness\x1F" s

/* Cached initial values for all the tags.
 * Only to be accessed through 'cmrIV' or 'wmrIV'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static sha256_midstate cmr_compIV,
                       cmr_caseIV,
                       cmr_pairIV,
                       cmr_disconnectIV,
                       cmr_injlIV,
                       cmr_injrIV,
                       cmr_takeIV,
                       cmr_dropIV,
                       cmr_idenIV,
                       cmr_unitIV,
                       cmr_witnessIV;
static sha256_midstate wmr_compIV,
                       wmr_assertlIV,
                       wmr_assertrIV,
                       wmr_caseIV,
                       wmr_pairIV,
                       wmr_disconnectIV,
                       wmr_injlIV,
                       wmr_injrIV,
                       wmr_takeIV,
                       wmr_dropIV,
                       wmr_idenIV,
                       wmr_unitIV,
                       wmr_witnessIV;
static void static_initialize(void) {
  MK_TAG(cmr_compIV.s, COMMITMENT_TAG("comp"));
  MK_TAG(cmr_caseIV.s, COMMITMENT_TAG("case"));
  MK_TAG(cmr_pairIV.s, COMMITMENT_TAG("pair"));
  MK_TAG(cmr_disconnectIV.s, COMMITMENT_TAG("disconnect"));
  MK_TAG(cmr_injlIV.s, COMMITMENT_TAG("injl"));
  MK_TAG(cmr_injrIV.s, COMMITMENT_TAG("injr"));
  MK_TAG(cmr_takeIV.s, COMMITMENT_TAG("take"));
  MK_TAG(cmr_dropIV.s, COMMITMENT_TAG("drop"));
  MK_TAG(cmr_idenIV.s, COMMITMENT_TAG("iden"));
  MK_TAG(cmr_unitIV.s, COMMITMENT_TAG("unit"));
  MK_TAG(cmr_witnessIV.s, COMMITMENT_TAG("witness"));
  MK_TAG(wmr_compIV.s, WITNESS_TAG("comp"));
  MK_TAG(wmr_assertlIV.s, WITNESS_TAG("assertl"));
  MK_TAG(wmr_assertrIV.s, WITNESS_TAG("assertr"));
  MK_TAG(wmr_caseIV.s, WITNESS_TAG("case"));
  MK_TAG(wmr_pairIV.s, WITNESS_TAG("pair"));
  MK_TAG(wmr_disconnectIV.s, WITNESS_TAG("disconnect"));
  MK_TAG(wmr_injlIV.s, WITNESS_TAG("injl"));
  MK_TAG(wmr_injrIV.s, WITNESS_TAG("injr"));
  MK_TAG(wmr_takeIV.s, WITNESS_TAG("take"));
  MK_TAG(wmr_dropIV.s, WITNESS_TAG("drop"));
  MK_TAG(wmr_idenIV.s, WITNESS_TAG("iden"));
  MK_TAG(wmr_unitIV.s, WITNESS_TAG("unit"));
  MK_TAG(wmr_witnessIV.s, WITNESS_TAG("witness"));
}
/* Given a tag for a node, return the SHA-256 hash of its associated CMR tag.
 * This is the "initial value" for computing the commitment Merkle root for that expression.
 *
 * Precondition: 'tag' \notin {HIDDEN, JET}
 */
static sha256_midstate cmrIV(tag_t tag) {
  call_once(&static_initialized, &static_initialize);

  switch (tag) {
   case COMP: return cmr_compIV;
   case ASSERTL:
   case ASSERTR:
   case CASE: return cmr_caseIV;
   case PAIR: return cmr_pairIV;
   case DISCONNECT: return cmr_disconnectIV;
   case INJL: return cmr_injlIV;
   case INJR: return cmr_injrIV;
   case TAKE: return cmr_takeIV;
   case DROP: return cmr_dropIV;
   case IDEN: return cmr_idenIV;
   case UNIT: return cmr_unitIV;
   case WITNESS: return cmr_witnessIV;
   /* Precondition violated. */
   case HIDDEN:
   case JET:
    break;
  }
  assert(false);
  UNREACHABLE;
}

/* Given a tag for a node, return the SHA-256 hash of its associated WMR tag.
 * This is the "initial value" for computing the witness Merkle root for that expression.
 *
 * Precondition: 'tag' \notin {HIDDEN, JET}
 */
static sha256_midstate wmrIV(tag_t tag) {
  call_once(&static_initialized, &static_initialize);

  switch (tag) {
   case COMP: return wmr_compIV;
   case ASSERTL: return wmr_assertlIV;
   case ASSERTR: return wmr_assertrIV;
   case CASE: return wmr_caseIV;
   case PAIR: return wmr_pairIV;
   case DISCONNECT: return wmr_disconnectIV;
   case INJL: return wmr_injlIV;
   case INJR: return wmr_injrIV;
   case TAKE: return wmr_takeIV;
   case DROP: return wmr_dropIV;
   case IDEN: return wmr_idenIV;
   case UNIT: return wmr_unitIV;
   case WITNESS: return wmr_witnessIV;
   /* Precondition violated. */
   case HIDDEN:
   case JET:
    break;
  }
  assert(false);
  UNREACHABLE;
}

/* Given a well-formed dag representing a Simplicity expression, compute the commitment Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis[i].commitmentMerkleRoot' will be the CMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * The CMR of the overall expression will be 'analysis[len - 1].commitmentMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' is well-formed.
 */
void computeCommitmentMerkleRoot(analyses* analysis, const dag_node* dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uint32_t block[16] = {0};
    size_t j = 8;

    /* For jets and primitives, their commitment Merkle root is the same as their witness Merkle root. */
    analysis[i].commitmentMerkleRoot = HIDDEN == dag[i].tag ? dag[i].hash
                                     : JET == dag[i].tag ? dag[i].wmr
                                     : cmrIV(dag[i].tag);

    /* Hash the child sub-expression's CMRs (if there are any children). */
    switch (dag[i].tag) {
     case COMP:
     case ASSERTL:
     case ASSERTR:
     case CASE:
     case PAIR:
      memcpy(block + j, analysis[dag[i].child[1]].commitmentMerkleRoot.s, sizeof(uint32_t[8]));
      j = 0;
      /*@fallthrough@*/
     case DISCONNECT: /* Only the first child is used in the CMR. */
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      memcpy(block + j, analysis[dag[i].child[0]].commitmentMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].commitmentMerkleRoot.s, block);
     case IDEN:
     case UNIT:
     case WITNESS:
     case HIDDEN:
     case JET:
      break;
    }
  }
}

/* Given a well-typed dag representing a Simplicity expression, compute the witness Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis[i].witnessMerkleRoot' will be the WMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * The WMR of the overall expression will be 'analysis[len - 1].witnessMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'.
 * Postconditon: analyses analysis[len] contains the witness Merkle roots of each subexpressions of 'dag'.
 */
void computeWitnessMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uint32_t block[16] = {0};

    analysis[i].witnessMerkleRoot = HIDDEN == dag[i].tag ? dag[i].hash
                                  : JET == dag[i].tag ? dag[i].wmr
                                  : wmrIV(dag[i].tag);
    switch (dag[i].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
     case DISCONNECT:
      memcpy(block, type_dag[dag[i].typeAnnotation[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, type_dag[dag[i].typeAnnotation[2]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[3]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].witnessMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].witnessMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      break;
     case COMP:
     case PAIR:
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, type_dag[dag[i].typeAnnotation[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[2]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].witnessMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].witnessMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      break;
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      memcpy(block, type_dag[dag[i].typeAnnotation[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, type_dag[dag[i].typeAnnotation[2]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[0]].witnessMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      break;
     case IDEN:
     case UNIT:
      memcpy(block + 8, type_dag[dag[i].typeAnnotation[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      break;
     case WITNESS:
      memcpy(block + 8, type_dag[dag[i].witness.typeAnnotation[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      memcpy(block, type_dag[dag[i].witness.typeAnnotation[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_bitstring(block + 8, &dag[i].witness.data);
      sha256_compression(analysis[i].witnessMerkleRoot.s, block);
      break;
     case HIDDEN:
     case JET:
      break;
    }
  }
}

/* This function fills in the 'WITNESS' nodes of a 'dag' with the data from 'witness'.
 * For each 'WITNESS' : A |- B expression in 'dag', the bits from the 'witness' bitstring are decoded in turn
 * to construct a compact representation of a witness value of type B.
 * This function only returns 'true' when exactly 'witness.len' bits are consumed by all the 'dag's witness values.
 *
 * Note: the 'witness' value is passed by copy because the implementation manipulates a local copy of the structure.
 *
 * Precondition: dag_node dag[len] and 'dag' without witness data and is well-typed with 'type_dag';
 *               witness is a valid bitstring;
 *
 * Postcondition: dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'
 *                  when the result is 'true';
 */
bool fillWitnessData(dag_node* dag, type* type_dag, const size_t len, bitstring witness) {
  for (size_t i = 0; i < len; ++i) {
    if (WITNESS == dag[i].tag) {
      if (witness.len <= 0) {
        /* There is no more data left in witness. */
        dag[i].witness = (witnessInfo){ .typeAnnotation = { dag[i].typeAnnotation[0], dag[i].typeAnnotation[1] } };
        /* This is fine as long as the witness type is trivial */
        if (type_dag[dag[i].witness.typeAnnotation[1]].bitSize) return false;
      } else {
        dag[i].witness = (witnessInfo)
          { .typeAnnotation = { dag[i].typeAnnotation[0], dag[i].typeAnnotation[1] }
          , .data = { .arr = &witness.arr[witness.offset/CHAR_BIT]
                    , .offset = witness.offset % CHAR_BIT
                    , .len = witness.len /* The value of .len will be finalized after the while loop. */
          }         };

        /* Traverse the witness type to parse the witness's compact representation as a bit sting. */
        size_t cur = typeSkip(dag[i].witness.typeAnnotation[1], type_dag);
        bool calling = true;
        type_dag[cur].back = 0;
        while (cur) {
          if (SUM == type_dag[cur].kind) {
            /* Parse one bit and traverse the left type or the right type depending on the value of the bit parsed. */
            assert(calling);
            if (witness.len <= 0) return false;
            bool bit = 1 & (witness.arr[witness.offset/CHAR_BIT] >> (CHAR_BIT - 1 - witness.offset % CHAR_BIT));
            witness.offset++; witness.len--;
            size_t next = typeSkip(type_dag[cur].typeArg[bit], type_dag);
            if (next) {
              type_dag[next].back = type_dag[cur].back;
              cur = next;
            } else {
              cur = type_dag[cur].back;
              calling = false;
            }
          } else {
            assert(PRODUCT == type_dag[cur].kind);
            size_t next;
            if (calling) {
              next = typeSkip(type_dag[cur].typeArg[0], type_dag);
              if (next) {
                /* Traverse the first element of the product type, if it has any data. */
                type_dag[next].back = cur;
                cur = next;
                continue;
              }
            }
            next = typeSkip(type_dag[cur].typeArg[1], type_dag);
            if (next) {
              /* Traverse the second element of the product type, if it has any data. */
              type_dag[next].back = type_dag[cur].back;
              cur = next;
              calling = true;
            } else {
              cur = type_dag[cur].back;
              calling = false;
            }
          }
        }
        /* The length of this 'WITNESS' node's witness value is
         * the difference between the remaining witness length from before and after parsing.
         */
        dag[i].witness.data.len -= witness.len;

        /* Note: Above we use 'typeSkip' to skip over long chains of products against trivial types
         * This avoids a potential DOS vulnerability where a DAG of deeply nested products of unit types with sharing is traversed,
         * taking exponential time.
         * While traversing still could take exponential time in terms of the size of the type's dag,
         * at least one bit of witness data is required per PRODUCT type encountered.
         * This ought to limit the total number of times through the above loop to no more that 3 * dag[i].witness.data.len.
         */
        /* :TODO: build a test case that creates such a long chain of products with unit types for a witness value. */
      }
    }
  }
  return (0 == witness.len);
}
