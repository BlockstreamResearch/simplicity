#include "dag.h"

#include <assert.h>
#include <stdbool.h>
#include "bounded.h"
#include "tag.h"
#include "uword.h"

/* :TODO: remove these includes after witnesses are supported, etc. */
#include <stdio.h>
#include <stdlib.h>

/* Prepends Simplicity tag prefixes to a string literal 's'. */
#define COMMITMENT_TAG(s) "Simplicity\x1F" "Commitment\x1F" s
#define WITNESS_TAG(s) "Simplicity\x1F" "Witness\x1F" s

/* Given a tag for a node, return the SHA-256 hash of its assocaited CMR tag.
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
   case ASSERTL:
   case ASSERTR:
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
  /* :TODO: Support jets and primitives */
  fprintf(stderr, "Commitment Merkle root for jets and primitives not yet implemented\n");
  exit(EXIT_FAILURE);

  /* Precondition violated. */
  assert(false);
  return (sha256_midstate){0};
}

/* Given a tag for a node, return the SHA-256 hash of its assocaited WMR tag.
 * This is the "initial value" for computing the witness Merkle root for that expression.
 *
 * Precondition: 'tag' is a valid tag;
 *               HIDDEN != 'tag'
 */
static sha256_midstate wmrIV(int32_t tag) {
  /* Cache the initial values for all the tags. */
  static bool static_initialized = false;
  static sha256_midstate compIV,
                         assertlIV,
                         assertrIV,
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
    MK_TAG(compIV.s, WITNESS_TAG("comp"));
    MK_TAG(assertlIV.s, WITNESS_TAG("assertl"));
    MK_TAG(assertrIV.s, WITNESS_TAG("assertr"));
    MK_TAG(caseIV.s, WITNESS_TAG("case"));
    MK_TAG(pairIV.s, WITNESS_TAG("pair"));
    MK_TAG(disconnectIV.s, WITNESS_TAG("disconnect"));
    MK_TAG(injlIV.s, WITNESS_TAG("injl"));
    MK_TAG(injrIV.s, WITNESS_TAG("injr"));
    MK_TAG(takeIV.s, WITNESS_TAG("take"));
    MK_TAG(dropIV.s, WITNESS_TAG("drop"));
    MK_TAG(idenIV.s, WITNESS_TAG("iden"));
    MK_TAG(unitIV.s, WITNESS_TAG("unit"));
    MK_TAG(witnessIV.s, WITNESS_TAG("witness"));
    static_initialized = true;
  }

  switch (tag) {
   case COMP: return compIV;
   case ASSERTL: return assertlIV;
   case ASSERTR: return assertrIV;
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
  /* :TODO: Support jets and primitives */
  fprintf(stderr, "Witness Merkle root for jets and primitives not yet implemented\n");
  exit(EXIT_FAILURE);

  /* Precondition violated. */
  assert(false);
  return (sha256_midstate){0};
}

/* Given a SHA-256 midstate, 's', of '*count / 512' blocks, and
 * a 'block' with '*count % 512' bits set and with the remaining bits set to 0,
 * push a new bit of value 'bit' onto the block.
 * If the block ends up full, compress and update the midstate.
 *
 * Precondition: uint32_t s[8];
 *               uint32_t block[16];
 *               NULL != count;
 */
static void sha256_pushBit(uint32_t* s, uint32_t* block, size_t* count, bool bit) {
  if (bit) block[*count / 32 % 16] |= (uint32_t)1 << (31 - *count % 32);
  (*count)++;
  if (0 == *count % 512) {
    sha256_compression(s, block);
    memset(block, 0, sizeof(uint32_t[16]));
  }
}

/* Given a SHA-256 midstate, 's', of '*count / 512' blocks, and
 * a 'block' with '*count % 512' bits set and with the remaining bits set to 0,
 * finalize the SHA-256 computation by adding SHA-256 padding and set 's' to the resulting SHA-256 hash.
 *
 * Precondition: uint32_t s[8];
 *               uint32_t block[16];
 *               NULL != count;
 */
static void sha256_end(uint32_t* s, uint32_t* block, const size_t len) {
  size_t count = len;
  sha256_pushBit(s, block, &count, 1);
  if (448 < count % 512) {
    sha256_compression(s, block);
    memset(block, 0, sizeof(uint32_t[14]));
  }
  block[14] = (uint32_t)(len >> 32);
  block[15] = (uint32_t)len;
  sha256_compression(s, block);
}

/* Compute the SHA-256 hash, 's', of the bitstring represented by 'witness'.
 *
 * Precondition: uint32_t s[8];
 *               (*witness) is a valid bitstring;
 */
static void sha256_witnessData(uint32_t* s, const bitstring* witness) {
  uint32_t block[16] = { 0 };
  size_t count = 0;
  sha256_iv(s);
  /* :TODO: Optimize this loop. */
  while (count < witness->len) {
    sha256_pushBit(s, block, &count, 1 & witness->arr[(witness->offset + count)/CHAR_BIT]
                                      >> (CHAR_BIT - 1 - (witness->offset + count) % CHAR_BIT));
  }
  sha256_end(s, block, count);
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
    if (HIDDEN == dag[i].tag) {
      analysis[i].commitmentMerkleRoot = dag[i].hash;
    } else {
      analysis[i].commitmentMerkleRoot = cmrIV(dag[i].tag);

      /* Hash the child sub-expression's CMRs (if there are any children). */
      uint32_t block[16] = {0};
      size_t j = 8;
      switch (dag[i].tag) {
       case COMP:
       case ASSERTL:
       case ASSERTR:
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
    if (HIDDEN == dag[i].tag) {
      analysis[i].witnessMerkleRoot = dag[i].hash;
    } else {
      analysis[i].witnessMerkleRoot = wmrIV(dag[i].tag);

      uint32_t block[16] = {0};
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
        sha256_witnessData(block + 8, &dag[i].witness.data);
        sha256_compression(analysis[i].witnessMerkleRoot.s, block);
        break;
      }
    }
  }
}

/* This function finds subexpressions in 'dag' that have known jetted implementations and replaces them by those jets.
 * For jets that have a discount, one would normally have jets deserialized via a code for the specific jet.
 * If all jets are discounted jets, one might not even use this function in production.
 *
 * A 'filter' can be set to only force some kinds of jets.  This parameter is mostly used for testing purposes.
 * In produciton we expect 'filter' to be passed the 'JET_ALL' value.
 *
 * Precondition: dag_node dag[len] and 'dag' has witness data and is well-typed;
 *               analyses analysis[len] contains the witness Merkle roots for each subexpression of 'dag'.
 */
void forceJets(dag_node* dag, const analyses* analysis, const size_t len, JET_FLAG filter) {
  if (!filter) return;
  for (size_t i = 0; i < len; ++i) {
    jet_ptr jet = lookupJet(&analysis[i].witnessMerkleRoot, filter);
    if (jet) {
      dag[i].tag = JET;
      dag[i].jet = jet;
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
                /* Travese the first element of the product type, if it has any data. */
                type_dag[next].back = cur;
                cur = next;
                continue;
              }
            }
            next = typeSkip(type_dag[cur].typeArg[1], type_dag);
            if (next) {
              /* Travese the second element of the product type, if it has any data. */
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
         * the difference between the remaning witness length from before and after parsing.
         */
        dag[i].witness.data.len -= witness.len;

        /* Note: Above we use 'typeSkip' to skip over long chains of products against trivial types
         * This avoids a potential DOS vunlernability where a DAG of deeply nested products of unit types with sharing is traversed,
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
