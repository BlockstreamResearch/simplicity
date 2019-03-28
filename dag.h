/* This module defines the structure for Simplicity DAGs, and functions for some analysis of that structure,
 * such as computing Merkle Roots.
 */
#ifndef DAG_H
#define DAG_H

#include <stddef.h>
#include <stdint.h>
#include "type.h"
#include "jetTable.h"

/* Unique numeric tags the various kinds of Simplicity combinators.
 * We choose to generate unique tags by using the reverse bit pattern used in Simplicity's bit-wise prefix code.
 * Thus all tags for core, witness, and hidden node are even numbers.
 * Jets and primitive tags are be odd numbers.
 * Assertions are not part of Simplicity's bit-wise prefix code, and instead make use of unused codes that extend the code for CASE.
 */
#define COMP       0x00
#define CASE       0x10
#define ASSERTL    0x30
#define ASSERTR    0x70
#define PAIR       0x08
#define DISCONNECT 0x18
#define INJL       0x04
#define INJR       0x14
#define TAKE       0x0c
#define DROP       0x1c
#define IDEN       0x02
#define UNIT       0x12
#define HIDDEN     0x06
#define WITNESS    0x0e
#define JET        0x03

/* This structure is use to count the different kinds of combinators in a Simplicity DAG. */
typedef struct combinator_counters {
  size_t comp_cnt, case_cnt, pair_cnt, disconnect_cnt,
         injl_cnt, injr_cnt, take_cnt, drop_cnt;
} combinator_counters;

/* Given a tag for an expression, add it to the 'census'.
 *
 * Precondition: 'tag' is a valid tag.
 */
static inline void enumerator(combinator_counters* census, int32_t tag) {
  if (!census) return;
  switch (tag) {
   case COMP: census->comp_cnt++; return;
   case ASSERTL:
   case ASSERTR: /* Assertions are counted as CASE combinators. */
   case CASE: census->case_cnt++; return;
   case PAIR: census->pair_cnt++; return;
   case DISCONNECT: census->disconnect_cnt++; return;
   case INJL: census->injl_cnt++; return;
   case INJR: census->injr_cnt++; return;
   case TAKE: census->take_cnt++; return;
   case DROP: census->drop_cnt++; return;
  }
}

/* Returns the number of children that a Simplicity combinator of the 'tag' kind has.
 *
 * Precondition: 'tag' is a valid tag.
 */
static inline size_t numChildren(int32_t tag) {
  switch (tag & 0x7) {
   case 0x00: return 2;
   case 0x04: return 1;
   default: return 0;
  }
}

/* Represents a bitstring of length 'len' bits using an array of unsigned char.
 * The bit at index 'n', where 0 <= 'n' < 'len', is located at bit '1 << (CHAR_BIT - 1 - (offset + n) % CHAR_BIT)' of
 * array element 'arr[(offset + n) / CHAR_BIT]'.
 * Other bits in the array may be any value.
 *
 * Invariant: 0 < len implies
 *              unsigned char arr[(offset + len - 1) / CHAR_BIT + 1];
 */
typedef struct bitstring {
  size_t len;
  size_t offset;
  const unsigned char* arr;
} bitstring;

/* The contents of a 'WITNESS' node that has witness data. */
typedef struct witnessInfo {
  size_t typeAnnotation[2]; /* A 'witness v : A |- B' expression has only 2 type annotations. */
  bitstring data;           /* A compect bitstring representation for a value 'v' of type 'B'. */
} witnessInfo;

/* A node the the DAG of a Simplicity expression.
 * It consists of a 'tag' indicating the kind of expression the node represents.
 * The contents of a node depend on the kind of the expressions.
 * The node may have references to children, when it is a combinator kind of expression.
 *
 * Invariant: 'tag' is a valid tag;
 *            sha256_midstate hash is active when tag == HIDDEN;
 *            jet_ptr jet is active when tag == JET;
 *            witnessInfo witness is be active when tag == WITNESS and the node has witness data
 *            size_t child[numChildren(tag)] when tag \notin {HIDDEN, JET, WITNESS};
 *                                        or when tag == WITNESS and the node is without witness data.
 */
typedef struct dag_node {
  int32_t tag;
  union {
    struct {
      size_t typeAnnotation[4];
      size_t child[2];
    };
    witnessInfo witness;
    sha256_midstate hash;
    jet_ptr jet;
  };
} dag_node;

/* A well-formed Simplicity DAG is an array of 'dag_node's,
 *
 *     dag_node dag[len],
 *
 * such that
 *
 *     0 < len
 *
 * and for all 'i', 0 <= 'i' < 'len' and for all 'j', 0 <= 'j' < 'numChildren(dag[i].tag)',
 *
 *     dag[i].child[j] < i
 *
 * and for all 'i', 0 <= 'i' < 'len',
 *
 *     if dag[dag[i].child[0]].tag == HIDDEN then dag[i].tag == ASSERTR
 *
 *     and
 *
 *     if dag[dag[i].child[1]].tag == HIDDEN then dag[i].tag == ASSERTL
 *
 * Note that a well-formed Simplicity DAG is not neccesarily a well-typed Simplicity DAG.
 */

/* A structure of static analyses for a particular node of a Simplicity DAG.
 * 'commitmentMerkleRoot' is the commitment Merkle root of the subexpressions represented by the node.
 */
typedef struct analyses {
  sha256_midstate commitmentMerkleRoot;
  sha256_midstate witnessMerkleRoot;
} analyses;

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
void computeCommitmentMerkleRoot(analyses* analysis, const dag_node* dag, size_t len);

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
void computeWitnessMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, size_t len);

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
void forceJets(dag_node* dag, const analyses* analysis, size_t len, JET_FLAG filter);

/* This function fills in the 'WITNESS' nodes of a 'dag' with the data from 'witness'.
 * For each 'WITNESS' : A |- B expression in 'dag', the bits from the 'witness' bitstring are decoded in turn
 * to construct a compact representation of a witness value of type B.
 * This funciton only returns 'true' when exactly 'witness.len' bits are consumed by all the 'dag's witness values.
 *
 * Precondition: dag_node dag[len] and 'dag' without witness data and is well-typed with 'type_dag';
 *               witness is a valid bitstring;
 *
 * Postcondition: dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'
 *                  when the result is 'true';
 */
bool fillWitnessData(dag_node* dag, type* type_dag, const size_t len, bitstring witness);

#endif
