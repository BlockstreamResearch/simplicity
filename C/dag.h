/* This module defines the structure for Simplicity DAGs, and functions for some analysis of that structure,
 * such as computing Merkle Roots.
 */
#ifndef DAG_H
#define DAG_H

#include <stddef.h>
#include <stdint.h>
#include "type.h"

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

/* A node the the DAG of a Simplicity expression.
 * It consists of a 'tag' indicating the kind of expression the node represents.
 * The contents of a node depend on the kind of the expressions.
 * The node may have references to children, when it is a combinator kind of expression.
 *
 * Invariant: 'tag' is a valid tag;
 *            size_t child[numChildren(tag)] when tag != HIDDEN;
 *            sha256_midstate hash is active when tag == HIDDEN;
 */
typedef struct dag_node {
  int32_t tag;
  union {
    struct {
      size_t child[2];
      size_t typeAnnotation[4];
    };
    sha256_midstate hash;
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
  size_t extraCellsBoundTCO[2];
  size_t extraStackBound[2]; /* extraStackBound[0] is for TCO off and extraStackBound[1] is for TCO on */
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
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag'.
 */
void computeWitnessMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, size_t len);

/* Given a well-typed dag representing a Simplicity expression, compute the bounds on memory requirement for evaluation.
 * For all 'i', 0 <= 'i' < 'len', compute 'analysis[i].extraCellsBoundTCO' and 'analysis[i].extraStackBoundTCO'
 * for the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag'.
 */
void computeEvalTCOBounds(analyses* analysis, const dag_node* dag, const type* type_dag, size_t len);

#endif
