#ifndef DAG_H
#define DAG_H

#include <stddef.h>
#include <stdint.h>

/* Unique numeric tags the various kinds of Simplicity combinators.
 * We choose to generate unique tags by using the reverse bit pattern used in Simplicity's bit-wise prefix code.
 * Thus all tags for core, witness, and hidden node are even numbers.
 * Jets and primitive tags are be odd numbers.
 */
#define COMP       0x00
#define CASE       0x10
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

/* Returns the number of children that a Simplicity combinator of the 'tag' kind has.
 *
 * Precondition: 'tag' is a valid tag.
 */
static inline int32_t numChildren(int32_t tag) {
  switch (tag & 0x7) {
   case 0x00: return 2;
   case 0x04: return 1;
   default: return 0;
  }
}

/* A node the the DAG of a Simplicity expression.
 * It consists of a 'tag' indicating the kind of expression the node represents.
 * The contents of a node depend on the kind of the expressions.
 * The node may have references to children, if it is a combinator kind of expression.
 *
 * Invariant: 'tag' is a valid tag;
 *            size_t child[2] when numChildren(tag) == 2;
 *            size_t child[1] when numChildren(tag) == 1;
 *            uint8_t hash[32] when HIDDEN == tag
 */
typedef struct dag_node {
  int32_t tag;
  union {
    size_t child[2];
    uint8_t hash[32];
  };
} dag_node;

/* A well-formed Simplicity DAG is an array of 'dag_node's,
 *
 *     dag_node dag[len],
 *
 * such that for all 'i', 0 <= 'i' < 'len' and for all 'j', 0 <= 'j' < 'numChildren'('dag'['i'].'tag'),
 *
 *     dag[i].child[j] < i.
 *
 * Note that a well-formed Simplicity DAG is not neccesarily a well-typed Simplicity DAG.
 */

/* A structure of static analyses for a particular node of a Simplicity DAG.
 * 'commitmentMerkleRoot' is the commitment Merkle root of the subexpressions represented by the node.
 */
typedef struct analyses {
  uint8_t commitmentMerkleRoot[32];
} analyses;

/* Given a well-formed dag representing a Simplicity expressions, compute the commitment Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis'['i'].'commitmentMerkleRoot' will be the CMR of the subexpression denoted by the slice ('dag_nodes'['i'])('dag').
 * The commitment Merkle root of the overall expression will be 'analysis'['len'-1].'commitmentMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len];
 *               'dag' is well-formed.
 */
void computeCommitmentMerkleRoot(analyses* analysis, const dag_node* dag, size_t len);

#endif
