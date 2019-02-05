/* This module defines the stucture for Simplicity type DAGs and computes type Merkle roots. */
#ifndef TYPE_H
#define TYPE_H

#include <stddef.h>
#include "tag.h"

typedef enum typeName
  { ONE, SUM, PRODUCT }
typeName;

/* A structure for Simplicity type DAGs. */
typedef struct type {
  size_t typeArg[2];
  sha256_midstate typeMerkleRoot;
  typeName kind;
} type;

/* A well-formed type DAG is an array of 'type's,
 *
 *     type type_dag[n],
 *
 * such that
 *
 *     0 < n
 *
 * and
 *
 *     type_dag[0].kind == ONE.
 *
 * and for all 'i', 1 <= 'i' < 'n' and for all 'j', 0 <= 'j' < 2.
 *
 *     type_dag[i].kind \in { SUM, PRODUCT } and type_dag[i].typeArg[j] < i.
 */

/* Given a well-formed 'type_dag', compute the type Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'type_dag'['i'].'typeMerkleRoot' will be the TMR of the subexpression denoted by the slice
 *
 *     (type_dag[i + 1])type_dag.
 *
 * Precondition: type type_dag[len] and 'type_dag' is well-formed.
 */
void computeTypeAnalyses(type* type_dag, size_t len);

#endif
