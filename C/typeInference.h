/* This module provides function for running monomorphic type inference over Simplicity DAGs. */
#ifndef TYPEINFERENCE_H
#define TYPEINFERENCE_H

#include "dag.h"
#include "type.h"

/* If the Simplicity DAG, 'dag', has a principal type (including constraints due to sharing of subexpressions),
 * then allocate a well-formed type DAG containing all the type annotations needed for the principal type of 'dag'
 * with all free type variables instantiated at ONE, and set '*type_dag' to this allocation.
 * and update the .typeAnnotation array within each node of the 'dag' to refer to their type within the resulting type DAG.
 *
 * Recall that a well-formed type DAG is always non-empty because the first element of the array is guaranteed to be the type 'ONE'.
 *
 * If malloc fails, return 'false', otherwise return 'true'.
 * If the Simplicity DAG, 'dag', has no principal type (because it has a type error), then '*type_dag' is set to NULL.
 *
 * Precondition: NULL != type_dag
 *               dag_node dag[len] is well-formed;
 *               '*census' contains a tally of the different tags that occur in 'dag'.
 *
 * Postcondition: if the return value is 'true'
 *                then either NULL == '*type_dag'
 *                     or 'dag' is well-typed with '*type_dag' and without witness values.
 *                if the return value is 'false' then 'NULL == *type_dag'
 */
bool mallocTypeInference(type** type_dag, dag_node* dag, size_t len, const combinator_counters* census);

#endif
