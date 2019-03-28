/* This module provides function for running monomorphic type inference over Simplicity DAGs. */
#ifndef TYPEINFERENCE_H
#define TYPEINFERENCE_H

#include "dag.h"
#include "type.h"

/* If the Simplicity DAG, 'dag', has a principal type (including constraints due to sharing of subexprssions),
 * Then allocate an return a well-formed type DAG containing all the type annotations needed for the principal type of 'dag'
 * with all free type variables instantiated at ONE,
 * and update the .typeAnnotation array within each node of the 'dag' to referer to their type withing the resulting type DAG.
 *
 * Recall that a well-formed type DAG is always non-empty because the first element of the array is guarenteed to be the type 'ONE'.
 *
 * If the Simplicity DAG, 'dag', has no principal type (because it has a type error), then NULL is returned.
 * If malloc fails, then NULL is returned.
 *
 * Precondition: dag_node dag[len] is well-formed;
 *               '*census' contains a tally of the different tags that occur in 'dag'.
 *
 * Postcondition: the return value is NULL
 *             or 'dag' is well-typed with the allocated return value and without witness values.
 */
type* mallocTypeInference(dag_node* dag, size_t len, const combinator_counters* census);

#endif
