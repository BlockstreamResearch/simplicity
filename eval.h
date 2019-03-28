/* This module provides functions for evaluating Simplicity programs and expressions.
 */
#ifndef EVAL_H
#define EVAL_H

#include "dag.h"
#include "frame.h"

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[roundUWord(inputSize)]'.
 *
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, return 'false'.
 * If malloc fails, return 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, return 'false'.
 * Otherwise return 'true'.
 *
 * If the function returns 'true' and 'NULL != output', copy the final active write frame's data to 'output[roundWord(outputSize)]'.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               outputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               inputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               output == NULL or UWORD output[roundUWord(outputSize)];
 *               input == NULL or UWORD input[roundUWord(inputSize)];
 */
bool evalTCOExpression( UWORD* output, size_t outputSize, const UWORD* input, size_t inputSize
                      , const dag_node* dag, type* type_dag, size_t len
                      );

/* Run the Bit Machine on the well-typed Simplicity program 'dag[len]'.
 *
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, return 'false'.
 * If malloc fails, return 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, return 'false'.
 * Otherwise return 'true'.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type 1 |- 1;
 */
static inline bool evalTCOProgram(const dag_node* dag, type* type_dag, size_t len) {
  return evalTCOExpression( NULL, 0, NULL, 0, dag, type_dag, len);
}
#endif
