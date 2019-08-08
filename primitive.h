/* This module defines the interface that each Simplicity application must implement.
 */
#ifndef PRIMITIVE_H
#define PRIMITIVE_H

#include "bitstream.h"
#include "typeInference.h"

/* Allocate a fresh set of unification variables bound to at least all the types necessary
 * for all the jets that can be created by 'decodeJet', and also the type 'TWO^256'.
 * Return the number of non-trivial bindings created.
 *
 * However, if malloc fails, then return 0.
 *
 * Precondition: NULL != bound_var;
 *               NULL != word256_ix;
 *
 * Postcondition: Either '*bound_var == NULL' and the function returns 0
 *                or 'unification_var (*bound_var)[N]' is an array of fresh unification variables bound to various types
 *                   such that for any 'jet : A |- B' there is some 'i < N' and 'j < N' such that '(*bound_var)[i]' is bound to 'A'
 *                                                                                            and '(*bound_var)[j]' is bound to 'B'
 *                   and, in particular, '*word256_ix < N' and '(*bound_var)[*word256_ix]' is bound the type 'TWO^256'
 */
size_t mallocBoundVars(unification_var** bound_var, size_t* word256_ix);

/* Decode an application specific jet from 'stream' into 'node'.
 * An application specific jet is a jet that is, or includes a primitive node.
 * All application specific jets begin with a bit prefix of '10' which needs to have already been consumed from the 'stream'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != node
 *               NULL != stream
 */
int32_t decodeJet(dag_node* node, bitstream* stream);

#endif
