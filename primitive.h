/* This module defines the interface that each Simplicity application must implement.
 */
#ifndef PRIMITIVE_H
#define PRIMITIVE_H

#include "bitstream.h"
#include "dag.h"

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
