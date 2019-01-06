/* This module provides functions for deserializing Simplicity's bit-wise prefix coding. */
#ifndef DESERIALIZE_H
#define DESERIALIZE_H

#include <stdio.h>
#include "dag.h"

#define ERR_BITSTREAM_EOF (-1)
#define ERR_DATA_OUT_OF_RANGE (-2)
#define ERR_FAIL_CODE (-3)
#define ERR_STOP_CODE (-4)
#define ERR_IMPOSSIBLE (-128)

/* Datatype representing a bit stream.
 * Bits are streamed from MSB to LSB.
 *
 * Invariant: NULL != file
 *            0 <= available <= CHAR_BIT
 */
typedef struct bit_stream {
  FILE* file;          /* Underlying byte stream */
  int available;       /* Number of bits unparsed from 'byte' */
  unsigned char byte;  /* Current, partially parsed byte */
} bit_stream;

/* Initialize a bit stream, 'stream', from a given byte stream, 'file'.
 * Precondition: NULL != file
 */
static inline bit_stream initializeBitStream(FILE* file) {
  return (bit_stream){ .file = file, .available = 0 };
}

/* Decode an encoded number between 1 and 2^31 - 1 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured.
 *
 * Precondition: NULL != stream
 */
int32_t decodeUptoMaxInt(bit_stream* stream);

/* Decode a length-prefixed Simplicity DAG from 'stream'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' the length prefix's value is too large.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceeding nodes.
 * Returns 'ERR_FAIL_CODE' if the encoding of a fail expression is encountered (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 0 if malloc fails.
 * In the above error cases, '*dag' is set to NULL.
 * If successful, returns a positive value equal to the length of an allocated array of (*dag).
 *
 * Precondition: NULL != dag
 *               NULL != stream
 *
 * Postcondition: (dag_node (*dag)[return_value] and '*dag' is a well-formed dag) when the return value of the function is positive;
 *                NULL == *dag when the return value is non-positive.
 */
int32_t decodeMallocDag(dag_node** dag, bit_stream* stream);

#endif
