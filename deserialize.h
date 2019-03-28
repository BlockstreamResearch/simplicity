/* This module provides functions for deserializing Simplicity's bit-wise prefix coding. */
#ifndef DESERIALIZE_H
#define DESERIALIZE_H

#include <stdio.h>
#include "dag.h"

#define ERR_BITSTREAM_EOF (-1)
#define ERR_DATA_OUT_OF_RANGE (-2)
#define ERR_FAIL_CODE (-3)
#define ERR_STOP_CODE (-4)
#define ERR_HIDDEN (-5)
#define ERR_MALLOC (-6)

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
 * Returns 'ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *  (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'ERR_HIDDEN' if there are illegal HIDDEN children in the DAG.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_MALLOC' if malloc fails.
 * In the above error cases, '*dag' is set to NULL.
 * If successful, returns a positive value equal to the length of an allocated array of (*dag).
 *
 * Precondition: NULL != dag
 *               NULL != stream
 *
 * Postcondition: if the return value of the function is positive
 *                  then (dag_node (*dag)[return_value] and '*dag' is a well-formed dag without witness data);
 *                '*census' contains a tally of the different tags that occur in 'dag' when the return value
 *                          of the function is positive and when NULL != census;
 *                NULL == *dag when the return value is negative.
 */
int32_t decodeMallocDag(dag_node** dag, combinator_counters* census, bit_stream* stream);

/* Decode a string of up to 2^31 - 1 bits from 'stream'.
 * This is the format in which the data for 'WITNESS' nodes are encoded.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the encoded string of bits exceeds this decoder's limits.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_MALLOC' if malloc fails.
 * If successful, '*witness' is set to the decoded bitstring and 0 is returned.
 *
 * Precondition: NULL != witness;
 *
 * Postcondition: if 'result == 0' and '0 < witness->len' then
 *                  'unsigned char witness->arr[(witness->len + witness->offset - 1) / CHAR_BIT + 1] and
 *                  (*witness) represents a some bitstring;
 *                if 'result < 0' or 'wintess->len == 0' then witness->arr == NULL;
 */
int32_t decodeMallocWitnessData(bitstring* witness, bit_stream* stream);

#endif
