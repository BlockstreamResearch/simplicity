/* This module provides functions for deserializing Simplicity's bit-wise prefix coding. */
#ifndef DESERIALIZE_H
#define DESERIALIZE_H

#include <stdint.h>
#include <stdio.h>

#define ERR_BITSTREAM_EOF (-1)
#define ERR_DATA_OUT_OF_RANGE (-2)

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

#endif
