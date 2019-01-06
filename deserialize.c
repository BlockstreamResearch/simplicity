#include "deserialize.h"

#include <limits.h>
#include <stdlib.h>

/* Ensure a non-zero amount of bits are 'available'.
 * If no more bits are available in the 'stream', returns 'ERR_BISTREAM_EOF'.
 * Returns 0 if successful.
 *
 * Precondition: NULL != stream
 */
static int32_t ensureBuffer(bit_stream* stream) {
  if (stream->available <= 0) {
    int ch = fgetc(stream->file);
    if (ch < 0) return ERR_BITSTREAM_EOF;
    stream->byte = ch;
    stream->available = CHAR_BIT;
  }
  return 0;
}

/* Fetches up to 31 bits from 'stream' as the 'n' least significant bits of return value.
 * The 'n' bits are set from the MSB to the LSB.
 * Returns 'ERR_BITSTREAM_EOF' if not enough bits are available.
 *
 * Precondition: 0 <= n < 32
 *               NULL != stream
 */
static int32_t getNBits(int n, bit_stream* stream) {
  if (0 < n) {
    int32_t err = ensureBuffer(stream);
    if (err < 0) return err;
  } else {
    return 0;
  }

  int32_t result = 0;
  while (stream->available < n) {
    n -= stream->available;
    result |= (stream->byte & (((uint32_t)1 << stream->available) - 1)) << n;
    stream->available = 0;
    int32_t err = ensureBuffer(stream);
    if (err < 0) return err;
  }
  stream->available -= n;
  result |= (stream->byte >> stream->available) & (((uint32_t)1 << n) - 1);
  return result;
}

/* Returns one bit from 'stream', 0 or 1.
 * Returns 'ERR_BITSTREAM_EOF' if no bits are available.
 *
 * Precondition: NULL != stream
 */
static int32_t getBit(bit_stream* stream) {
  return getNBits(1, stream);
}

/* Fetches 'len' bytes from 'stream' into 'result'.
 * The bits in each byte are set from the MSB to the LSB and the bytes of 'result' are set from 0 upto 'len'.
 * Returns 'ERR_BITSTREAM_EOF' if not enough bits are available ('result' may be modified).
 * Returns 0 if successful.
 *
 * Precondition: uint8_t result[len];
 *               NULL != stream
 */
static int32_t getByteArray(uint8_t* result, const size_t len, bit_stream* stream) {
  for (size_t i = 0; i < len; ++i) {
    int32_t byte = getNBits(8, stream);
    if (byte < 0) return byte;
    result[i] = byte;
  }
  return 0;
}

/* Fetches a 256-bit hash value from 'stream' into 'result'.
 * Returns 'ERR_BITSTREAM_EOF' if not enough bits are available ('result' may be modified).
 * Returns 0 if successful.
 *
 * Precondition: uint8_t result[32];
 *               NULL != stream
 */
static int32_t getHash(uint8_t* result, bit_stream* stream) {
  return getByteArray(result, 32, stream);
}

/* Decode an encoded bitstring up to length 1.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaing bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto1Bit(int32_t* result, bit_stream* stream) {
  *result = getBit(stream);
  if (*result <= 0) return *result;

  *result = getBit(stream);
  if (*result < 0) return *result;
  if (0 != *result) return ERR_DATA_OUT_OF_RANGE;

  *result = getBit(stream);
  if (*result < 0) return *result;
  return 1;
}

/* Decode an encoded number between 1 and 3 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto3(bit_stream* stream) {
  int32_t result;
  int32_t len = decodeUpto1Bit(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded bitstring up to length 3.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaing bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto3Bits(int32_t* result, bit_stream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;

  *result = 0;
  if (0 == bit) {
    return 0;
  } else {
    int32_t n = decodeUpto3(stream);
    if (0 <= n) {
      *result = getNBits(n, stream);
      if (*result < 0) return *result;
    }
    return n;
  }
}

/* Decode an encoded number between 1 and 15 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto15(bit_stream* stream) {
  int32_t result;
  int32_t len = decodeUpto3Bits(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded bitstring up to length 15.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaing bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto15Bits(int32_t* result, bit_stream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;

  *result = 0;
  if (0 == bit) {
    return 0;
  } else {
    int32_t n = decodeUpto15(stream);
    if (0 <= n) {
      *result = getNBits(n, stream);
      if (*result < 0) return *result;
    }
    return n;
  }
}

/* Decode an encoded number between 1 and 65535 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto65535(bit_stream* stream) {
  int32_t result;
  int32_t len = decodeUpto15Bits(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded number between 1 and 2^31 - 1 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is retured.
 *
 * Precondition: NULL != stream
 */
int32_t decodeUptoMaxInt(bit_stream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  if (0 == bit) {
    return 1;
  } else {
    int32_t n = decodeUpto65535(stream);
    if (n < 0) return n;
    if (30 < n) return ERR_DATA_OUT_OF_RANGE;
    {
      int32_t result = getNBits(n, stream);
      if (result < 0) return result;
      return ((1 << n) | result);
    }
  }
}

/* Decode a single node of a Simplicity dag from 'stream' into 'dag'['i'].
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the node's child isn't a reference to one of the preceeding nodes.
 * Returns 'ERR_FAIL_CODE' if the encoding of a fail expression is encountered (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * :TODO: Decoding of witness, primitives and jets are not implemented yet.
 *
 * Precondition: dag_node dag[i + 1];
 *               i < 2^31 - 1
 *               NULL != stream
 */
static int32_t decodeNode(dag_node* dag, size_t i, bit_stream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  if (0 == bit) {
    int32_t code = getNBits(2, stream);
    if (code < 0) return code;
    int32_t subcode = getNBits(code < 3 ? 2 : 1, stream);
    if (subcode < 0) return subcode;
    for (int32_t j = 0; j < 2 - code; ++j) {
      int32_t ix = decodeUptoMaxInt(stream);
      if (ix < 0) return ix;
      if (i < ix) return ERR_DATA_OUT_OF_RANGE;
      dag[i].child[j] = i - ix;
    }
    switch (code) {
     case 0:
      switch (subcode) {
       case 0: dag[i].tag = COMP; return 0;
       case 1: dag[i].tag = CASE; return 0;
       case 2: dag[i].tag = PAIR; return 0;
       case 3: dag[i].tag = DISCONNECT; return 0;
      }
     case 1:
      switch (subcode) {
       case 0: dag[i].tag = INJL; return 0;
       case 1: dag[i].tag = INJR; return 0;
       case 2: dag[i].tag = TAKE; return 0;
       case 3: dag[i].tag = DROP; return 0;
      }
     case 2:
      switch (subcode) {
       case 0: dag[i].tag = IDEN; return 0;
       case 1: dag[i].tag = UNIT; return 0;
       case 2: return ERR_FAIL_CODE;
       case 3: return ERR_STOP_CODE;
      }
     case 3:
      switch (subcode) {
       case 0:
        dag[i].tag = HIDDEN;
        return getHash(dag[i].hash, stream);
       case 1:
        dag[i].tag = WITNESS;
        // TODO: parse witness data
        fprintf(stderr, "witness nodes not yet implemented\n");
        exit(EXIT_FAILURE);
      }
    }
    return ERR_IMPOSSIBLE;
  } else {
    // TODO: Decode primitives and jets
    fprintf(stderr, "primitives and jets nodes not yet implemented\n");
    exit(EXIT_FAILURE);
  }
}

/* Decode a Simplicity DAG consisting of 'len' nodes from 'stream' into 'dag'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceeding nodes.
 * Returns 'ERR_FAIL_CODE' if the encoding of a fail expression is encountered (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: dag_node dag[len];
 *               len < 2^31
 *               NULL != stream
 */
static int32_t decodeDag(dag_node* dag, const size_t len, bit_stream* stream) {
  for (size_t i = 0; i < len; ++i) {
    int32_t err = decodeNode(dag, i, stream);
    if (err < 0) return err;
  }
  return 0;
}

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
int32_t decodeMallocDag(dag_node** dag, bit_stream* stream) {
  *dag = NULL;
  int32_t dagLen = decodeUptoMaxInt(stream);
  if (dagLen <= 0) return dagLen;
  /* :TODO: a consensus parameter limiting the maximum length of a DAG needs to be enforeced here */
  if (PTRDIFF_MAX / sizeof(dag_node) < dagLen) return ERR_DATA_OUT_OF_RANGE;
  *dag = malloc(sizeof(dag_node[dagLen]));
  if (!*dag) return 0;

  int32_t err = decodeDag(*dag, dagLen, stream);
  if (err < 0) {
    free(*dag);
    *dag = NULL;
    return err;
  } else {
    return dagLen;
  }
}
