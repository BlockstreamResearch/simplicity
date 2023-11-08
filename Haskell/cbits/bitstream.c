#include "bitstream.h"

const size_t c_sizeof_bitstream = sizeof(bitstream);

void c_initializeBitstream(bitstream *result, const unsigned char* arr, size_t len) {
  *result = initializeBitstream(arr, len);
}
