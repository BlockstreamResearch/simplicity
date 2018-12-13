#include <limits.h>
#include <stdlib.h>
#include "deserialize.h"

_Static_assert(CHAR_BIT == 8, "Buffers passed to fmemopen persume 8 bit chars");

int main() {
  int successes = 0;
  int failures = 0;
  { const unsigned char buf[] =
    { 0x4b, 0x86, 0x39, 0xe8, 0xdf, 0xc0, 0x38, 0x0f, 0x7f, 0xff
    , 0xff, 0x00, 0x00, 0x00, 0xf0, 0xe0, 0x00, 0x00, 0x00, 0x3c
    , 0x3b, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x00, 0x00, 0x00, 0x00
    };
    const int32_t expected[] =
    { 1, 2, 3, 4, 5, 7, 8, 15, 16, 17
    , 0xffff, 0x10000, 0x40000000, 0x7fffffff, ERR_DATA_OUT_OF_RANGE
    };

    FILE* file = fmemopen((void *)buf, sizeof(buf), "rb"); /* Casting away const. */
    if (!file) {
      fprintf(stderr, "fmemopen failed");
      exit(EXIT_FAILURE);
    }

    bit_stream stream = initializeBitStream(file);
    for (size_t i = 0; i < sizeof(expected)/sizeof(expected[0]); ++i) {
      int32_t result = decodeUptoMaxInt(&stream);
      if (expected[i] == result) {
        successes++;
      } else {
        failures++;
        printf("Unexpected result during parsing.  Expected %d and received %d\n", expected[i], result);
      }
    }
    fclose(file);
  }
  printf("Successes: %d\n", successes);
  printf("Failures: %d\n", failures);
  return (0 == failures) ? EXIT_SUCCESS : EXIT_FAILURE;
}
