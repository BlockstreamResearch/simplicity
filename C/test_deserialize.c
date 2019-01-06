#include <limits.h>
#include <stdlib.h>
#include "dag.h"
#include "deserialize.h"
#include "hashBlock.h"

_Static_assert(CHAR_BIT == 8, "Buffers passed to fmemopen persume 8 bit chars");

static int successes = 0;
static int failures = 0;

static void test_decodeUptoMaxInt() {
  const unsigned char buf[] =
  { 0x4b, 0x86, 0x39, 0xe8, 0xdf, 0xc0, 0x38, 0x0f, 0x7f, 0xff, 0xff, 0x00
  , 0x00, 0x00, 0xf0, 0xe0, 0x00, 0x00, 0x00, 0x3c, 0x3b, 0xff, 0xff, 0xff
  , 0xff, 0x0f, 0x00, 0x00, 0x00, 0x00
  };
  const int32_t expected[] =
  { 1, 2, 3, 4, 5, 7, 8, 15, 16, 17
  , 0xffff, 0x10000, 0x40000000, 0x7fffffff, ERR_DATA_OUT_OF_RANGE
  };

  FILE* file = fmemopen((void *)buf, sizeof(buf), "rb"); /* Casting away const. */
  if (!file) {
    fprintf(stderr, "fmemopen failed (" __FILE__ ", %d).", __LINE__);
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

static void test_decodeMallocDag_computeCommitmentMerkleRoot() {
  /* 'expected' is the expected CMR for the 'hashBlock' Simplicity expression. */
  const uint8_t expected[32] =
  { 0xe2, 0x6d, 0x71, 0xc3, 0x18, 0xe6, 0x1d, 0x3a, 0x9b, 0x31, 0xa9, 0xcd, 0x8b, 0xee, 0x8d, 0x4d
  , 0x3a, 0xb0, 0xab, 0x65, 0x6e, 0x77, 0x59, 0xf0, 0xaa, 0x10, 0xd1, 0xdd, 0x08, 0x9c, 0x85, 0x82
  };
  dag_node* dag = NULL;
  int32_t len;
  {
    FILE* file = fmemopen((void *)hashBlock, sizeof_hashBlock, "rb"); /* Casting away const. */
    if (!file) {
      fprintf(stderr, "fmemopen failed (" __FILE__ ", %d).", __LINE__);
      exit(EXIT_FAILURE);
    }

    bit_stream stream = initializeBitStream(file);
    len = decodeMallocDag(&dag, &stream);
    fclose(file);
  }
  if (len <= 0) {
    printf("Error parsing dag: %d\n", len);
  } else {
    analyses analysis[len];
    computeCommitmentMerkleRoot(analysis, dag, len);
    size_t i;
    for (i = 0; i < 32; i++) {
      if (expected[i] != analysis[len-1].commitmentMerkleRoot[i]) {
        printf("Unexpected CMR of hashblock\n");
        break;
      }
    }
    if (32 == i) {
      successes++;
    } else {
      failures++;
    }
  }
  free(dag);
}

int main() {
  test_decodeUptoMaxInt();
  test_decodeMallocDag_computeCommitmentMerkleRoot();

  printf("Successes: %d\n", successes);
  printf("Failures: %d\n", failures);
  return (0 == failures) ? EXIT_SUCCESS : EXIT_FAILURE;
}
