#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include "dag.h"
#include "deserialize.h"
#include "hashBlock.h"

_Static_assert(CHAR_BIT == 8, "Buffers passed to fmemopen persume 8 bit chars");

static FILE* fmemopen_rb(const void *buf, size_t size) {
  FILE* result = fmemopen((void *)(uintptr_t)buf, size, "rb"); /* Casting away const. */
  if (!result) {
    fprintf(stderr, "fmemopen failed.");
    exit(EXIT_FAILURE);
  }
  return result;
}

static int successes = 0;
static int failures = 0;

static void test_decodeUptoMaxInt(void) {
  const unsigned char buf[] =
  { 0x4b, 0x86, 0x39, 0xe8, 0xdf, 0xc0, 0x38, 0x0f, 0x7f, 0xff, 0xff, 0x00
  , 0x00, 0x00, 0xf0, 0xe0, 0x00, 0x00, 0x00, 0x3c, 0x3b, 0xff, 0xff, 0xff
  , 0xff, 0x0f, 0x00, 0x00, 0x00, 0x00
  };
  const int32_t expected[] =
  { 1, 2, 3, 4, 5, 7, 8, 15, 16, 17
  , 0xffff, 0x10000, 0x40000000, 0x7fffffff, ERR_DATA_OUT_OF_RANGE
  };

  FILE* file = fmemopen_rb(buf, sizeof(buf));
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

static void test_decodeMallocDag_computeCommitmentMerkleRoot(void) {
  /* 'expected' is the expected CMR for the 'hashBlock' Simplicity expression. */
  const uint32_t expected[8] =
    { 0xe26d71c3ul, 0x18e61d3aul, 0x9b31a9cdul, 0x8bee8d4dul
    , 0x3ab0ab65ul, 0x6e7759f0ul, 0xaa10d1ddul, 0x089c8582ul
    };
  dag_node* dag = NULL;
  int32_t len;
  {
    FILE* file = fmemopen_rb(hashBlock, sizeof_hashBlock);
    bit_stream stream = initializeBitStream(file);
    len = decodeMallocDag(&dag, &stream);
    fclose(file);
  }
  if (len <= 0) {
    printf("Error parsing dag: %d\n", len);
    failures++;
  } else {
    successes++;

    analyses analysis[len];
    computeCommitmentMerkleRoot(analysis, dag, (size_t)len);
    if (0 == memcmp(expected, analysis[len-1].commitmentMerkleRoot.s, sizeof(uint32_t[8]))) {
      successes++;
    } else {
      printf("Unexpected CMR of hashblock\n");
      failures++;
    }
  }
  free(dag);
}

int main(void) {
  test_decodeUptoMaxInt();
  test_decodeMallocDag_computeCommitmentMerkleRoot();

  printf("Successes: %d\n", successes);
  printf("Failures: %d\n", failures);
  return (0 == failures) ? EXIT_SUCCESS : EXIT_FAILURE;
}
