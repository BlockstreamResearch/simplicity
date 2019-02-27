#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include "dag.h"
#include "deserialize.h"
#include "eval.h"
#include "typeInference.h"
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

static void test_hashBlock(void) {
  /* 'expected' is the expected CMR for the 'hashBlock' Simplicity expression. */
  const uint32_t expectedCMR[8] =
    { 0xe26d71c3ul, 0x18e61d3aul, 0x9b31a9cdul, 0x8bee8d4dul
    , 0x3ab0ab65ul, 0x6e7759f0ul, 0xaa10d1ddul, 0x089c8582ul
    };
  const uint32_t expectedWMR[8] =
    { 0xeeae47e2ul, 0xf7876c3bul, 0x9cbcd404ul, 0xa338b089ul
    , 0xfdeadf1bul, 0x9bb382ecul, 0x6e69719dul, 0x31baec9aul
    };
  dag_node* dag = NULL;
  combinator_counters census;
  int32_t len;
  {
    FILE* file = fmemopen_rb(hashBlock, sizeof_hashBlock);
    bit_stream stream = initializeBitStream(file);
    len = decodeMallocDag(&dag, &census, &stream);
    fclose(file);
  }
  if (!dag) {
    failures++;
    printf("Error parsing dag: %d\n", len);
  } else {
    successes++;

    analyses analysis[len];
    computeCommitmentMerkleRoot(analysis, dag, (size_t)len);
    if (0 == memcmp(expectedCMR, analysis[len-1].commitmentMerkleRoot.s, sizeof(uint32_t[8]))) {
      successes++;
    } else {
      failures++;
      printf("Unexpected CMR of hashblock\n");
    }

    type* type_dag = mallocTypeInference(dag, (size_t)len, &census);
    if (!type_dag) {
      failures++;
      printf("Unexpected failure of type inference for hashblock\n");
    } else {
      computeWitnessMerkleRoot(analysis, dag, type_dag, (size_t)len);
      if (0 == memcmp(expectedWMR, analysis[len-1].witnessMerkleRoot.s, sizeof(uint32_t[8]))) {
        successes++;
      } else {
        failures++;
        printf("Unexpected WMR of hashblock\n");
      }

      _Static_assert(UWORD_BIT - 1 <= SIZE_MAX - (256+512), "UWORD_BIT is far too large.");
      UWORD output[roundUWord(256)];
      UWORD input[roundUWord(256+512)];
      { frameItem frame = initWriteFrame(256+512, &input[roundUWord(256+512)]);
        /* Set SHA-256's initial value. */
        write256(&frame, (sha256_midstate){
          .s = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 }
        });
        /* Set the block to be compressed to "abc" with padding. */
        write256(&frame, (sha256_midstate){ .s = { 0x61626380 } });
        write256(&frame, (sha256_midstate){ .s = { [7] = 0x18 } });
      }
      computeEvalTCOBounds(analysis, dag, type_dag, (size_t)len);
      if (evalTCOExpression(output, 256, input, 256+512, analysis, dag, type_dag, (size_t)len)) {
        /* The expected result is the value 'SHA256("abc")'. */
        const uint32_t expectedHash[8] = { 0xba7816bful, 0x8f01cfeaul, 0x414140deul, 0x5dae2223ul
                                         , 0xb00361a3ul, 0x96177a9cul, 0xb410ff61ul, 0xf20015adul };
        frameItem frame = initReadFrame(256, &output[0]);
        sha256_midstate result = read256(&frame);
        if (0 == memcmp(expectedHash, result.s, sizeof(uint32_t[8]))) {
          successes++;
        } else {
          failures++;
          printf("Unexpected output of hashblock computation.\n");
        }
      } else {
        failures++;
        printf("Unexpected failure of hashblock evaluation\n");
      }

      free(type_dag);
    }
  }
  free(dag);
}

static void test_occursCheck(void) {
  /* The untyped Simplicity term (case (drop iden) iden) ought to cause an occurs check failure. */
  const unsigned char buf[] = { 0xc1, 0x07, 0x20, 0x30 };
  dag_node* dag = NULL;
  combinator_counters census = {0};
  int32_t len;
  {
    FILE* file = fmemopen_rb(buf, sizeof(buf));
    bit_stream stream = initializeBitStream(file);
    len = decodeMallocDag(&dag, &census, &stream);
    fclose(file);
  }
  if (!dag) {
    printf("Error parsing dag: %d\n", len);
  } else {
    type* type_dag = mallocTypeInference(dag, (size_t)len, &census);
    if (!type_dag) {
      successes++;
    } else {
      printf("Unexpected occurs check success\n");
      failures++;
    }
    free(type_dag);
  }
  free(dag);
}

int main(void) {
  test_decodeUptoMaxInt();
  test_hashBlock();
  test_occursCheck();

  printf("Successes: %d\n", successes);
  printf("Failures: %d\n", failures);
  return (0 == failures) ? EXIT_SUCCESS : EXIT_FAILURE;
}
