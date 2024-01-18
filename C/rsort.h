#ifndef SIMPLICITY_RSORT_H
#define SIMPLICITY_RSORT_H

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include "limitations.h"
#include "sha256.h"
#include "simplicity_assert.h"

_Static_assert(UCHAR_MAX < SIZE_MAX, "UCHAR_MAX >= SIZE_MAX");
#define CHAR_COUNT ((size_t)1 << CHAR_BIT)

/* Internal function used by 'hasDuplicates'.  Do not call directly. */
const sha256_midstate* rsort(const sha256_midstate** a, size_t len, uint32_t* stack);

/* Searches for duplicates in an array of 'sha256_midstate's.
 * If malloc fails, returns -1.
 * If no duplicates are found, returns 0.
 * If duplicates are found, returns a positive value.
 *
 * Precondition: const sha256_midstate a[len];
 *               len <= DAG_LEN_MAX;
 */
static inline int hasDuplicates(const sha256_midstate* a, uint_fast32_t len) {
  if (len < 2) return 0;
  static_assert(sizeof(a->s) * CHAR_BIT == 256, "sha256_midstate.s has unnamed padding.");
  static_assert(DAG_LEN_MAX <= UINT32_MAX, "DAG_LEN_MAX does not fit in uint32_t.");
  static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(const sha256_midstate*), "perm array too large.");
  simplicity_assert(len <= SIZE_MAX / sizeof(const sha256_midstate*));
  const sha256_midstate **perm = malloc(len * sizeof(const sha256_midstate*));
  uint32_t *stack = malloc(((CHAR_COUNT - 1)*(sizeof((*perm)->s)) + 1) * sizeof(uint32_t));
  int result = perm && stack ? 0 : -1;

  if (0 <= result) {
    for (uint_fast32_t i = 0; i < len; ++i) {
      perm[i] = a + i;
    }

    result = NULL != rsort(perm, len, stack);
  }

  free(perm);
  free(stack);
  return result;
}

#endif
