#ifndef SIMPLICITY_RSORT_H
#define SIMPLICITY_RSORT_H

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include "sha256.h"

_Static_assert(UCHAR_MAX < SIZE_MAX, "UCHAR_MAX >= SIZE_MAX");
#define CHAR_COUNT ((size_t)1 << CHAR_BIT)

/* Internal function used by 'hasDuplicates'.  Do not call directly. */
const sha256_midstate* rsort(size_t* scratch, const sha256_midstate** a, size_t len, size_t level);

/* Searches for duplicates in an array of pointers to 'sha256_midstate's.
 * If 'true' is returned, '*duplicates' is set according to whether duplicate 'sha256_midstate' values were found.
 * If 'true' is returned, the array is also wiped, with all pointers set to NULL.
 * If malloc fails, false is returned and '*duplicates' and the array are unchanged.
 *
 * Precondition: NULL != duplicates;
 *               For all 0 <= i < len, NULL != a[i];
 * Postcondition: If 'true' is returned then for all 0 <= i < len, NULL == a[i];
 */
static inline bool hasDuplicates(bool* duplicates, const sha256_midstate** a, size_t len) {
  _Static_assert(sizeof((*a)->s) * CHAR_BIT == 256, "sha256_midstate.s has unnamed padding");
  _Static_assert(sizeof((*a)->s) < SIZE_MAX / CHAR_COUNT, "CHAR_BIT is way too large");
  _Static_assert((sizeof((*a)->s) + 1) * CHAR_COUNT <= SIZE_MAX/sizeof(size_t), "sizeof(size_t) is way too large");
  size_t * scratch = malloc((sizeof((*a)->s) + 1) * CHAR_COUNT * sizeof(size_t));

  if (scratch) {
    *duplicates = rsort(scratch, a, len, sizeof((*a)->s));

    /* Censor the array because its current order is implemenation defined. */
    while (len) { a[--len] = NULL; }
  }

  free(scratch);
  return scratch;
}

#endif
