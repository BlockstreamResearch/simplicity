#ifndef SIMPLICITY_RSORT_H
#define SIMPLICITY_RSORT_H

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include "limitations.h"
#include "sha256.h"

/* Searches for duplicates in an array of 'sha256_midstate's.
 * If malloc fails, returns -1.
 * If no duplicates are found, returns 0.
 * If duplicates are found, returns a positive value.
 *
 * Precondition: const sha256_midstate a[len];
 *               len <= DAG_LEN_MAX;
 */
int hasDuplicates(const sha256_midstate* a, uint_fast32_t len);

#endif
