/* This module defines some constants used for error codes when processing Simplicity.
 * Errors can either indicate a transient or a permanent failure.
 */
#ifndef SIMPLICITY_ERRORCODES_H
#define SIMPLICITY_ERRORCODES_H

#include <stdbool.h>

/* By convention, odd error codes are transient failures (i.e. out of memory)
 * while even error codes are permanent failures (i.e. unexpected end of file or parsing error, etc.)
 */
typedef enum {
  SIMPLICITY_NO_ERROR = 0,
  SIMPLICITY_ERR_MALLOC = -1,
  SIMPLICITY_ERR_BITSTREAM_EOF = -2,
  SIMPLICITY_ERR_NOT_YET_IMPLEMENTED = -3,
  SIMPLICITY_ERR_DATA_OUT_OF_RANGE = -4,
  SIMPLICITY_ERR_DATA_OUT_OF_ORDER = -6,
  SIMPLICITY_ERR_FAIL_CODE = -8,
  SIMPLICITY_ERR_STOP_CODE = -10,
  SIMPLICITY_ERR_HIDDEN = -12,
  SIMPLICITY_ERR_BITSTREAM_UNUSED_BYTES = -14,
  SIMPLICITY_ERR_BITSTREAM_UNUSED_BITS = -16,
  SIMPLICITY_ERR_TYPE_INFERENCE_UNIFICATION = -18,
  SIMPLICITY_ERR_TYPE_INFERENCE_OCCURS_CHECK = -20,
  SIMPLICITY_ERR_TYPE_INFERENCE_NOT_PROGRAM = -22,
  SIMPLICITY_ERR_WITNESS_EOF = -24,
  SIMPLICITY_ERR_WITNESS_UNUSED_BITS = -26,
  SIMPLICITY_ERR_UNSHARED_SUBEXPRESSION = -28,
  SIMPLICITY_ERR_CMR = -30,
  SIMPLICITY_ERR_AMR = -32,
  SIMPLICITY_ERR_EXEC_BUDGET = -34,
  SIMPLICITY_ERR_EXEC_MEMORY = -36,
  SIMPLICITY_ERR_EXEC_JET = -38,
  SIMPLICITY_ERR_EXEC_ASSERT = -40,
  SIMPLICITY_ERR_ANTIDOS = -42,
} simplicity_err;

/* Check if failure is permanent (or success which is always permanent). */
static inline bool IS_PERMANENT(simplicity_err err) {
  return !(err & 1);
}

/* Check if no failure. */
static inline bool IS_OK(simplicity_err err) {
  return SIMPLICITY_NO_ERROR == err;
}

#endif
