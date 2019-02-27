/* This module provides functions for evaluating Simplicity programs and expressions.
 * Helper functions are provided for writing initial data to and reading results from the evaluation of Simplicity expressions.
 * These helper functions are also used for marshalling data to and from jets.
 */
#ifndef EVAL_H
#define EVAL_H

#include <assert.h>
#include <stdbool.h>
#include <limits.h>
#include "dag.h"
#include "uword.h"

/* A Bit Machine frame contains an '.edge' pointer to a slice of an array of UWORDs to hold the frame's cells.
 * The '.offset' is used to represent the cursors position.
 * For a read frame, the '.edge' points to one-past-the-end of the slice of the UWORDs array for the frame's cells,
 * and the '.offset' value is equal to the frame's cursor position plus the amount of padding used in the frame.
 * For a write frame, the '.edge' points to the begining of the slice of the UWORDs array for the frame's cells,
 * and the '.offset' value is equal to the total number of cells minus the frame's cursor position.
 */
typedef struct frameItem {
  UWORD* edge;
  size_t offset;
} frameItem;

/* Initialize a new read frame.
 * 'n' is the number of cells for the read frame.
 * 'from' is a pointer to the beginning of the new slice for the array of UWORDS to hold the frame's cells.
 *
 * Precondition: n + UWORD_BIT - 1 <= SIZE_MAX;
 *               UWORD from[roundUWord(n)];
 */
static inline frameItem initReadFrame(size_t n, UWORD* from) {
/* 'UWORD_BIT - 1 - (n + (UWORD_BIT - 1)) % UWORD_BIT' equals the numer of padding bits in a frame of size 'n'. */
  return (frameItem){ .edge = from + roundUWord(n), .offset = UWORD_BIT - 1 - (n + (UWORD_BIT - 1)) % UWORD_BIT };
}

/* Initialize a new write frame.
 * 'n' is the number of cells for the write frame.
 * 'from' is a pointer to the one-past-the-end of the new slice for the array of UWORDS to hold the frame's cells.
 *
 * Precondition: n + UWORD_BIT - 1 <= SIZE_MAX
 *               UWORD (from - roundUWord(n))[roundUWord(n)];
 */
static inline frameItem initWriteFrame(size_t n, UWORD* from) {
  return (frameItem){ .edge = from - roundUWord(n), .offset = n };
}

/* Given a read frame, return the value of the cell at the cursor.
 *
 * Precondition: '*frame' is a valid read frame for 1 more cell.
 */
static inline bool peekBit(const frameItem* frame) {
  return 1 & (*(frame->edge - 1 - frame->offset / UWORD_BIT) >> (UWORD_BIT - (frame->offset % UWORD_BIT) - 1));
}

/* Given a read frame, return the value of the cell at the cursor and advance the cursor by one cell.
 *
 * Precondition: '*frame' is a valid read frame for 1 more cell.
 */
static inline bool readBit(frameItem* frame) {
  bool result = peekBit(frame);
  frame->offset++;
  return result;
}

/* Given a write frame, set its cursor's cell to 'bit' and advance the cursor by one cell.
 * Cells in front of the cursor's final position may be overwritten.
 *
 * Precondition: '*frame' is a valid write frame for 1 more cell.
 */
static inline void writeBit(frameItem* frame, bool bit) {
  assert(0 < frame->offset);
  frame->offset--;
  UWORD* dst_ptr = frame->edge + frame->offset / UWORD_BIT;
  if (bit) {
    *dst_ptr |= (UWORD)((UWORD)1 << (frame->offset % UWORD_BIT));
  } else {
    *dst_ptr = LSBclear(*dst_ptr, frame->offset % UWORD_BIT + 1);
  }
}

/* Given a read frame, return the value of the 32 cells after the cursor and advance the frame's cursor by 32.
 * The cell values are returned with the first cell in the MSB of the result and the last cell in the LSB of the result.
 *
 * Precondition: '*frame' is a valid read frame for 32 more cells.
 */
uint32_t read32(frameItem* frame);

/* Given a write frame, set the value of the 32 cells after the cursor and advance the frame's cursor by 32.
 * The first cell is set to the value of the MSB of 'x' and the last cell is set to the LSB of 'x'.
 * Cells in front of the cursor's final position may be overwritten.
 *
 * Precondition: '*frame' is a valid write frame for 32 more cells.
 */
void write32(frameItem* frame, uint32_t x);

/* Given a read frame, return the value of the 256 cells after the cursor and advance the frame's cursor by 256.
 * The cell values are returned with the first cell in the MSB of the first element of the result's '.s' array,
 * and the last cell in the LSB of the last element of the result's '.s' array.
 *
 * Precondition: '*frame' is a valid read frame for 256 more cells.
 */
static inline sha256_midstate read256(frameItem* frame) {
  sha256_midstate result;
  result.s[0] = read32(frame);
  result.s[1] = read32(frame);
  result.s[2] = read32(frame);
  result.s[3] = read32(frame);
  result.s[4] = read32(frame);
  result.s[5] = read32(frame);
  result.s[6] = read32(frame);
  result.s[7] = read32(frame);
  return result;
}

/* Given a write frame, set the value of the 256 cells after the cursor and advance the frame's cursor by 256.
 * The first cell is set to the  MSB of the first element of 'x.s',
 * and the last cell is set to the LSB of the last element of 'x.s'.
 * Cells in front of the cursor's final position may be overwritten.
 *
 * Precondition: '*frame' is a valid write frame for 256 more cells.
 */
static inline void write256(frameItem* frame, sha256_midstate x) {
  write32(frame, x.s[0]);
  write32(frame, x.s[1]);
  write32(frame, x.s[2]);
  write32(frame, x.s[3]);
  write32(frame, x.s[4]);
  write32(frame, x.s[5]);
  write32(frame, x.s[6]);
  write32(frame, x.s[7]);
}

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[roundUWord(inputSize)]'.
 *
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, return 'false'.
 * If malloc fails, return 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, return 'false'.
 * Otherwise return 'true'.
 *
 * If the function returns 'true' and 'NULL != output', copy the final active write frame's data to 'output[roundWord(outputSize)]'.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               outputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               inputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               output == NULL or UWORD output[roundUWord(outputSize)];
 *               input == NULL or UWORD input[roundUWord(inputSize)];
 *               analyses analysis[len];
 *               'max(analysis[len-1].extraCellsBoundTCO[0], analysis[len-1].extraCellsBoundTCO[1]) == SIZE_MAX'.
 *                 or 'analysis[len-1].extraCellsBoundTCO' characterizes the number of UWORDs needed
 *                   for the frames allocated during evaluation of 'dag';
 *               analysis[len-1].extraStackBoundTCO[0] bounds the the number of stack frames needed during execution of 'dag';
 */
bool evalTCOExpression( UWORD* output, size_t outputSize, const UWORD* input, size_t inputSize
                      , const analyses* analysis, const dag_node* dag, const type* type_dag, size_t len
                      );

/* Run the Bit Machine on the well-typed Simplicity program 'dag[len]'.
 *
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, return 'false'.
 * If malloc fails, return 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, return 'false'.
 * Otherwise return 'true'.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type 1 |- 1;
 *               analyses analysis[len];
 *               'max(analysis[len-1].extraCellsBoundTCO[0], analysis[len-1].extraCellsBoundTCO[1]) == SIZE_MAX'.
 *                 or 'analysis[len-1].extraCellsBoundTCO' characterizes the number of UWORDs needed
 *                   for the frames allocated during evaluation of 'dag';
 *               analysis[len-1].extraStackBoundTCO[0] bounds the the number of stack frames needed during execution of 'dag';
 */
static inline bool evalTCOProgram(const analyses* analysis, const dag_node* dag, const type* type_dag, size_t len) {
  return evalTCOExpression( NULL, 0, NULL, 0, analysis, dag, type_dag, len);
}
#endif
