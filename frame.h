/* This module provides functions writing initial data to and reading results from the frame used during evaluation
 * of Simplicity expressions.
 * These helper functions are also used for marshaling data to and from jets.
 */
#ifndef FRAME_H
#define FRAME_H

#include <assert.h>
#include <stdbool.h>
#include "uword.h"

/* A Bit Machine frame contains an '.edge' pointer to a slice of an array of UWORDs to hold the frame's cells.
 * The '.offset' is used to represent the cursors position.
 * For a read frame, the '.edge' points to one-past-the-end of the slice of the UWORDs array for the frame's cells,
 * and the '.offset' value is equal to the frame's cursor position plus the amount of padding used in the frame.
 * For a write frame, the '.edge' points to the beginning of the slice of the UWORDs array for the frame's cells,
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
 * The function returns the same value as bit.  This facilitates using 'writeBit' within an 'if' statement
 *
 *     if (writeBit(frame, bit)) { ... } else { ... }
 *
 * so that one can both decide conditions based on a Boolean value while at the same time writing to the frame the choice made.
 *
 * Precondition: '*frame' is a valid write frame for 1 more cell.
 */
static inline bool writeBit(frameItem* frame, bool bit) {
  assert(0 < frame->offset);
  frame->offset--;
  UWORD* dst_ptr = frame->edge + frame->offset / UWORD_BIT;
  if (bit) {
    *dst_ptr |= (UWORD)((UWORD)1 << (frame->offset % UWORD_BIT));
  } else {
    *dst_ptr = LSBclear(*dst_ptr, frame->offset % UWORD_BIT + 1);
  }
  return bit;
}

/* Given a write frame, advance the cursor by 'n' cells.
 *
 * Precondition: '*frame' is a valid write frame for 'n' more cells.
 */
static inline void skipBits(frameItem* frame, size_t n) {
  assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a read frame, the 'readN' function returns the value of the 'N' cells after the cursor and
 * advances the frame's cursor by 'N'.
 * The cell values are returned with the first cell in the MSB of the result and the last cell in the LSB of the result.
 *
 * Precondition: '*frame' is a valid read frame for 'N' more cells.
 */
uint_fast8_t read8(frameItem* frame);
uint_fast16_t read16(frameItem* frame);
uint_fast32_t read32(frameItem* frame);
uint_fast64_t read64(frameItem* frame);

/* Given a write frame, the 'writeN' function sets the value of the 'N' cells after the cursor and
 * advances the frame's cursor by 'N'.
 * The first cell is set to the value of the MSB of 'x' and the last cell is set to the LSB of 'x'.
 * Cells in front of the cursor's final position may be overwritten.
 *
 * Precondition: '*frame' is a valid write frame for 'N' more cells.
 */
void write8(frameItem* frame, uint_fast8_t x);
void write16(frameItem* frame, uint_fast16_t x);
void write32(frameItem* frame, uint_fast32_t x);
void write64(frameItem* frame, uint_fast64_t x);

static inline void read32s(uint32_t* x, size_t n, frameItem* frame) {
  for(; n; --n) *(x++) = (uint32_t)read32(frame);
}

static inline void write32s(frameItem* frame, const uint32_t* x, size_t n) {
  for(; n; --n) write32(frame, *(x++));
}
#endif
