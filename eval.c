#include "eval.h"

#include "bounded.h"

/* :TODO: remove these includes after witnesses are supported, etc. */
#include <stdio.h>
#include <stdlib.h>

/* We choose an unusual representation for frames of the Bit Machine.
 *
 * An 'n'-bit frame is stored in the array of 'UWORD's of length 'l' where 'l' is the least value such that 'n <= l * UWORD_BIT'.
 * Thus there may be extra "padding" bits in the array when 'n < l * UWORD_BIT'.
 *
 * We choose to store the frames bits in a sequence with the first bits in the last element of the array and
 * the last bits in the first element of the array.
 * Within a 'UWORD' array element, the bits of the frame are stored with the first bits in the most significant positions
 * and the last bits in the least significant positions.
 * We chooose to put padding bits entirely within the most significant bits of the last element of the array.
 *
 * Thus the last bit of the frame will always be the least significant bit of the first element of the array.
 * When there are no padding bits, the first bit of the frame will be the most significant bit of the last element of the array.
 * When there are padding bits, the first bit of the frame will occur at the most significant non-padding bit.
 *
 * More precisely, bit 'm' of an 'n'-bit frame (with '0 <= m < n') is the bit at position '1 << ((n-m-1) % UWORD_BIT)'
 * of the element of the array at index '(n-m-1 / UWORD_BIT)'.
 *
 * 0-bit frames are allowed, in which case the array will have length 0.
 *
 * Rationale:
 *
 * The Bit Machine's standard library of jets operates using a "big endian" representation of integers
 * from the Bit Machine's perspective.
 * It is often the case that we encounter types that are sums of various integers sizes.
 * For example, the Bitcoin primitive 'outputValue : TWO^32 |- ONE + TWO^64' has a target type
 * that is the sum of 64-bit integer (with a 0-bit integer).
 *
 * When a frame is generated from a type such as 'ONE + TWO^64' our representation places the tag for this type
 * by itself as the least significant bit of the last element of the frame's array (as long as 'UWORD_BIT' divides 64).
 * When this frame contains a value of the right-hand type, 'TWO^64', this value entirely fits perfectly within
 * the within the first elements of the array (again, as long as 'UWORD_BIT' divides 64).
 * Futhermore, if 'UWORD_BIT == 8', then this representation place this value of type 'TWO^64'
 * into the machine's memory in little endian byte order.
 *
 * All of the above means that when jets need to marshal values from the Bit Machine's representation
 * to the architecture's representation, it will often be the case that the data is already byte-aligned and
 * in the correct order for little endian processors.
 * When a jet marshals a architecture-sized word, and 'UWORD' is the architecture's native integer size, then
 * it will often be the case that the data is word-aligned (for both big and little endian processors).
 * Only the case when 'UWORD_BIT == 8' and architecture's processor is big-endian will the compiler need to emit
 * byte-swapping instructions.
 *
 * Nevertheless, our implmementation is independent of architecture and will function correctly on all architectures
 * for any value of UWORD_BIT.
 *
 * Note: while we do attempt make the fast path for marshalling values for jets common, when assigning discounts to jets
 * it is important to only consider the worst case, slow path, behaviour, as good byte or bit alignment is not guarenteed in
 * presence of oddly shaped pairs of values.
 */

/* The main memory used by the Bit Machine during execution is contained in a single allocation of an array of 'UWORD's
 * named 'cells'.
 * The read and write frames used by the Bit Machine during execution are slices of this single array allocation.
 * We represent the read frame and write frame stacks within 'cells' using a [gap buffer](https://en.wikipedia.org/wiki/Gap_buffer).
 * The frames of the read frame stack are assigned to the beginning of the cell array
 * with the active read frame occuring as the last of these frames.
 * The frames of the write frame stack are assigned to the end of the cell array
 * with the active write frame occuring as the first of these frames.
 * This leaves a (possibly empty) gap of unused UWORDs between the '.edge' of the active read frame
 * and the '.edge' of the active write frame.
 * This gap will shrink / grow / move during the execution of the Bit Machine.
 * Thus whether a particular UWORD from 'cells' belongs to some read frame or write frame will vary during the execution.
 * Static analysis determines a safe size that is acceptable for the 'cells' array.
 */

/* To keep track of the individual frames of the read frame and write frame stacks we another single allocation of
 * an array of 'frameItem's called 'frames'.
 * This 'frames' array is another instance of a [gap buffer](https://en.wikipedia.org/wiki/Gap_buffer).
 * The read frames are tracked by 'frameItem's occuring at the beginning of the 'frames' array
 * with the active read frame tracked the last of these 'frameItem's.
 * The write frames are tracked by 'frameItem's occuring at the end of the 'frames' array
 * with the active write frame tracked the first of these 'frameItem's.
 * This leaves a (possibly empty) gap of unused 'frameItem's between the item that tracks active read frame
 * and the item that tracks the active write frame.
 * This gap will shrink / grow / move during the execution of the Bit Machine.
 * Thus whether a particular 'frameItem' from 'frames' tracks a read frame or write frame will vary during the execution.
 * The 'frameItem' that tracks the active read frame is located at 'state.activeReadFrame'.
 * The 'frameItem' that tracks the active write frame is located at 'state.activeWriteFrame'.
 * There is always an active read frame and an active write frame, though these frames are initially of size 0
 * when evaluating Simplicity programs.
 * Static analysis determines a safe size that is acceptable for the 'frames' array.
 */

/* When a 'frameItem' tracks a read frame, its '.edge' field points to the UWORD from 'cell' that is
 * one-past-the-end of the 'cells' slice that makes up that frame.
 * The '.offset' value indirectly tracks the position of the read frame's cursor.
 * A cursor at the beginning of a read frame is denoted by an '.offset' value equal to that frame's padding.
 * When the frame has no padding, a cursor at the beginning of a read frame is denoted by an '.offset' of 0.
 * For each subsequent cursor position within the read frame, the '.offset' increments by one.
 * When the cursor is at (one-cell past) the end of the read frame, the '.offset' value will be equal to the total number of bits
 * allocated for the frame (including padding bits), which is necessarily some multiple of (UWORD_BIT).
 * We say "a read frame is valid for /n/ more cells" when '.edge - roundUWord(.offset + n)' points to a
 * 'UWORD[roundUWord(.offset + n)]' array of initialized values.
 * We say "a read frame is valid" if it is valid for 0 more cells.
 *
 * When a 'frameItem' tracks a write frame, its '.edge' field points the UWORD from 'cell' that is
 * the first element of the 'cells' slice that makes up that frame.
 * The '.offset' value indirectly tracks the position of the write frame's cursor.
 * A cursor at the beginning of a read frame is denoted by an '.offset' value equal to
 * that frame's number of bits (excluding padding).
 * For each subsequent cursor position within the write frame, the '.offset' decrements by one.
 * When the cursor is at (one-cell past) the end of the write frame, the '.offset' value will be equal to 0.
 * We say "a write frame is valid for /n/ more cells" when '.edge' points to an 'UWORD[roundUWord(.offset)]' array of
 * initialized values and 'n <= .offset'.
 * We say "a write frame is valid" if it is valid for 0 more cells.
 *
 * Notice that the interpretation of the fields of a 'frameItem' depends on whether the 'frameItem' is tracking a read frame or
 * a write frame.
 */

/* Given a read frame, advance its cursor by 'n' cells.
 *
 * Precondition: NULL != frame.
 */
static void forward(frameItem* frame, size_t n) {
  frame->offset += n;
}

/* Given a read frame, move its cursor backwards by 'n' cells.
 *
 * Precondition: n <= frame->offset
 */
static void backward(frameItem* frame, size_t n) {
  assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a write frame, advance its cursor by 'n' cells.
 *
 * Precondition: n <= frame->offset
 */
static void skip(frameItem* frame, size_t n) {
  assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a write frame and a read frame, copy 'n' cells from after the read frame's cursor to after the write frame's cursor,
 * and then advance the write frame's cursor by 'n'.
 * Cells in front of the '*dst's cursor's final position may be overwritten.
 *
 * Precondition: '*dst' is a valid write frame for 'n' more cells.
 *               '*src' is a valid read frame for 'n' more cells.
 */
/* :TODO: optimize this with memcopy. */
static void copyBits(frameItem* dst, const frameItem* src, size_t n) {
  frameItem src0 = *src;

  /* :TODO: Use static analysis to limit the number of iterations through this loop. */
  for(; n; --n) {
    writeBit(dst, peekBit(&src0));
    src0.offset++;
  }
}

/* Given a read frame, return the value of the 32 cells after the cursor and advance the frame's cursor by 32.
 * The cell values are returned with the first cell in the MSB of the result and the last cell in the LSB of the result.
 *
 * Precondition: '*frame' is a valid read frame for 32 more cells.
 */
/* :TODO: optimize this. */
uint32_t read32(frameItem* frame) {
  uint32_t result = 0;
  for (size_t i = 32; i; --i) {
    result |= (uint32_t)peekBit(frame) << (i - 1);
    frame->offset++;
  }
  return result;
}

/* Given a write frame, set the value of the 32 cells after the cursor and advance the frame's cursor by 32.
 * The first cell is set to the value of the MSB of 'x' and the last cell is set to the LSB of 'x'.
 * Cells in front of the cursor's final position may be overwritten.
 *
 * Precondition: '*frame' is a valid write frame for 32 more cells.
 */
/* :TODO: optimize this. */
void write32(frameItem* frame, uint32_t x) {
  for (size_t i = 32; i; --i) {
    writeBit(frame, 1 & (x >> (i - 1)));
  }
}

/* Our representation of the Bit Machine state consists of a gap buffer of 'frameItem's.
 * The gap buffer is allocated at 'frame'
 * The read frames of the gap buffer extends from the beginning of the buffer to '.activeReadFrame'.
 * The write frames extend from the end of the buffer down to '.activeWriteFrame'.
 */
typedef struct evalState {
  frameItem* activeReadFrame;
  frameItem* activeWriteFrame;
} evalState;

/* 'call' is an item is used to track the "call stack" of the Bit Machine during evaluation.
 * Each call stack frame holds the call's TCO state and where to return to after the call.
 */
typedef struct call {
  size_t return_to;
  union {
    bool tcoOn;
    bool bit; /* Scratch space used by the 'CASE' combinator. */
  };
} call;

/* Starting from the Bit Machine 'state',
 * run the machine with the TCO (off) program generated by the well-typed Simplicity expression 'dag[len]' of type 'A |- B'.
 * If an 'assertr' or 'assertl' combinator fails, return 'false', otherwise return 'true'.
 *
 * The 'state' of the Bit Machine is whatever the state is after the last successfully executed Bit Machine instruction.
 *
 * ** No heap allocations are allowed in 'runTCO' or any of its subroutines. **
 *
 * Precondition: The gap between 'state.activeReadFrame' and 'state.activeWriteFrame' is sufficent for execution of 'dag'
 *                 and the values are initalized;
 *               The gap between 'activeReadFrame(state)->edge' and 'activeWriteFrame(state)->edge'
 *                 is sufficent for execution of 'dag';
 *               '*activeReadFrame(state)' is a valid read frame for 'bitSize(A)' more cells.
 *               '*activeWriteFrame(state)' is a valid write frame for 'bitSize(B)' more cells.
 *               call stack[len];
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag'.
 */
static bool runTCO(evalState state, call* stack, const dag_node* dag, const type* type_dag, size_t len) {
/* The program counter, 'pc', is the current combinator being interpreted.  */
  size_t pc = len - 1;

/* 'stack' represents the interpreter's call stack.
 * However, the stack is not directly represented as an array.
 * Instead, the bottom of the call stack is located at 'stack[len - 1]' and the top of the call stack is located at 'stack[pc]'.
 * The intermetate call stack items are somewhere between 'pc' and 'len - 1'.
 * The each call stack item references the one below it through the 'stack[i].return_to' values.
 * The bottom of the stack's '.return_to' value is set to 'len' which is an out-of-bounds index.
 *
 * During CALLs, a new 'stack[i]' value is created where 'i' is index of the combinator being called,
 * and 'stack[i].return_to' is set to the current 'pc' value.
 * During TAIL_CALLs, 'stack[i].return_to' is instead set to the 'stack[pc].return_to' value.
 * During RETURNs, the 'pc' is set to the 'stack[pc].return_to' value.
 * TAIL_CALLs allows for faster returns within the interpreter (unrelated to Simplicity's TCO),
 * skipping over intermediate combinators.
 */
  stack[pc] = (call){ .return_to = len, .tcoOn = false };

/* 'calling' lets us know if we are entering a CALL or returning from a CALL. */
  bool calling = true;

  /* :TODO: Use static analysis to limit the number of iterations through this loop. */
  while(pc < len) {
    assert(state.activeReadFrame < state.activeWriteFrame);
    assert(state.activeReadFrame->edge <= state.activeWriteFrame->edge);
    switch (dag[pc].tag) {
     case COMP:
      if (calling) {
        /* NEW_FRAME(type_dag[dag[pc].typeAnnotation[1]].bitSize) */
        *(state.activeWriteFrame - 1) = initWriteFrame(type_dag[dag[pc].typeAnnotation[1]].bitSize, state.activeWriteFrame->edge);
        state.activeWriteFrame--;

        /* CALL(dag[pc].child[0], SAME_TCO) */
        stack[dag[pc].child[0]] = (call){ .return_to = pc, .tcoOn = stack[pc].tcoOn };
        pc = dag[pc].child[0];
      } else {
        assert(0 == state.activeWriteFrame->offset);

        /* MOVE_FRAME */
        memmove( state.activeReadFrame->edge, state.activeWriteFrame->edge
               , sizeof(UWORD[(state.activeWriteFrame + 1)->edge - state.activeWriteFrame->edge])
               );
        *(state.activeReadFrame + 1) = initReadFrame(type_dag[dag[pc].typeAnnotation[1]].bitSize, state.activeReadFrame->edge);
        state.activeWriteFrame++; state.activeReadFrame++;

        /* TAIL_CALL(dag[pc].child[1], true) */
        calling = true;
        stack[dag[pc].child[1]] = (call){ .return_to = stack[pc].return_to, .tcoOn = true };
        pc = dag[pc].child[1];
      }
      break;
     case ASSERTL:
     case ASSERTR:
     case CASE:
      if (calling) {
        bool bit = peekBit(state.activeReadFrame);

        /* FWD(1 + PADL(A,B) when bit = 0; FWD(1 + PADR(A,B) when bit = 1 */
        forward(state.activeReadFrame, 1 + pad( bit
                                     , type_dag[dag[pc].typeAnnotation[0]].bitSize
                                     , type_dag[dag[pc].typeAnnotation[1]].bitSize));

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[bit]); */
        stack[dag[pc].child[bit]] = (call)
          { .return_to = stack[pc].tcoOn ? stack[pc].return_to : pc
          , .tcoOn = stack[pc].tcoOn
          };

        /* Remember the bit we peeked at for the case when we return. */
        stack[pc].bit = bit;

        pc = dag[pc].child[bit];

      } else {
        /* BWD(1 + PADL(A,B) when bit = 0; BWD(1 + PADR(A,B) when bit = 1 */
        backward(state.activeReadFrame, 1 + pad( stack[pc].bit
                                      , type_dag[dag[pc].typeAnnotation[0]].bitSize
                                      , type_dag[dag[pc].typeAnnotation[1]].bitSize));

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case PAIR:
      if (calling) {
        /* CALL(dag[pc].child[0], false); */
        stack[dag[pc].child[0]] = (call){ .return_to = pc, .tcoOn = false };
        pc = dag[pc].child[0];
      } else {
        /* TAIL_CALL(dag[pc].child[1], SAME_TCO); */
        calling = true;
        stack[dag[pc].child[1]] = (call)
          { .return_to = stack[pc].return_to
          , .tcoOn = stack[pc].tcoOn
          };
        pc = dag[pc].child[1];
      }
      break;
     case DISCONNECT:
      /* :TODO: Support disconnect */
      fprintf(stderr, "evalTCO for disconnect not yet implemented\n");
      exit(EXIT_FAILURE);
      break;
     case INJL:
     case INJR:
      /* WRITE(0) when INJL; WRITE(1) when INJR */
      writeBit(state.activeWriteFrame, INJR == dag[pc].tag);

      /* SKIP(PADL(A,B)) when INJL; SKIP(PADR(A,B)) when INJR */
      skip(state.activeWriteFrame, pad( INJR == dag[pc].tag
                                 , type_dag[dag[pc].typeAnnotation[1]].bitSize
                                 , type_dag[dag[pc].typeAnnotation[2]].bitSize));
      /*@fallthrough@*/
     case TAKE:
      assert(calling);
      /* TAIL_CALL(dag[pc].child[0], SAME_TCO); */
      stack[dag[pc].child[0]] = (call)
        { .return_to = stack[pc].return_to
        , .tcoOn = stack[pc].tcoOn
        };
      pc = dag[pc].child[0];
      break;
     case DROP:
      if (calling) {
        /* FWD(BITSIZE(A)) */
        forward(state.activeReadFrame, type_dag[dag[pc].typeAnnotation[0]].bitSize);

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[0]); */
        stack[dag[pc].child[0]] = (call)
          { .return_to = stack[pc].tcoOn ? stack[pc].return_to : pc
          , .tcoOn = stack[pc].tcoOn
          };
        pc = dag[pc].child[0];
      } else {
        /* BWD(BITSIZE(A)) */
        backward(state.activeReadFrame, type_dag[dag[pc].typeAnnotation[0]].bitSize);

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case IDEN:
      copyBits(state.activeWriteFrame, state.activeReadFrame, type_dag[dag[pc].typeAnnotation[0]].bitSize);
      /*@fallthrough@*/
     case UNIT:
      assert(calling);
      if (stack[pc].tcoOn) {
        /* DROP_FRAME */
        state.activeReadFrame--;
      }

      /* RETURN; */
      calling = false;
      pc = stack[pc].return_to;
      break;
     case HIDDEN: return false; /* We have failed an 'ASSERTL' or 'ASSERTR' combinator. */
     case WITNESS:
     default:
      /* :TODO: Support witness, jets and primitives */
      fprintf(stderr, "evalTCO for witness, jets, and primitives not yet implemented\n");
      exit(EXIT_FAILURE);
      break;
    }
  }
  assert(pc == len);
  return true;
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
                      ) {
  size_t cellsBound = bounded_add( bounded_add(roundUWord(inputSize), roundUWord(outputSize))
                                 , max(analysis[len-1].extraCellsBoundTCO[0], analysis[len-1].extraCellsBoundTCO[1])
                                 );
  size_t stackBound = bounded_add(analysis[len-1].extraStackBound[0], 2);

  /* :TODO: add reasonable, consensus critical limits to cells and stack bounds */
  if (SIZE_MAX <= cellsBound || SIZE_MAX <= stackBound) return false;

  /* We use calloc for 'cells' because the frame data must be initialized before we can perform bitwise operations. */
  /* :TODO: use a checked_malloc for heap allocations. */
  UWORD* cells = calloc(cellsBound ? cellsBound : 1, sizeof(UWORD));
  frameItem* frames = malloc(sizeof(frameItem[stackBound]));
  call* stack = malloc(sizeof(call[len]));

  bool result = false;

  if (cells && frames && stack) {
    if (input) memcpy(cells, input, sizeof(UWORD[roundUWord(inputSize)]));

    evalState state =
      { .activeReadFrame = frames
      , .activeWriteFrame = frames + (stackBound - 1)
      };
    *(state.activeReadFrame) = initReadFrame(inputSize, cells);
    *(state.activeWriteFrame) = initWriteFrame(outputSize, cells + cellsBound);

    result = runTCO(state, stack, dag, type_dag, len);

    assert(!result || state.activeReadFrame == frames);
    assert(!result || state.activeWriteFrame == frames + (stackBound - 1));

    if (result && output) {
      memcpy(output, state.activeWriteFrame->edge, sizeof(UWORD[roundUWord(outputSize)]));
    }
  }

  free(stack);
  free(frames);
  free(cells);
  return result;
}
