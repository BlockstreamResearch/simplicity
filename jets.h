/* This module defines jets that simulate various Simplicity expressions.
 * Their specifications are given by the specific Simplicity expressions they are simulating.
 */
#ifndef SIMPLICITY_JETS_H
#define SIMPLICITY_JETS_H

#include "frame.h"

/* Forward declaration of the structure holding the environment in which a Simplicity expression is evaluated within. */
typedef struct txEnv txEnv;

/* A jet simulates the execution of some Simplicity expression (without witnesses or delegation) of A |- B.
 * It reads data from a read frame 'src', and writes its output to a write frame 'dst'.
 * If successful then 'true' is returned.
 * If the expression being simulated would fail an 'ASSERTL' or 'ASSERTR' combinator, then 'false' is returned.
 * Cells in front of 'dst's cursor's final position may be overwritten.
 *
 * Precondition: 'src' is a valid read frame for 'bitSize(A)' more cells;
 *               '*dst' is a valid write frame for 'bitSize(B)' more cells;
 *               if the jet simulates a Simplicity expression with primitives then 'NULL != env';
 */
typedef bool (*jet_ptr)(frameItem* dst, frameItem src, const txEnv* env);

bool add_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_32(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_32(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env);

#endif
