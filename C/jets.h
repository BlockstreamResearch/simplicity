/* This module defines jets that simulate various Simplicity expressions.
 * Their specifications are given by the specific Simplicity expressions they are simulating.
 * The witness Merkle roots for each jet's corresponding Simplicity expression is given in 'jetTable.gperf'.
 * See also 'jetTable.h'.
 */
#ifndef JETS_H
#define JETS_H

#include "jetTable.h"

bool adder32(frameItem* dst, frameItem src, const txEnv* env);
bool fullAdder32(frameItem* dst, frameItem src, const txEnv* env);
bool subtractor32(frameItem* dst, frameItem src, const txEnv* env);
bool fullSubtractor32(frameItem* dst, frameItem src, const txEnv* env);
bool multiplier32(frameItem* dst, frameItem src, const txEnv* env);
bool fullMultiplier32(frameItem* dst, frameItem src, const txEnv* env);
bool sha256_hashBlock(frameItem* dst, frameItem src, const txEnv* env);

#endif
