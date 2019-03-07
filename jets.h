/* This module defines jets that simulate various Simplicity expressions.
 * Their specifications are given by the specific Simplicity expressions they are simulating.
 * The witness Merkle roots for each jet's corresponding Simplicity expression is given in 'jetTable.gperf'.
 * See also 'jetTable.h'.
 */
#ifndef JETS_H
#define JETS_H

#include "frame.h"

bool adder32(frameItem* dst, frameItem src);
bool fullAdder32(frameItem* dst, frameItem src);
bool subtractor32(frameItem* dst, frameItem src);
bool fullSubtractor32(frameItem* dst, frameItem src);
bool multiplier32(frameItem* dst, frameItem src);
bool fullMultiplier32(frameItem* dst, frameItem src);
bool sha256_hashBlock(frameItem* dst, frameItem src);

#endif
