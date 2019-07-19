/* This module provides the 'lookupJet' function for finding jets (see 'jets.h') by witness Merkle root. */
#ifndef JETTABLE_H
#define JETTABLE_H

#include "frame.h"
#include "tag.h"

/* 'JET_FLAG's are used to characterize different groups of jets.
 * This allows some jets to be selectively enabled.
 * The primary purpose of this is to allow the testing of the Simplicity specifications that characterize jets.
 * This allows you to enable (already tested) jets in the body of such specifications without
 * turning the specification itself into a jet.
 */
#define JET_FLAG unsigned int
#define JET_WORD (1 << 0)
#define JET_HASH (1 << 1)
#define JET_EC   (1 << 2)
#define JET_SIG  (1 << 3)
#define JET_ALL  ((JET_FLAG)-1)

/* A jet simulates the execution of some Simplicity expression (without witnesses or delegation) of A |- B.
 * It reads data from a read frame 'src', and writes its output to a write frame 'dst'.
 * If successful then 'true' is returned.
 * If the expression being simulated would fail an 'ASSERTL' or 'ASSERTR' combinator, then 'false' is returned.
 * Cells in front of 'dst's cursor's final position may be overwritten.
 *
 * Precondition: 'src' is a valid read frame for 'bitSize(A)' more cells;
 *               '*dst' is a valid write frame for 'bitSize(B)' more cells;
 */
typedef bool (*jet_ptr)(frameItem* dst, frameItem src);

/* Given a witness Merkle root for some Simplicity expression, find a jet that simulates it.
 * If such a jet is found, and that jet's type matches the 'filter' then the jet is returned.
 * Otherwise 'NULL' is returned.
 *
 * Precondition: wmr != NULL.
 */
jet_ptr lookupJet(const sha256_midstate *wmr, JET_FLAG filter);

#endif
