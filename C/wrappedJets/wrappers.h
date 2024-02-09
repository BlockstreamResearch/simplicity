#ifndef WRAPPEDJETS_WRAPPERS_H
#define WRAPPEDJETS_WRAPPERS_H

#include "../simplicity_assert.h"

/* In test suites, like the Haskell testsuite, we use test jets via these wrappers.
 * During that testing we allocate a correctly sized frame for each jet,
 * and as part of the testing we want to verify that jet writes to the end of that specifically allocated frame.
 *
 * However, other uses of these jets may call jets in which jets will only write to part of the frame.
 * (this would happen, for instance, when executing jets in a bit machine context.)
 *
 * Therefore we only enable these assertions when JET_FRAME_TESTING is enabled.
 */
#ifdef JET_FRAME_TESTING
#  define JET_FRAME_TESTING_FLAG 1
#else
#  define JET_FRAME_TESTING_FLAG 0
#endif
#define simplicity_jet_frame_assert(cond) do { if (JET_FRAME_TESTING_FLAG) { simplicity_assert(cond); } } while(0)

#define COREWRAP_(jet)                                                                                                        \
bool c_##jet(frameItem* dst, const frameItem* src) {                                                                          \
  bool result = jet(dst, *src, NULL);                                                                                         \
  simplicity_jet_frame_assert(!result || 0 == dst->offset);                                                                   \
  return result;                                                                                                              \
}

#define WRAP_(jet)                                                                                                            \
bool c_##jet(frameItem* dst, const frameItem* src, const txEnv* env) {                                                        \
  bool result = jet(dst, *src, env);                                                                                          \
  simplicity_jet_frame_assert(!result || 0 == dst->offset);                                                                   \
  return result;                                                                                                              \
}

#endif
