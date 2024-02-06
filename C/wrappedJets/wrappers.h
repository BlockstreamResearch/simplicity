#ifndef WRAPPEDJETS_WRAPPERS_H
#define WRAPPEDJETS_WRAPPERS_H

#include "simplicity_assert.h"

#define COREWRAP_(jet)                                                                                                        \
bool c_##jet(frameItem* dst, const frameItem* src) {                                                                          \
  bool result = jet(dst, *src, NULL);                                                                                         \
  simplicity_debug_assert (!result || 0 == dst->offset);                                                                                       \
  return result;                                                                                                              \
}

#define WRAP_(jet)                                                                                                            \
bool c_##jet(frameItem* dst, const frameItem* src, const txEnv* env) {                                                        \
  bool result = jet(dst, *src, env);                                                                                          \
  simplicity_debug_assert (!result || 0 == dst->offset);                                                                                       \
  return result;                                                                                                              \
}

#endif
