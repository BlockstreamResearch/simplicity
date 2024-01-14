#ifndef WRAPPEDJETS_WRAPPERS_H
#define WRAPPEDJETS_WRAPPERS_H

#define COREWRAP_(jet)                                                                                                        \
bool c_##jet(frameItem* dst, const frameItem* src) {                                                                          \
  bool result = jet(dst, *src, NULL);                                                                                         \
  assert (!result || 0 == dst->offset);                                                                                       \
  return result;                                                                                                              \
}

#define WRAP_(jet)                                                                                                            \
bool c_##jet(frameItem* dst, const frameItem* src, const txEnv* env) {                                                        \
  bool result = jet(dst, *src, env);                                                                                          \
  assert (!result || 0 == dst->offset);                                                                                       \
  return result;                                                                                                              \
}

#endif
