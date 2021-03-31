#include "jets.h"

bool c_add_32(frameItem* dst, const frameItem *src) {
  return add_32(dst, *src, NULL);
}

bool c_full_add_32(frameItem* dst, const frameItem *src) {
  return full_add_32(dst, *src, NULL);
}

bool c_subtract_32(frameItem* dst, const frameItem *src) {
  return subtract_32(dst, *src, NULL);
}

bool c_full_subtract_32(frameItem* dst, const frameItem *src) {
  return full_subtract_32(dst, *src, NULL);
}

bool c_multiply_32(frameItem* dst, const frameItem *src) {
  return multiply_32(dst, *src, NULL);
}

bool c_full_multiply_32(frameItem* dst, const frameItem *src) {
  return full_multiply_32(dst, *src, NULL);
}

bool c_sha_256_block(frameItem* dst, const frameItem* src) {
  return sha_256_block(dst, *src, NULL);
}
