#include <secp256k1.h>
#include "int128_impl.h"

/* Avoid having static functions purned as dead code by making sure they are "used" somewhere. */
void secp256k1_anchor(void) {
  (void)(&secp256k1_u128_mul);
  (void)(&secp256k1_i128_check_bit);
  (void)(&secp256k1_u128_accum_mul);
  (void)(&secp256k1_u128_accum_u64);
  (void)(&secp256k1_u128_rshift);
  (void)(&secp256k1_u128_to_u64);
  (void)(&secp256k1_u128_hi_u64);
  (void)(&secp256k1_u128_from_u64);
  (void)(&secp256k1_u128_check_bits);
  (void)(&secp256k1_i128_mul);
  (void)(&secp256k1_i128_accum_mul);
  (void)(&secp256k1_i128_det);
  (void)(&secp256k1_i128_rshift);
  (void)(&secp256k1_i128_to_i64);
  (void)(&secp256k1_i128_from_i64);
  (void)(&secp256k1_i128_eq_var);
  (void)(&secp256k1_i128_check_bit);
  return;
}
