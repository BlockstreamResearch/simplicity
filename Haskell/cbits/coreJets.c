#include "jets.h"

#define WRAP_(jet)                                                                                                            \
bool c_##jet(frameItem* dst, const frameItem* src) {                                                                          \
  return jet(dst, *src, NULL);                                                                                                \
}

WRAP_(add_32)
WRAP_(full_add_32)
WRAP_(subtract_32)
WRAP_(full_subtract_32)
WRAP_(multiply_32)
WRAP_(full_multiply_32)

WRAP_(sha_256_block)

WRAP_(fe_normalize)
WRAP_(fe_negate)
WRAP_(fe_add)
WRAP_(fe_square)
WRAP_(fe_multiply)
WRAP_(fe_multiply_beta)
WRAP_(fe_invert)
WRAP_(fe_square_root)
WRAP_(fe_is_zero)
WRAP_(fe_is_odd)
WRAP_(scalar_normalize)
WRAP_(scalar_negate)
WRAP_(scalar_add)
WRAP_(scalar_square)
WRAP_(scalar_multiply)
WRAP_(scalar_multiply_lambda)
WRAP_(scalar_invert)
WRAP_(scalar_is_zero)
WRAP_(gej_infinity)
WRAP_(gej_rescale)
WRAP_(gej_normalize)
WRAP_(gej_negate)
WRAP_(ge_negate)
WRAP_(gej_double)
WRAP_(gej_add)
WRAP_(gej_ge_add_ex)
WRAP_(gej_ge_add)
WRAP_(gej_is_infinity)
WRAP_(gej_x_equiv)
WRAP_(gej_y_is_odd)
WRAP_(gej_is_on_curve)
WRAP_(ge_is_on_curve)
WRAP_(scale)
WRAP_(generate)
WRAP_(linear_combination_1)
WRAP_(linear_verify_1)
WRAP_(decompress)
WRAP_(point_verify_1)
WRAP_(bip_0340_verify)
WRAP_(parse_lock)
WRAP_(parse_sequence)