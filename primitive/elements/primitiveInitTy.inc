/* This file has been automatically generated. */
(*bound_var)[ty_u] = (unification_var){ .isBound = true, .bound = { .kind = ONE }};
(*bound_var)[ty_b] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_u] } }};
(*bound_var)[ty_w2] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_b], &(*bound_var)[ty_b] } }};
(*bound_var)[ty_w4] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w2], &(*bound_var)[ty_w2] } }};
(*bound_var)[ty_w8] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w4], &(*bound_var)[ty_w4] } }};
(*bound_var)[ty_w16] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w8], &(*bound_var)[ty_w8] } }};
(*bound_var)[ty_w32] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w16], &(*bound_var)[ty_w16] } }};
(*bound_var)[ty_w64] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w32], &(*bound_var)[ty_w32] } }};
(*bound_var)[ty_w128] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w64], &(*bound_var)[ty_w64] } }};
(*bound_var)[ty_w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w128], &(*bound_var)[ty_w128] } }};
(*bound_var)[ty_w512] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w256], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_w1024] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w512], &(*bound_var)[ty_w512] } }};
(*bound_var)[ty_mb] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_b] } }};
(*bound_var)[ty_mw32] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_w32] } }};
(*bound_var)[ty_mw256] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_mw512] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_w512] } }};
(*bound_var)[ty_mmw256] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_mw256] } }};
(*bound_var)[ty_mmspbw256w64] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_mspbw256w64] } }};
(*bound_var)[ty_mmspbw256w256] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_mspbw256w256] } }};
(*bound_var)[ty_mmspw2w256sbw4] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_mspw2w256sbw4] } }};
(*bound_var)[ty_mspbw256w64] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_spbw256w64] } }};
(*bound_var)[ty_mspbw256w256] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_spbw256w256] } }};
(*bound_var)[ty_mspw2w256sbw4] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_spw2w256sbw4] } }};
(*bound_var)[ty_mpw256w32] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_u], &(*bound_var)[ty_pw256w32] } }};
(*bound_var)[ty_sbw4] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_b], &(*bound_var)[ty_w4] } }};
(*bound_var)[ty_spbw256w64] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_pbw256], &(*bound_var)[ty_w64] } }};
(*bound_var)[ty_spbw256w256] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_pbw256], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_spw2w256sbw4] = (unification_var){ .isBound = true, .bound = { .kind = SUM, .arg = { &(*bound_var)[ty_pw2w256], &(*bound_var)[ty_sbw4] } }};
(*bound_var)[ty_pbw32] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_b], &(*bound_var)[ty_w32] } }};
(*bound_var)[ty_pbw64] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_b], &(*bound_var)[ty_w64] } }};
(*bound_var)[ty_pbw256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_b], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_pw2w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w2], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_pw256w32] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w256], &(*bound_var)[ty_w32] } }};
(*bound_var)[ty_pw256w512] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w256], &(*bound_var)[ty_w512] } }};
(*bound_var)[ty_pw256pbw256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w256], &(*bound_var)[ty_pbw256] } }};
(*bound_var)[ty_pw256pw512w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w256], &(*bound_var)[ty_pw512w256] } }};
(*bound_var)[ty_pw512w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_w512], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_ppw256w512w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw256w512], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_ppw256pbw256w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw256pbw256], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_ppw256pw512w256w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw256pw512w256], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_ppw512w256w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw512w256], &(*bound_var)[ty_w256] } }};
(*bound_var)[ty_ppw512w256w512] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw512w256], &(*bound_var)[ty_w512] } }};
(*bound_var)[ty_ppw512w256pw512w256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_pw512w256], &(*bound_var)[ty_pw512w256] } }};
(*bound_var)[ty_pppw256w512w256w512] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_ppw256w512w256], &(*bound_var)[ty_w512] } }};
(*bound_var)[ty_pppw256pbw256w256pbw256] = (unification_var){ .isBound = true, .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[ty_ppw256pbw256w256], &(*bound_var)[ty_pbw256] } }};