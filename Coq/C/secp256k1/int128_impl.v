(* clightgen -normalize -I secp256k1 -D USE_FORCE_WIDEMUL_INT128_STRUCT -D VERIFY secp256k1/int128_impl.c *)
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "11114914".
  Definition build_tag := "auto/2022/04/25/1917".
  Definition build_branch := "auto/2022/04".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "secp256k1/int128_impl.c".
  Definition normalized := true.
End Info.

Definition __IO_FILE : ident := $"_IO_FILE".
Definition __IO_backup_base : ident := $"_IO_backup_base".
Definition __IO_buf_base : ident := $"_IO_buf_base".
Definition __IO_buf_end : ident := $"_IO_buf_end".
Definition __IO_codecvt : ident := $"_IO_codecvt".
Definition __IO_marker : ident := $"_IO_marker".
Definition __IO_read_base : ident := $"_IO_read_base".
Definition __IO_read_end : ident := $"_IO_read_end".
Definition __IO_read_ptr : ident := $"_IO_read_ptr".
Definition __IO_save_base : ident := $"_IO_save_base".
Definition __IO_save_end : ident := $"_IO_save_end".
Definition __IO_wide_data : ident := $"_IO_wide_data".
Definition __IO_write_base : ident := $"_IO_write_base".
Definition __IO_write_end : ident := $"_IO_write_end".
Definition __IO_write_ptr : ident := $"_IO_write_ptr".
Definition ___builtin_addl : ident := $"__builtin_addl".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_isfinite : ident := $"__builtin_isfinite".
Definition ___builtin_isfinitef : ident := $"__builtin_isfinitef".
Definition ___builtin_isinf : ident := $"__builtin_isinf".
Definition ___builtin_isinff : ident := $"__builtin_isinff".
Definition ___builtin_isnan : ident := $"__builtin_isnan".
Definition ___builtin_isnanf : ident := $"__builtin_isnanf".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_mull : ident := $"__builtin_mull".
Definition ___builtin_nan : ident := $"__builtin_nan".
Definition ___builtin_nanf : ident := $"__builtin_nanf".
Definition ___builtin_nans : ident := $"__builtin_nans".
Definition ___builtin_nansf : ident := $"__builtin_nansf".
Definition ___builtin_negl : ident := $"__builtin_negl".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_subl : ident := $"__builtin_subl".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_ftos : ident := $"__compcert_i64_ftos".
Definition ___compcert_i64_ftou : ident := $"__compcert_i64_ftou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float32 : ident := $"__compcert_va_float32".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___pad5 : ident := $"__pad5".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition __chain : ident := $"_chain".
Definition __codecvt : ident := $"_codecvt".
Definition __cur_column : ident := $"_cur_column".
Definition __fileno : ident := $"_fileno".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __freeres_buf : ident := $"_freeres_buf".
Definition __freeres_list : ident := $"_freeres_list".
Definition __lock : ident := $"_lock".
Definition __markers : ident := $"_markers".
Definition __mode : ident := $"_mode".
Definition __offset : ident := $"_offset".
Definition __old_offset : ident := $"_old_offset".
Definition __shortbuf : ident := $"_shortbuf".
Definition __unused2 : ident := $"_unused2".
Definition __vtable_offset : ident := $"_vtable_offset".
Definition __wide_data : ident := $"_wide_data".
Definition _a : ident := $"a".
Definition _abort : ident := $"abort".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _d : ident := $"d".
Definition _fprintf : ident := $"fprintf".
Definition _hh : ident := $"hh".
Definition _hi : ident := $"hi".
Definition _hl : ident := $"hl".
Definition _lh : ident := $"lh".
Definition _ll : ident := $"ll".
Definition _lo : ident := $"lo".
Definition _main : ident := $"main".
Definition _mid34 : ident := $"mid34".
Definition _n : ident := $"n".
Definition _r : ident := $"r".
Definition _secp256k1_anchor : ident := $"secp256k1_anchor".
Definition _secp256k1_i128_accum_mul : ident := $"secp256k1_i128_accum_mul".
Definition _secp256k1_i128_check_pow2 : ident := $"secp256k1_i128_check_pow2".
Definition _secp256k1_i128_det : ident := $"secp256k1_i128_det".
Definition _secp256k1_i128_dissip_mul : ident := $"secp256k1_i128_dissip_mul".
Definition _secp256k1_i128_eq_var : ident := $"secp256k1_i128_eq_var".
Definition _secp256k1_i128_from_i64 : ident := $"secp256k1_i128_from_i64".
Definition _secp256k1_i128_mul : ident := $"secp256k1_i128_mul".
Definition _secp256k1_i128_rshift : ident := $"secp256k1_i128_rshift".
Definition _secp256k1_i128_to_i64 : ident := $"secp256k1_i128_to_i64".
Definition _secp256k1_mul128 : ident := $"secp256k1_mul128".
Definition _secp256k1_u128_accum_mul : ident := $"secp256k1_u128_accum_mul".
Definition _secp256k1_u128_accum_u64 : ident := $"secp256k1_u128_accum_u64".
Definition _secp256k1_u128_check_bits : ident := $"secp256k1_u128_check_bits".
Definition _secp256k1_u128_from_u64 : ident := $"secp256k1_u128_from_u64".
Definition _secp256k1_u128_hi_u64 : ident := $"secp256k1_u128_hi_u64".
Definition _secp256k1_u128_mul : ident := $"secp256k1_u128_mul".
Definition _secp256k1_u128_rshift : ident := $"secp256k1_u128_rshift".
Definition _secp256k1_u128_to_u64 : ident := $"secp256k1_u128_to_u64".
Definition _secp256k1_uint128 : ident := $"secp256k1_uint128".
Definition _secp256k1_umul128 : ident := $"secp256k1_umul128".
Definition _stderr : ident := $"stderr".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 142);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 43) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 139);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 43) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 141);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 140);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_stderr := {|
  gvar_info := (tptr (Tstruct __IO_FILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_secp256k1_umul128 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, tulong) :: (_b, tulong) :: (_hi, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ll, tulong) :: (_lh, tulong) :: (_hl, tulong) ::
               (_hh, tulong) :: (_mid34, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _ll
    (Ebinop Omul (Ecast (Ecast (Etempvar _a tulong) tuint) tulong)
      (Ecast (Etempvar _b tulong) tuint) tulong))
  (Ssequence
    (Sset _lh
      (Ebinop Omul (Ecast (Etempvar _a tulong) tuint)
        (Ebinop Oshr (Etempvar _b tulong) (Econst_int (Int.repr 32) tint)
          tulong) tulong))
    (Ssequence
      (Sset _hl
        (Ebinop Omul
          (Ebinop Oshr (Etempvar _a tulong) (Econst_int (Int.repr 32) tint)
            tulong) (Ecast (Etempvar _b tulong) tuint) tulong))
      (Ssequence
        (Sset _hh
          (Ebinop Omul
            (Ebinop Oshr (Etempvar _a tulong) (Econst_int (Int.repr 32) tint)
              tulong)
            (Ebinop Oshr (Etempvar _b tulong) (Econst_int (Int.repr 32) tint)
              tulong) tulong))
        (Ssequence
          (Sset _mid34
            (Ebinop Oadd
              (Ebinop Oadd
                (Ebinop Oshr (Etempvar _ll tulong)
                  (Econst_int (Int.repr 32) tint) tulong)
                (Ecast (Etempvar _lh tulong) tuint) tulong)
              (Ecast (Etempvar _hl tulong) tuint) tulong))
          (Ssequence
            (Sassign (Ederef (Etempvar _hi (tptr tulong)) tulong)
              (Ebinop Oadd
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _hh tulong)
                    (Ebinop Oshr (Etempvar _lh tulong)
                      (Econst_int (Int.repr 32) tint) tulong) tulong)
                  (Ebinop Oshr (Etempvar _hl tulong)
                    (Econst_int (Int.repr 32) tint) tulong) tulong)
                (Ebinop Oshr (Etempvar _mid34 tulong)
                  (Econst_int (Int.repr 32) tint) tulong) tulong))
            (Sreturn (Some (Ebinop Oadd
                             (Ebinop Oshl (Etempvar _mid34 tulong)
                               (Econst_int (Int.repr 32) tint) tulong)
                             (Ecast (Etempvar _ll tulong) tuint) tulong)))))))))
|}.

Definition f_secp256k1_mul128 := {|
  fn_return := tlong;
  fn_callconv := cc_default;
  fn_params := ((_a, tlong) :: (_b, tlong) :: (_hi, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ll, tulong) :: (_lh, tlong) :: (_hl, tlong) ::
               (_hh, tlong) :: (_mid34, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _ll
    (Ebinop Omul (Ecast (Ecast (Etempvar _a tlong) tuint) tulong)
      (Ecast (Etempvar _b tlong) tuint) tulong))
  (Ssequence
    (Sset _lh
      (Ebinop Omul (Ecast (Etempvar _a tlong) tuint)
        (Ebinop Oshr (Etempvar _b tlong) (Econst_int (Int.repr 32) tint)
          tlong) tlong))
    (Ssequence
      (Sset _hl
        (Ebinop Omul
          (Ebinop Oshr (Etempvar _a tlong) (Econst_int (Int.repr 32) tint)
            tlong) (Ecast (Etempvar _b tlong) tuint) tlong))
      (Ssequence
        (Sset _hh
          (Ebinop Omul
            (Ebinop Oshr (Etempvar _a tlong) (Econst_int (Int.repr 32) tint)
              tlong)
            (Ebinop Oshr (Etempvar _b tlong) (Econst_int (Int.repr 32) tint)
              tlong) tlong))
        (Ssequence
          (Sset _mid34
            (Ebinop Oadd
              (Ebinop Oadd
                (Ebinop Oshr (Etempvar _ll tulong)
                  (Econst_int (Int.repr 32) tint) tulong)
                (Ecast (Etempvar _lh tlong) tuint) tulong)
              (Ecast (Etempvar _hl tlong) tuint) tulong))
          (Ssequence
            (Sassign (Ederef (Etempvar _hi (tptr tlong)) tlong)
              (Ebinop Oadd
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _hh tlong)
                    (Ebinop Oshr (Etempvar _lh tlong)
                      (Econst_int (Int.repr 32) tint) tlong) tlong)
                  (Ebinop Oshr (Etempvar _hl tlong)
                    (Econst_int (Int.repr 32) tint) tlong) tlong)
                (Ebinop Oshr (Etempvar _mid34 tulong)
                  (Econst_int (Int.repr 32) tint) tulong) tulong))
            (Sreturn (Some (Ebinop Oadd
                             (Ebinop Oshl (Etempvar _mid34 tulong)
                               (Econst_int (Int.repr 32) tint) tulong)
                             (Ecast (Etempvar _ll tulong) tuint) tulong)))))))))
|}.

Definition f_secp256k1_u128_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tulong) :: (_b, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _secp256k1_umul128 (Tfunction
                               (Tcons tulong
                                 (Tcons tulong (Tcons (tptr tulong) Tnil)))
                               tulong cc_default))
    ((Etempvar _a tulong) :: (Etempvar _b tulong) ::
     (Eaddrof
       (Efield
         (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
           (Tstruct _secp256k1_uint128 noattr)) _hi tulong) (tptr tulong)) ::
     nil))
  (Sassign
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
    (Etempvar _t'1 tulong)))
|}.

Definition f_secp256k1_u128_accum_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tulong) :: (_b, tulong) :: nil);
  fn_vars := ((_hi, tulong) :: nil);
  fn_temps := ((_lo, tulong) :: (_t'1, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _secp256k1_umul128 (Tfunction
                                 (Tcons tulong
                                   (Tcons tulong (Tcons (tptr tulong) Tnil)))
                                 tulong cc_default))
      ((Etempvar _a tulong) :: (Etempvar _b tulong) ::
       (Eaddrof (Evar _hi tulong) (tptr tulong)) :: nil))
    (Sset _lo (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
        (Ebinop Oadd (Etempvar _t'5 tulong) (Etempvar _lo tulong) tulong)))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
      (Ssequence
        (Sset _t'3 (Evar _hi tulong))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
            (Ebinop Oadd (Etempvar _t'2 tulong)
              (Ebinop Oadd (Etempvar _t'3 tulong)
                (Ebinop Olt (Etempvar _t'4 tulong) (Etempvar _lo tulong)
                  tint) tulong) tulong)))))))
|}.

Definition f_secp256k1_u128_accum_u64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
    (Sassign
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
      (Ebinop Oadd (Etempvar _t'3 tulong) (Etempvar _a tulong) tulong)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
        (Ebinop Oadd (Etempvar _t'1 tulong)
          (Ebinop Olt (Etempvar _t'2 tulong) (Etempvar _a tulong) tint)
          tulong)))))
|}.

Definition f_secp256k1_u128_rshift := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, (tptr (Tstruct __IO_FILE noattr))) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Sifthenelse (Eunop Onotbool
                   (Ebinop Olt (Etempvar _n tuint)
                     (Econst_int (Int.repr 128) tint) tint) tint)
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'5 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'5 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_3 (tarray tschar 11)) ::
               (Evar ___stringlit_2 (tarray tschar 31)) ::
               (Econst_int (Int.repr 67) tint) ::
               (Evar ___stringlit_1 (tarray tschar 31)) :: nil)))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
        Sbreak)
      Sskip)
    Sbreak)
  (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                 (Econst_int (Int.repr 64) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
          (Ebinop Oshr (Etempvar _t'4 tulong)
            (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 64) tint)
              tuint) tulong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
        (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Ebinop Ogt (Etempvar _n tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
              (Ebinop Oor
                (Ebinop Oshl
                  (Ebinop Omul (Econst_int (Int.repr 1) tuint)
                    (Etempvar _t'2 tulong) tulong)
                  (Ebinop Osub (Econst_int (Int.repr 64) tint)
                    (Etempvar _n tuint) tuint) tulong)
                (Ebinop Oshr (Etempvar _t'3 tulong) (Etempvar _n tuint)
                  tulong) tulong))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
            (Ebinop Oshr (Etempvar _t'1 tulong) (Etempvar _n tuint) tulong))))
      Sskip)))
|}.

Definition f_secp256k1_u128_to_u64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _secp256k1_uint128 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _a (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_secp256k1_u128_hi_u64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _secp256k1_uint128 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _a (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_secp256k1_u128_from_u64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
    (Econst_int (Int.repr 0) tint))
  (Sassign
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
    (Etempvar _a tulong)))
|}.

Definition f_secp256k1_u128_check_bits := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'5, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Sifthenelse (Eunop Onotbool
                   (Ebinop Olt (Etempvar _n tuint)
                     (Econst_int (Int.repr 128) tint) tint) tint)
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'5 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'5 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_3 (tarray tschar 11)) ::
               (Evar ___stringlit_2 (tarray tschar 31)) ::
               (Econst_int (Int.repr 91) tint) ::
               (Evar ___stringlit_1 (tarray tschar 31)) :: nil)))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
        Sbreak)
      Sskip)
    Sbreak)
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                   (Econst_int (Int.repr 64) tint) tint)
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sset _t'1
          (Ecast
            (Ebinop Oeq
              (Ebinop Oshr (Etempvar _t'4 tulong)
                (Ebinop Osub (Etempvar _n tuint)
                  (Econst_int (Int.repr 64) tint) tuint) tulong)
              (Econst_int (Int.repr 0) tint) tint) tint)))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
              (Sset _t'1
                (Ecast
                  (Ebinop Oeq
                    (Ebinop Oshr (Etempvar _t'3 tulong) (Etempvar _n tuint)
                      tulong) (Econst_int (Int.repr 0) tint) tint) tbool)))
            (Sset _t'1 (Ecast (Etempvar _t'1 tint) tint)))
          (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_secp256k1_i128_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tlong) :: (_b, tlong) :: nil);
  fn_vars := ((_hi, tlong) :: nil);
  fn_temps := ((_t'1, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _secp256k1_mul128 (Tfunction
                                (Tcons tlong
                                  (Tcons tlong (Tcons (tptr tlong) Tnil)))
                                tlong cc_default))
      ((Etempvar _a tlong) :: (Etempvar _b tlong) ::
       (Eaddrof (Evar _hi tlong) (tptr tlong)) :: nil))
    (Sassign
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
      (Ecast (Etempvar _t'1 tlong) tulong)))
  (Ssequence
    (Sset _t'2 (Evar _hi tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
      (Ecast (Etempvar _t'2 tlong) tulong))))
|}.

Definition f_secp256k1_i128_accum_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tlong) :: (_b, tlong) :: nil);
  fn_vars := ((_hi, tlong) :: nil);
  fn_temps := ((_lo, tulong) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tlong) :: (_t'18, tulong) :: (_t'17, tulong) ::
               (_t'16, tlong) :: (_t'15, tlong) :: (_t'14, tulong) ::
               (_t'13, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'12, tlong) :: (_t'11, tulong) :: (_t'10, tlong) ::
               (_t'9, tulong) :: (_t'8, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'7, tlong) :: (_t'6, tulong) :: (_t'5, tlong) ::
               (_t'4, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _secp256k1_mul128 (Tfunction
                                (Tcons tlong
                                  (Tcons tlong (Tcons (tptr tlong) Tnil)))
                                tlong cc_default))
      ((Etempvar _a tlong) :: (Etempvar _b tlong) ::
       (Eaddrof (Evar _hi tlong) (tptr tlong)) :: nil))
    (Sset _lo (Ecast (Etempvar _t'1 tlong) tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'18
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
        (Ebinop Oadd (Etempvar _t'18 tulong) (Etempvar _lo tulong) tulong)))
    (Ssequence
      (Ssequence
        (Sset _t'16 (Evar _hi tlong))
        (Ssequence
          (Sset _t'17
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
          (Sassign (Evar _hi tlong)
            (Ebinop Oadd (Etempvar _t'16 tlong)
              (Ebinop Olt (Etempvar _t'17 tulong) (Etempvar _lo tulong) tint)
              tlong))))
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'14
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
              (Sifthenelse (Ebinop Ole (Etempvar _t'14 tulong)
                             (Econst_long (Int64.repr 9223372036854775807) tulong)
                             tint)
                (Ssequence
                  (Sset _t'15 (Evar _hi tlong))
                  (Sset _t'2
                    (Ecast
                      (Ebinop Ole (Ecast (Etempvar _t'15 tlong) tulong)
                        (Econst_long (Int64.repr 9223372036854775807) tulong)
                        tint) tbool)))
                (Sset _t'2 (Econst_int (Int.repr 0) tint))))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
              (Ssequence
                (Sset _t'12 (Evar _hi tlong))
                (Sifthenelse (Eunop Onotbool
                               (Ebinop Ole (Etempvar _t'2 tint)
                                 (Ebinop Ole
                                   (Ebinop Oadd (Etempvar _t'11 tulong)
                                     (Ecast (Etempvar _t'12 tlong) tulong)
                                     tulong)
                                   (Econst_long (Int64.repr 9223372036854775807) tulong)
                                   tint) tint) tint)
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Sset _t'13
                          (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'13 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_3 (tarray tschar 11)) ::
                           (Evar ___stringlit_2 (tarray tschar 31)) ::
                           (Econst_int (Int.repr 112) tint) ::
                           (Evar ___stringlit_4 (tarray tschar 142)) :: nil)))
                      (Scall None
                        (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
                    Sbreak)
                  Sskip))))
          Sbreak)
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                      (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
                (Sifthenelse (Ebinop Ogt (Etempvar _t'9 tulong)
                               (Econst_long (Int64.repr 9223372036854775807) tulong)
                               tint)
                  (Ssequence
                    (Sset _t'10 (Evar _hi tlong))
                    (Sset _t'3
                      (Ecast
                        (Ebinop Ogt (Ecast (Etempvar _t'10 tlong) tulong)
                          (Econst_long (Int64.repr 9223372036854775807) tulong)
                          tint) tbool)))
                  (Sset _t'3 (Econst_int (Int.repr 0) tint))))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                      (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
                (Ssequence
                  (Sset _t'7 (Evar _hi tlong))
                  (Sifthenelse (Eunop Onotbool
                                 (Ebinop Ole (Etempvar _t'3 tint)
                                   (Ebinop Ogt
                                     (Ebinop Oadd (Etempvar _t'6 tulong)
                                       (Ecast (Etempvar _t'7 tlong) tulong)
                                       tulong)
                                     (Econst_long (Int64.repr 9223372036854775807) tulong)
                                     tint) tint) tint)
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Sset _t'8
                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                          (Scall None
                            (Evar _fprintf (Tfunction
                                             (Tcons
                                               (tptr (Tstruct __IO_FILE noattr))
                                               (Tcons (tptr tschar) Tnil))
                                             tint
                                             {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                            ((Etempvar _t'8 (tptr (Tstruct __IO_FILE noattr))) ::
                             (Evar ___stringlit_3 (tarray tschar 11)) ::
                             (Evar ___stringlit_2 (tarray tschar 31)) ::
                             (Econst_int (Int.repr 117) tint) ::
                             (Evar ___stringlit_5 (tarray tschar 139)) ::
                             nil)))
                        (Scall None
                          (Evar _abort (Tfunction Tnil tvoid cc_default))
                          nil))
                      Sbreak)
                    Sskip))))
            Sbreak)
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
            (Ssequence
              (Sset _t'5 (Evar _hi tlong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
                (Ebinop Oadd (Etempvar _t'4 tulong) (Etempvar _t'5 tlong)
                  tulong)))))))))
|}.

Definition f_secp256k1_i128_dissip_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tlong) :: (_b, tlong) :: nil);
  fn_vars := ((_hi, tlong) :: nil);
  fn_temps := ((_lo, tulong) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tlong) :: (_t'18, tulong) :: (_t'17, tlong) ::
               (_t'16, tlong) :: (_t'15, tulong) ::
               (_t'14, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'13, tlong) :: (_t'12, tulong) :: (_t'11, tlong) ::
               (_t'10, tulong) ::
               (_t'9, (tptr (Tstruct __IO_FILE noattr))) :: (_t'8, tlong) ::
               (_t'7, tulong) :: (_t'6, tlong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _secp256k1_mul128 (Tfunction
                                (Tcons tlong
                                  (Tcons tlong (Tcons (tptr tlong) Tnil)))
                                tlong cc_default))
      ((Etempvar _a tlong) :: (Etempvar _b tlong) ::
       (Eaddrof (Evar _hi tlong) (tptr tlong)) :: nil))
    (Sset _lo (Ecast (Etempvar _t'1 tlong) tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'17 (Evar _hi tlong))
      (Ssequence
        (Sset _t'18
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
        (Sassign (Evar _hi tlong)
          (Ebinop Oadd (Etempvar _t'17 tlong)
            (Ebinop Olt (Etempvar _t'18 tulong) (Etempvar _lo tulong) tint)
            tlong))))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'15
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
            (Sifthenelse (Ebinop Ole (Etempvar _t'15 tulong)
                           (Econst_long (Int64.repr 9223372036854775807) tulong)
                           tint)
              (Ssequence
                (Sset _t'16 (Evar _hi tlong))
                (Sset _t'2
                  (Ecast
                    (Ebinop Ogt (Ecast (Etempvar _t'16 tlong) tulong)
                      (Econst_long (Int64.repr 9223372036854775807) tulong)
                      tint) tbool)))
              (Sset _t'2 (Econst_int (Int.repr 0) tint))))
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
            (Ssequence
              (Sset _t'13 (Evar _hi tlong))
              (Sifthenelse (Eunop Onotbool
                             (Ebinop Ole (Etempvar _t'2 tint)
                               (Ebinop Ole
                                 (Ebinop Osub (Etempvar _t'12 tulong)
                                   (Ecast (Etempvar _t'13 tlong) tulong)
                                   tulong)
                                 (Econst_long (Int64.repr 9223372036854775807) tulong)
                                 tint) tint) tint)
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'14
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Scall None
                        (Evar _fprintf (Tfunction
                                         (Tcons
                                           (tptr (Tstruct __IO_FILE noattr))
                                           (Tcons (tptr tschar) Tnil)) tint
                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                        ((Etempvar _t'14 (tptr (Tstruct __IO_FILE noattr))) ::
                         (Evar ___stringlit_3 (tarray tschar 11)) ::
                         (Evar ___stringlit_2 (tarray tschar 31)) ::
                         (Econst_int (Int.repr 129) tint) ::
                         (Evar ___stringlit_6 (tarray tschar 141)) :: nil)))
                    (Scall None
                      (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
                  Sbreak)
                Sskip))))
        Sbreak)
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
              (Sifthenelse (Ebinop Ogt (Etempvar _t'10 tulong)
                             (Econst_long (Int64.repr 9223372036854775807) tulong)
                             tint)
                (Ssequence
                  (Sset _t'11 (Evar _hi tlong))
                  (Sset _t'3
                    (Ecast
                      (Ebinop Ole (Ecast (Etempvar _t'11 tlong) tulong)
                        (Econst_long (Int64.repr 9223372036854775807) tulong)
                        tint) tbool)))
                (Sset _t'3 (Econst_int (Int.repr 0) tint))))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
              (Ssequence
                (Sset _t'8 (Evar _hi tlong))
                (Sifthenelse (Eunop Onotbool
                               (Ebinop Ole (Etempvar _t'3 tint)
                                 (Ebinop Ogt
                                   (Ebinop Osub (Etempvar _t'7 tulong)
                                     (Ecast (Etempvar _t'8 tlong) tulong)
                                     tulong)
                                   (Econst_long (Int64.repr 9223372036854775807) tulong)
                                   tint) tint) tint)
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'9 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_3 (tarray tschar 11)) ::
                           (Evar ___stringlit_2 (tarray tschar 31)) ::
                           (Econst_int (Int.repr 134) tint) ::
                           (Evar ___stringlit_7 (tarray tschar 140)) :: nil)))
                      (Scall None
                        (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
                    Sbreak)
                  Sskip))))
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
            (Ssequence
              (Sset _t'6 (Evar _hi tlong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
                (Ebinop Osub (Etempvar _t'5 tulong) (Etempvar _t'6 tlong)
                  tulong))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
              (Ebinop Osub (Etempvar _t'4 tulong) (Etempvar _lo tulong)
                tulong))))))))
|}.

Definition f_secp256k1_i128_det := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tlong) :: (_b, tlong) :: (_c, tlong) :: (_d, tlong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _secp256k1_i128_mul (Tfunction
                                (Tcons
                                  (tptr (Tstruct _secp256k1_uint128 noattr))
                                  (Tcons tlong (Tcons tlong Tnil))) tvoid
                                cc_default))
    ((Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr))) ::
     (Etempvar _a tlong) :: (Etempvar _d tlong) :: nil))
  (Scall None
    (Evar _secp256k1_i128_dissip_mul (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _secp256k1_uint128 noattr))
                                         (Tcons tlong (Tcons tlong Tnil)))
                                       tvoid cc_default))
    ((Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr))) ::
     (Etempvar _b tlong) :: (Etempvar _c tlong) :: nil)))
|}.

Definition f_secp256k1_i128_rshift := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, (tptr (Tstruct __IO_FILE noattr))) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Sifthenelse (Eunop Onotbool
                   (Ebinop Olt (Etempvar _n tuint)
                     (Econst_int (Int.repr 128) tint) tint) tint)
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'6 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'6 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_3 (tarray tschar 11)) ::
               (Evar ___stringlit_2 (tarray tschar 31)) ::
               (Econst_int (Int.repr 148) tint) ::
               (Evar ___stringlit_1 (tarray tschar 31)) :: nil)))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
        Sbreak)
      Sskip)
    Sbreak)
  (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                 (Econst_int (Int.repr 64) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
          (Ecast
            (Ebinop Oshr (Ecast (Etempvar _t'5 tulong) tlong)
              (Ebinop Osub (Etempvar _n tuint)
                (Econst_int (Int.repr 64) tint) tuint) tlong) tulong)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
          (Ecast
            (Ebinop Oshr (Ecast (Etempvar _t'4 tulong) tlong)
              (Econst_int (Int.repr 63) tint) tlong) tulong))))
    (Sifthenelse (Ebinop Ogt (Etempvar _n tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
              (Ebinop Oor
                (Ebinop Oshl
                  (Ebinop Omul (Econst_int (Int.repr 1) tuint)
                    (Etempvar _t'2 tulong) tulong)
                  (Ebinop Osub (Econst_int (Int.repr 64) tint)
                    (Etempvar _n tuint) tuint) tulong)
                (Ebinop Oshr (Etempvar _t'3 tulong) (Etempvar _n tuint)
                  tulong) tulong))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
            (Ecast
              (Ebinop Oshr (Ecast (Etempvar _t'1 tulong) tlong)
                (Etempvar _n tuint) tlong) tulong))))
      Sskip)))
|}.

Definition f_secp256k1_i128_to_i64 := {|
  fn_return := tlong;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _secp256k1_uint128 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _a (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
  (Sreturn (Some (Ecast (Etempvar _t'1 tulong) tlong))))
|}.

Definition f_secp256k1_i128_from_i64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_a, tlong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _hi tulong)
    (Ecast
      (Ebinop Oshr (Etempvar _a tlong) (Econst_int (Int.repr 63) tint) tlong)
      tulong))
  (Sassign
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
        (Tstruct _secp256k1_uint128 noattr)) _lo tulong)
    (Ecast (Etempvar _a tlong) tulong)))
|}.

Definition f_secp256k1_i128_eq_var := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_b, (tptr (Tstruct _secp256k1_uint128 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _a (tptr (Tstruct _secp256k1_uint128 noattr)))
          (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _b (tptr (Tstruct _secp256k1_uint128 noattr)))
            (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tulong) (Etempvar _t'3 tulong)
                     tint)
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef
                (Etempvar _a (tptr (Tstruct _secp256k1_uint128 noattr)))
                (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _b (tptr (Tstruct _secp256k1_uint128 noattr)))
                  (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
            (Sset _t'1
              (Ecast
                (Ebinop Oeq (Etempvar _t'4 tulong) (Etempvar _t'5 tulong)
                  tint) tbool))))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_secp256k1_i128_check_pow2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _secp256k1_uint128 noattr))) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'6, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Sifthenelse (Eunop Onotbool
                   (Ebinop Olt (Etempvar _n tuint)
                     (Econst_int (Int.repr 127) tint) tint) tint)
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'6 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'6 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_3 (tarray tschar 11)) ::
               (Evar ___stringlit_2 (tarray tschar 31)) ::
               (Econst_int (Int.repr 172) tint) ::
               (Evar ___stringlit_8 (tarray tschar 31)) :: nil)))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
        Sbreak)
      Sskip)
    Sbreak)
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                   (Econst_int (Int.repr 64) tint) tint)
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tulong)
                       (Ebinop Oshl
                         (Ecast (Econst_int (Int.repr 1) tint) tulong)
                         (Ebinop Osub (Etempvar _n tuint)
                           (Econst_int (Int.repr 64) tint) tuint) tulong)
                       tint)
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
              (Sset _t'1
                (Ecast
                  (Ebinop Oeq (Etempvar _t'5 tulong)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))
            (Sset _t'1 (Ecast (Etempvar _t'1 tint) tint)))
          (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
              (Tstruct _secp256k1_uint128 noattr)) _hi tulong))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _r (tptr (Tstruct _secp256k1_uint128 noattr)))
                    (Tstruct _secp256k1_uint128 noattr)) _lo tulong))
              (Sset _t'1
                (Ecast
                  (Ebinop Oeq (Etempvar _t'3 tulong)
                    (Ebinop Oshl
                      (Ecast (Econst_int (Int.repr 1) tint) tulong)
                      (Etempvar _n tuint) tulong) tint) tbool)))
            (Sset _t'1 (Ecast (Etempvar _t'1 tint) tint)))
          (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_secp256k1_anchor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn None)
|}.

Definition composites : list composite_definition :=
(Composite __IO_FILE Struct
   (Member_plain __flags tint :: Member_plain __IO_read_ptr (tptr tschar) ::
    Member_plain __IO_read_end (tptr tschar) ::
    Member_plain __IO_read_base (tptr tschar) ::
    Member_plain __IO_write_base (tptr tschar) ::
    Member_plain __IO_write_ptr (tptr tschar) ::
    Member_plain __IO_write_end (tptr tschar) ::
    Member_plain __IO_buf_base (tptr tschar) ::
    Member_plain __IO_buf_end (tptr tschar) ::
    Member_plain __IO_save_base (tptr tschar) ::
    Member_plain __IO_backup_base (tptr tschar) ::
    Member_plain __IO_save_end (tptr tschar) ::
    Member_plain __markers (tptr (Tstruct __IO_marker noattr)) ::
    Member_plain __chain (tptr (Tstruct __IO_FILE noattr)) ::
    Member_plain __fileno tint :: Member_plain __flags2 tint ::
    Member_plain __old_offset tlong :: Member_plain __cur_column tushort ::
    Member_plain __vtable_offset tschar ::
    Member_plain __shortbuf (tarray tschar 1) ::
    Member_plain __lock (tptr tvoid) :: Member_plain __offset tlong ::
    Member_plain __codecvt (tptr (Tstruct __IO_codecvt noattr)) ::
    Member_plain __wide_data (tptr (Tstruct __IO_wide_data noattr)) ::
    Member_plain __freeres_list (tptr (Tstruct __IO_FILE noattr)) ::
    Member_plain __freeres_buf (tptr tvoid) :: Member_plain ___pad5 tulong ::
    Member_plain __mode tint :: Member_plain __unused2 (tarray tschar 20) ::
    nil)
   noattr ::
 Composite _secp256k1_uint128 Struct
   (Member_plain _lo tulong :: Member_plain _hi tulong :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_float32,
   Gfun(External (EF_runtime "__compcert_va_float32"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons (tptr tvoid) Tnil) tfloat cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_ftos,
   Gfun(External (EF_runtime "__compcert_i64_ftos"
                   (mksignature (AST.Tsingle :: nil) AST.Tlong cc_default))
     (Tcons tfloat Tnil) tulong cc_default)) ::
 (___compcert_i64_ftou,
   Gfun(External (EF_runtime "__compcert_i64_ftou"
                   (mksignature (AST.Tsingle :: nil) AST.Tlong cc_default))
     (Tcons tfloat Tnil) tlong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_negl,
   Gfun(External (EF_builtin "__builtin_negl"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tlong Tnil) tlong cc_default)) ::
 (___builtin_addl,
   Gfun(External (EF_builtin "__builtin_addl"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_subl,
   Gfun(External (EF_builtin "__builtin_subl"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_mull,
   Gfun(External (EF_builtin "__builtin_mull"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_nanf,
   Gfun(External (EF_builtin "__builtin_nanf"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons (tptr tschar) Tnil) tfloat cc_default)) ::
 (___builtin_nansf,
   Gfun(External (EF_builtin "__builtin_nansf"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons (tptr tschar) Tnil) tfloat cc_default)) ::
 (___builtin_nan,
   Gfun(External (EF_builtin "__builtin_nan"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tschar) Tnil) tdouble cc_default)) ::
 (___builtin_nans,
   Gfun(External (EF_builtin "__builtin_nans"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tschar) Tnil) tdouble cc_default)) ::
 (___builtin_isnanf,
   Gfun(External (EF_builtin "__builtin_isnanf"
                   (mksignature (AST.Tsingle :: nil) AST.Tint cc_default))
     (Tcons tfloat Tnil) tint cc_default)) ::
 (___builtin_isnan,
   Gfun(External (EF_builtin "__builtin_isnan"
                   (mksignature (AST.Tfloat :: nil) AST.Tint cc_default))
     (Tcons tdouble Tnil) tint cc_default)) ::
 (___builtin_isinff,
   Gfun(External (EF_builtin "__builtin_isinff"
                   (mksignature (AST.Tsingle :: nil) AST.Tint cc_default))
     (Tcons tfloat Tnil) tint cc_default)) ::
 (___builtin_isinf,
   Gfun(External (EF_builtin "__builtin_isinf"
                   (mksignature (AST.Tfloat :: nil) AST.Tint cc_default))
     (Tcons tdouble Tnil) tint cc_default)) ::
 (___builtin_isfinitef,
   Gfun(External (EF_builtin "__builtin_isfinitef"
                   (mksignature (AST.Tsingle :: nil) AST.Tint cc_default))
     (Tcons tfloat Tnil) tint cc_default)) ::
 (___builtin_isfinite,
   Gfun(External (EF_builtin "__builtin_isfinite"
                   (mksignature (AST.Tfloat :: nil) AST.Tint cc_default))
     (Tcons tdouble Tnil) tint cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_builtin "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil AST.Tvoid cc_default))
     Tnil tvoid cc_default)) :: (_stderr, Gvar v_stderr) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_secp256k1_umul128, Gfun(Internal f_secp256k1_umul128)) ::
 (_secp256k1_mul128, Gfun(Internal f_secp256k1_mul128)) ::
 (_secp256k1_u128_mul, Gfun(Internal f_secp256k1_u128_mul)) ::
 (_secp256k1_u128_accum_mul, Gfun(Internal f_secp256k1_u128_accum_mul)) ::
 (_secp256k1_u128_accum_u64, Gfun(Internal f_secp256k1_u128_accum_u64)) ::
 (_secp256k1_u128_rshift, Gfun(Internal f_secp256k1_u128_rshift)) ::
 (_secp256k1_u128_to_u64, Gfun(Internal f_secp256k1_u128_to_u64)) ::
 (_secp256k1_u128_hi_u64, Gfun(Internal f_secp256k1_u128_hi_u64)) ::
 (_secp256k1_u128_from_u64, Gfun(Internal f_secp256k1_u128_from_u64)) ::
 (_secp256k1_u128_check_bits, Gfun(Internal f_secp256k1_u128_check_bits)) ::
 (_secp256k1_i128_mul, Gfun(Internal f_secp256k1_i128_mul)) ::
 (_secp256k1_i128_accum_mul, Gfun(Internal f_secp256k1_i128_accum_mul)) ::
 (_secp256k1_i128_dissip_mul, Gfun(Internal f_secp256k1_i128_dissip_mul)) ::
 (_secp256k1_i128_det, Gfun(Internal f_secp256k1_i128_det)) ::
 (_secp256k1_i128_rshift, Gfun(Internal f_secp256k1_i128_rshift)) ::
 (_secp256k1_i128_to_i64, Gfun(Internal f_secp256k1_i128_to_i64)) ::
 (_secp256k1_i128_from_i64, Gfun(Internal f_secp256k1_i128_from_i64)) ::
 (_secp256k1_i128_eq_var, Gfun(Internal f_secp256k1_i128_eq_var)) ::
 (_secp256k1_i128_check_pow2, Gfun(Internal f_secp256k1_i128_check_pow2)) ::
 (_secp256k1_anchor, Gfun(Internal f_secp256k1_anchor)) :: nil).

Definition public_idents : list ident :=
(_secp256k1_anchor :: _fprintf :: _stderr :: _abort ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_debug :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_isfinite :: ___builtin_isfinitef :: ___builtin_isinf ::
 ___builtin_isinff :: ___builtin_isnan :: ___builtin_isnanf ::
 ___builtin_nans :: ___builtin_nan :: ___builtin_nansf :: ___builtin_nanf ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_mull :: ___builtin_subl :: ___builtin_addl ::
 ___builtin_negl :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_ftou :: ___compcert_i64_ftos :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float32 :: ___compcert_va_float64 :: ___compcert_va_int64 ::
 ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


