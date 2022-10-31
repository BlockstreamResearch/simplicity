Require Import VST.floyd.proofauto.
Require Import jets_secp256k1.
Require Import spec_int128.
Require Import VST.msl.iter_sepcon.
Require Import extraMath.
Require Import progressC.

Opaque Z.shiftl Z.shiftr Z.pow.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition secp256k1_umul128_spec : ident * funspec :=
DECLARE _secp256k1_umul128
  WITH a : Z, b : Z, hi : val, sh : share
PRE [ tulong, tulong, tptr tulong ]
  PROP(writable_share sh;
       0 <= a < Int64.modulus;
       0 <= b < Int64.modulus)
  PARAMS(Vlong (Int64.repr a); Vlong (Int64.repr b); hi)
  SEP(data_at_ sh tulong hi)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr (a * b)))
  SEP(data_at sh tulong (Vlong (Int64.repr (Z.shiftr (a * b) 64))) hi).

Definition secp256k1_mul128_spec : ident * funspec :=
DECLARE _secp256k1_mul128
  WITH a : Z, b : Z, hi : val, sh : share
  PRE [ tlong, tlong, tptr tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed)
    PARAMS(Vlong (Int64.repr a); Vlong (Int64.repr b); hi)
  SEP(data_at_ sh tlong hi)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr (a * b)))
  SEP(data_at sh tlong (Vlong (Int64.repr (Z.shiftr (a * b) 64))) hi).

Lemma iter_sepcon_wand_in B f (x : B) l (Hl : In x l) : iter_sepcon f l = (f x * (f x -* iter_sepcon f l))%logic.
Proof.
apply pred_ext;[|apply wand_frame_elim].
apply In_Permutation_cons in Hl.
destruct Hl as [l' Hl'].
rewrite (iter_sepcon_permutation _ Hl').
simpl.
entailer!.
apply wand_frame_intro.
Qed.

Ltac unfold_Int128 :=
  unfold Int128_max_unsigned,
         Int128_max_signed,
         Int128_min_signed,
         Int128_modulus
  in *|-*.

Definition Gprog := ltac:(with_library prog
  [secp256k1_umul128_spec
  ;secp256k1_mul128_spec
(*   ;secp256k1_u128_load_spec *)
  ;secp256k1_u128_mul_spec
  ;secp256k1_u128_accum_mul_spec
  ;secp256k1_u128_accum_u64_spec
  ;secp256k1_u128_rshift_spec
  ;secp256k1_u128_to_u64_spec
  ;secp256k1_u128_hi_u64_spec
  ;secp256k1_u128_from_u64_spec
  ;secp256k1_u128_check_bits_spec
(*   ;secp256k1_i128_load_spec *)
  ;secp256k1_i128_mul_spec
  ;secp256k1_i128_accum_mul_spec
  ;secp256k1_i128_dissip_mul_spec
  ;secp256k1_i128_det_spec
  ;secp256k1_i128_rshift_spec
  ;secp256k1_i128_to_u64_spec
  ;secp256k1_i128_to_i64_spec
  ;secp256k1_i128_from_i64_spec
  ;secp256k1_i128_eq_var_spec
  ;secp256k1_i128_check_pow2_spec
  ]).

Lemma body_secp256k1_umul128: semax_body Vprog Gprog f_secp256k1_umul128 secp256k1_umul128_spec.
Proof.
start_function.
repeat progressC.
* f_equal.
  apply Int64.eqm_repr_eq.
  eapply Int64.eqm_trans;[apply Int64.eqm_unsigned_repr|apply Int64.eqm_refl2].
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  rewrite !Z.shiftr_div_pow2 by lia.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  (2 ^ 32 * ((a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) +
  2 ^ 32 * ((a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32)  +
  (2 ^ 32 * (a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) +
  (a mod 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32)) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  rewrite <- !(Zmult_mod_distr_l _ _ (2^32)).
  rewrite <- (Z.mod_small (a mod 2 ^ 32 * (b mod 2 ^ 32)) (2^64)) by (rewrite strict_bounds; solve_bounds).
  change (2^32 * 2^32) with (2^64).
  rewrite Zplus_mod_idemp_r, <- Zplus_assoc, Zplus_mod_idemp_l.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  ((2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2^64 +
  (a mod 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32) + b mod 2 ^ 32)))) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  change (2^64) with (2^32 * 2^32) at 1.
  rewrite Zmult_mod_distr_l, Zmult_mod_idemp_r, <- Zmult_mod_distr_l, Zplus_mod_idemp_l.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  ((2 ^ 32 * (a / 2 ^ 32) + (a mod 2 ^ 32)) * b) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  reflexivity.
* rewrite <- (Z.shiftr_shiftr _ 32 32), !Z.shiftr_div_pow2 by lia.
  rewrite <- Z.div_add_l by lia.
  match goal with
   |- context [Int64.repr (?x / 2^32)] => replace x with
   (((2 ^ 32 * (a mod 2 ^ 32 * (b / 2 ^ 32) / 2 ^ 32) + (a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) +
     (a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32)) +
    (a / 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32)) +
    (2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) + (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32))
   ) by ring
  end.
  rewrite <- !Z_div_mod_eq by lia.
  rewrite <- Z.mul_add_distr_l.
  rewrite <- Z_div_mod_eq by lia.
  rewrite <- Z.div_add_l by lia.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.mul_add_distr_l.
  rewrite (Z.mul_comm _ (2^32)).
  rewrite <- Z_div_mod_eq by lia.
  rewrite Z.add_comm.
  rewrite <- Z.div_add_l by lia.
  rewrite (Z.mul_comm _ (2^32)), Z.mul_assoc.
  rewrite <- Z.mul_add_distr_r.
  rewrite <- Z_div_mod_eq by lia.
  entailer!.
Qed.

Lemma body_secp256k1_mul128: semax_body Vprog Gprog f_secp256k1_mul128 secp256k1_mul128_spec.
Proof.
start_function.
repeat progressC.
* f_equal.
  apply Int64.eqm_repr_eq.
  eapply Int64.eqm_trans;[apply Int64.eqm_unsigned_repr|apply Int64.eqm_refl2].
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  rewrite !Z.shiftr_div_pow2 by lia.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  (2 ^ 32 * ((a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) +
  2 ^ 32 * ((a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32)  +
  (2 ^ 32 * (a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) +
  (a mod 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32)) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  rewrite <- !(Zmult_mod_distr_l _ _ (2^32)).
  rewrite <- (Z.mod_small (a mod 2 ^ 32 * (b mod 2 ^ 32)) (2^64)) by (rewrite strict_bounds; solve_bounds).
  change (2^32 * 2^32) with (2^64).
  rewrite Zplus_mod_idemp_r, <- Zplus_assoc, Zplus_mod_idemp_l.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  ((2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2^64 +
  (a mod 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32) + b mod 2 ^ 32)))) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  change (2^64) with (2^32 * 2^32) at 1.
  rewrite Zmult_mod_distr_l, Zmult_mod_idemp_r, <- Zmult_mod_distr_l, Zplus_mod_idemp_l.
  match goal with
   |- (?x mod 2^64) = _ => replace x with
  ((2 ^ 32 * (a / 2 ^ 32) + (a mod 2 ^ 32)) * b) by ring
  end.
  rewrite <- Z_div_mod_eq by lia.
  reflexivity.
* rewrite <- (Z.shiftr_shiftr _ 32 32), !Z.shiftr_div_pow2 by lia.
  rewrite <- Z.div_add_l by lia.
  match goal with
   |- context [Int64.repr (?x / 2^32)] => replace x with
   (((2 ^ 32 * (a mod 2 ^ 32 * (b / 2 ^ 32) / 2 ^ 32) + (a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) +
     (a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32)) +
    (a / 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32)) +
    (2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) + (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32))
   ) by ring
  end.
  rewrite <- !Z_div_mod_eq by lia.
  rewrite <- Z.mul_add_distr_l.
  rewrite <- Z_div_mod_eq by lia.
  rewrite <- Z.div_add_l by lia.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.mul_add_distr_l.
  rewrite (Z.mul_comm _ (2^32)).
  rewrite <- Z_div_mod_eq by lia.
  rewrite Z.add_comm.
  rewrite <- Z.div_add_l by lia.
  rewrite (Z.mul_comm _ (2^32)), Z.mul_assoc.
  rewrite <- Z.mul_add_distr_r.
  rewrite <- Z_div_mod_eq by lia.
  entailer!.
Qed.

(*
Lemma body_secp256k1_u128_load: semax_body Vprog Gprog f_secp256k1_u128_load secp256k1_u128_load_spec.
Proof.
start_function.
repeat forward.
entailer!.
unfold secp256k1_uint128_at.
rewrite <- (Int64.repr_unsigned (Int64.repr (_ + lo))), Int64.unsigned_repr_eq.
rewrite Z.shiftl_mul_pow2, <- Zplus_mod_idemp_l, <- Zmult_mod_idemp_r, Z_mod_same_full by lia.
rewrite Z.mul_0_r, Z.add_0_l.
clear_mod.
rewrite Z.shiftr_div_pow2, Z.div_add_l by lia.
rewrite Z.div_small, Z.add_0_r by solve_bounds.
entailer!.
Qed.
*)

Lemma body_secp256k1_u128_mul: semax_body Vprog Gprog f_secp256k1_u128_mul secp256k1_u128_mul_spec.
Proof.
start_function.
unfold_data_at (data_at_ sh t_secp256k1_uint128 r).
simpl.
rewrite (field_at_data_at _ _ (DOT _hi)).
assert_PROP (field_compatible t_secp256k1_uint128 (DOT _hi) r) by
 entailer!.
forward_call (a, b, (field_address t_secp256k1_uint128 (DOT _hi) r), sh).
forward.
unfold secp256k1_uint128_at.
unfold_data_at (data_at sh t_secp256k1_uint128 _ r).
entailer!.
Qed.

Lemma body_secp256k1_u128_accum_mul: semax_body Vprog Gprog f_secp256k1_u128_accum_mul secp256k1_u128_accum_mul_spec.
Proof.
start_function.
forward_call.
repeat progressC.
unfold secp256k1_uint128_at.
rewrite Z.add_assoc.
rewrite <- shiftr_add_carry by lia.
entailer!.
Qed.

Lemma body_secp256k1_u128_accum_u64: semax_body Vprog Gprog f_secp256k1_u128_accum_u64 secp256k1_u128_accum_u64_spec.
Proof.
start_function.
repeat progressC.
unfold secp256k1_uint128_at.
rewrite shiftr_add_carry by lia.
rewrite (shiftr_small a), Z.add_0_r, (Z.mod_small a) by solve_bounds.
entailer!.
Qed.

Lemma body_secp256k1_u128_rshift: semax_body Vprog Gprog f_secp256k1_u128_rshift secp256k1_u128_rshift_spec.
Proof.
start_function.
forward_verify_check.
 revert H1.
 convert_C_to_math.
 cbn.
 case Z.ltb_spec;[discriminate|lia].
unfold secp256k1_uint128_at.
unfold_Int128.
repeat progressC.
* rewrite !Z.shiftr_shiftr by lia.
  replace (64 + (n - 64)) with n by ring.
  rewrite (shiftr_small _ (n + 64));[entailer!|].
  cut (0 <= r0 < 2^128);[|solve_bounds].
  assert (2^128 <= 2^(n+64)) by (apply Z.pow_le_mono_r;lia).
  lia.
* rewrite !Z.shiftr_shiftr by lia.
  rewrite Z.add_comm.
  replace (Int64.repr (Z.lor _ _)) with (Int64.repr (Z.shiftr r0 n));[entailer!|].
  rewrite <- Z.shiftl_mul_pow2 by lia.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_same_bits.
  change Int64.zwordsize with 64.
  intros i Hi.
  rewrite Z.lor_spec, !Z.shiftr_spec, Z.shiftl_spec by lia.
  destruct (Z.neg_nonneg_cases (i - (64 - n))) as [Hneg|Hpos].
  - rewrite (Z.testbit_neg_r _ _ Hneg).
    rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_high, orb_false_r by lia.
    replace (i - (64 - n) + 64) with (i + n) by ring.
    reflexivity.
* replace n with 0 by lia.
  rewrite Z.shiftr_0_r.
  entailer!.
Qed.

Lemma body_secp256k1_u128_to_u64: semax_body Vprog Gprog f_secp256k1_u128_to_u64 secp256k1_u128_to_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
repeat progressC.
Qed.

Lemma body_secp256k1_u128_hi_u64: semax_body Vprog Gprog f_secp256k1_u128_hi_u64 secp256k1_u128_hi_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
repeat progressC.
Qed.

Lemma body_secp256k1_u128_from_u64: semax_body Vprog Gprog f_secp256k1_u128_from_u64 secp256k1_u128_from_u64_spec.
Proof.
start_function.
repeat progressC.
unfold secp256k1_uint128_at.
replace (Z.shiftr a 64) with 0;[entailer!|].
symmetry; auto using shiftr_small.
Qed.

Lemma body_secp256k1_u128_check_bits: semax_body Vprog Gprog f_secp256k1_u128_check_bits secp256k1_u128_check_bits_spec.
Proof.
start_function.
forward_verify_check.
 revert H1.
 convert_C_to_math.
 cbn.
 case Z.ltb_spec;[discriminate|lia].
unfold secp256k1_uint128_at.
assert (shiftr_small_eq : (r0 <? 2 ^ n) = (Z.shiftr r0 n =? 0)) by
  (case Z.eqb_spec; intros Heq; rewrite shiftr_small_iff in Heq; lia).
forward_if (temp _t'1 (Vint (Int.repr (Z.b2z (r0 <? 2^n)))));[| |forward].
* repeat progressC.
  do 3 f_equal.
  rewrite !Z.shiftr_shiftr by lia.
  replace (64 + (n - 64)) with n by ring.
  assumption.
* repeat progressC.
  - rewrite shiftr_small_eq.
    rewrite (Z_div_mod_eq_full r0 (2^64)) at 1.
    rewrite <- Z.shiftr_div_pow2 by lia.
    apply (f_equal Int64.unsigned) in H2.
    revert H2; convert_C_to_math; intros ->.
    replace (_ + r0 mod 2^64) with (r0 mod 2^64) by ring.
    reflexivity.
  - rewrite shiftr_small_eq.
    case (Z.eqb_spec);[|reflexivity].
    intros Hr0.
    elim H2.
    replace 64 with (n + (64 - n)) by ring.
    rewrite <- Z.shiftr_shiftr, Hr0, Z.shiftr_0_l by lia.
    reflexivity.
Qed.

(*
Lemma body_secp256k1_i128_load: semax_body Vprog Gprog f_secp256k1_i128_load secp256k1_i128_load_spec.
Proof.
start_function.
repeat forward.
entailer!.
unfold secp256k1_uint128_at.
rewrite <- (Int64.repr_unsigned (Int64.repr (_ + lo))), Int64.unsigned_repr_eq.
rewrite Z.shiftl_mul_pow2, <- Zplus_mod_idemp_l, <- Zmult_mod_idemp_r, Z_mod_same_full by lia.
rewrite Z.mul_0_r, Z.add_0_l.
clear_mod.
rewrite Z.shiftr_div_pow2, Z.div_add_l by lia.
rewrite Z.div_small, Z.add_0_r by solve_bounds.
entailer!.
Qed.
*)

Lemma body_secp256k1_i128_mul: semax_body Vprog Gprog f_secp256k1_i128_mul secp256k1_i128_mul_spec.
Proof.
start_function.
forward_call.
repeat progressC.
Qed.

Lemma body_secp256k1_i128_accum_mul: semax_body Vprog Gprog f_secp256k1_i128_accum_mul secp256k1_i128_accum_mul_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
unfold_Int128.
forward_call.
repeat progressC.
forward_verify_check.
 repeat progressC.
 set (hi := (_ + Z.b2z _)).
 forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (((Z.shiftr r0 64) mod 2^64 <=? 9223372036854775807) && (hi mod 2^64 <=? 9223372036854775807))%bool))));
 repeat progressC;
 revert H3;
 convert_C_to_math;
 try solve 
  [repeat (first[case (Z.leb_spec _ _)|case (Z.ltb_spec _ _)];try lia;try reflexivity)].
 case (Z.leb_spec _ _);try discriminate; intros Hr0.
 case (Z.leb_spec _ _);try discriminate; intros Hhi.
 case (Z.ltb_spec _ _);try discriminate; intros Hr0hi.
 apply Int64_low_is_nonneg in Hr0; [|solve_bounds].
 apply Int64_low_is_nonneg in Hhi;[|solve_bounds].
 apply Int64_high_is_neg in Hr0hi;[lia|].
 rewrite Z.add_assoc, <- shiftr_add_carry by lia.
 solve_bounds.
forward_verify_check.
 repeat progressC.
 set (hi := (_ + Z.b2z _)).
 forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((2^63-1 <? (Z.shiftr r0 64) mod 2^64) && (2^63-1 <? hi mod 2^64))%bool))));
 repeat progressC;
 revert H3;
 convert_C_to_math;
 try solve 
  [repeat (first[case (Z.leb_spec _ _)|case (Z.ltb_spec _ _)];try lia;try reflexivity)].
 case (Z.ltb_spec _ _);try discriminate; intros Hr0.
 case (Z.ltb_spec _ _);try discriminate; intros Hhi.
 case (Z.ltb_spec _ _);try discriminate; intros Hr0hi.
 apply Int64_high_is_neg in Hr0; [|solve_bounds].
 apply Int64_high_is_neg in Hhi;[|solve_bounds].
 apply Int64_low_is_nonneg in Hr0hi;[lia|].
 rewrite Z.add_assoc, <- shiftr_add_carry by lia.
 solve_bounds.
repeat progressC.
unfold secp256k1_uint128_at.
rewrite Z.add_assoc, <- shiftr_add_carry by lia.
entailer!.
Qed.

Lemma body_secp256k1_i128_dissip_mul: semax_body Vprog Gprog f_secp256k1_i128_dissip_mul secp256k1_i128_dissip_mul_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
unfold_Int128.
forward_call.
repeat progressC.
forward_verify_check.
 repeat progressC.
 set (hi := (_ + Z.b2z _)).
 forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (((Z.shiftr r0 64) mod 2^64 <=? 2^63-1) && (2^63-1 <? hi mod 2^64))%bool))));
 repeat progressC;
 revert H3;
 convert_C_to_math;
 try solve 
  [repeat (first[case (Z.leb_spec _ _)|case (Z.ltb_spec _ _)];try lia;try reflexivity)].
 case (Z.leb_spec _ _);try discriminate; intros Hr0.
 case (Z.ltb_spec _ _);try discriminate; intros Hhi.
 case (Z.ltb_spec _ _);try discriminate; intros Hr0hi.
 apply Int64_low_is_nonneg in Hr0; [|solve_bounds].
 apply Int64_high_is_neg in Hhi;[|solve_bounds].
 apply Int64_high_is_neg in Hr0hi;[lia|].
 rewrite Z.sub_add_distr, <- shiftr_sub_borrow by lia.
 solve_bounds.
forward_verify_check.
 repeat progressC.
 set (hi := (_ + Z.b2z _)).
 forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((2^63-1 <? (Z.shiftr r0 64) mod 2^64) && (hi mod 2^64 <=? 2^63-1))%bool))));
 repeat progressC;
 revert H3;
 convert_C_to_math;
 try solve 
  [repeat (first[case (Z.leb_spec _ _)|case (Z.ltb_spec _ _)];try lia;try reflexivity)].
 case (Z.ltb_spec _ _);try discriminate; intros Hr0.
 case (Z.leb_spec _ _);try discriminate; intros Hhi.
 case (Z.ltb_spec _ _);try discriminate; intros Hr0hi.
 apply Int64_high_is_neg in Hr0; [|solve_bounds].
 apply Int64_low_is_nonneg in Hhi;[|solve_bounds].
 apply Int64_low_is_nonneg in Hr0hi;[lia|].
 rewrite Z.sub_add_distr, <- shiftr_sub_borrow by lia.
 solve_bounds.
repeat progressC.
unfold secp256k1_uint128_at.
rewrite Z.sub_add_distr, <- shiftr_sub_borrow by lia.
entailer!.
Qed.

Lemma body_secp256k1_i128_det: semax_body Vprog Gprog f_secp256k1_i128_det secp256k1_i128_det_spec.
Proof.
start_function.
forward_call.
forward_call;[|entailer!].
unfold Int128_min_signed, Int128_max_signed.
assert (Htight := mul128_tight _ _ H H2).
assert (Htight' := mul128_tight _ _ H0 H1).
lia.
Qed.

Lemma body_secp256k1_i128_rshift: semax_body Vprog Gprog f_secp256k1_i128_rshift secp256k1_i128_rshift_spec.
Proof.
start_function.
forward_verify_check.
 revert H1.
 convert_C_to_math.
 cbn.
 case Z.ltb_spec;[discriminate|lia].
unfold secp256k1_uint128_at.
unfold_Int128.
repeat progressC.
* rewrite !Z.shiftr_shiftr by lia.
  replace (64 + (n - 64)) with n by ring.
  change (64 + 63) with 127.
  replace (n + 64) with (127 + (n - 63)) by ring.
  rewrite shiftr_small_signed by solve_bounds.
  entailer!.
* rewrite !Z.shiftr_shiftr by lia.
  rewrite Z.add_comm.
  replace (Int64.repr (Z.lor _ _)) with (Int64.repr (Z.shiftr r0 n));[entailer!|].
  rewrite <- Z.shiftl_mul_pow2 by lia.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_same_bits.
  change Int64.zwordsize with 64.
  intros i Hi.
  rewrite Z.lor_spec, !Z.shiftr_spec, Z.shiftl_spec by lia.
  destruct (Z.neg_nonneg_cases (i - (64 - n))) as [Hneg|Hpos].
   rewrite (Z.testbit_neg_r _ _ Hneg).
   rewrite Z.mod_pow2_bits_low by lia.
   reflexivity.
  rewrite Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_high, orb_false_r by lia.
  replace (i - (64 - n) + 64) with (i + n) by ring.
  reflexivity.
* replace n with 0 by lia.
  rewrite Z.shiftr_0_r.
  entailer!.
Qed.

Lemma body_secp256k1_i128_to_u64: semax_body Vprog Gprog f_secp256k1_i128_to_u64 secp256k1_i128_to_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
repeat progressC.
Qed.

Lemma body_secp256k1_i128_to_i64: semax_body Vprog Gprog f_secp256k1_i128_to_i64 secp256k1_i128_to_i64_spec.
Proof.
start_function.
forward_verify_check.
 repeat progressC.
 revert H0.
 convert_C_to_math.
 change (Z.shiftr r0 64) with (Z.shiftr r0 (63 + 1)).
 rewrite <- Z.shiftr_shiftr by lia.
 destruct (Z.neg_nonneg_cases r0) as [Hneg|Hpos].
  rewrite <- (Z_mod_plus_full r0 1 (2^64)), Z.mul_1_l.
  clear_mod.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (r0 + 2 ^ 64) with (r0 + 2 * 2^63).
  rewrite Z_div_plus_full by lia.
  replace (r0 / 2^63) with (-1).
   rewrite Z.eqb_refl; discriminate.
  cut (-1 <= r0 / 2 ^ 63 < 0);[|apply div_bounds];lia.
 clear_mod.
 replace (Z.shiftr r0 63) with 0.
  rewrite Z.eqb_refl; discriminate.
 rewrite !Z.shiftr_div_pow2, Z.div_small by lia.
 reflexivity.
forward_call.
repeat progressC.
Qed.

Lemma body_secp256k1_i128_from_i64: semax_body Vprog Gprog f_secp256k1_i128_from_i64 secp256k1_i128_from_i64_spec.
Proof.
start_function.
repeat progressC.
unfold secp256k1_uint128_at.
change 64 with (63 + 1).
rewrite <- Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia.
destruct (Z.neg_nonneg_cases a).
+ replace (a/2^63) with (-1);[entailer!|].
  cut (0 = a / 2^63 + 1);[lia|].
  rewrite <- Z_div_plus, Z.mul_1_l by lia.
  rewrite Zdiv_small;[reflexivity|rep_lia].
+ rewrite (Zdiv_small a);[entailer!|rep_lia].
Qed.

Lemma body_secp256k1_i128_eq_var: semax_body Vprog Gprog f_secp256k1_i128_eq_var secp256k1_i128_eq_var_spec.
Proof.
start_function.
do 2 forward.
assert (Hrs: r0 mod 2 ^ 128 =? s0 mod 2 ^ 128 =
             (((Z.shiftr r0 64) mod 2 ^ 64 =? (Z.shiftr s0 64) mod 2 ^ 64) &&
                (r0 mod 2^64 =? s0 mod 2^64))%bool).
 change (2^128) with (2^64 * 2^64).
 rewrite !Zmod_recombine, <-! Z.shiftl_mul_pow2, <-! Z.shiftr_div_pow2 by lia.
 apply shiftl_mod_eqb_unique; lia.
forward_if
  (temp _t'1 (Vint (Int.repr (Z.b2z (r0 mod 2^128 =? s0 mod 2^128))))).
+ repeat progressC.
  rewrite Hrs.
  revert H.
  convert_C_to_math.
  intros ->.
  reflexivity.
+ repeat progressC.
  apply Int64.eq_false in H.
  rewrite Hrs.
  revert H.
  convert_C_to_math.
  intros ->.
  reflexivity.
+ repeat progressC.
Qed.

(* Use with
   forward_call secp256k1_i128_eq_var_spec_alias_sub (r, shr, r0)
*)
Lemma secp256k1_i128_eq_var_spec_alias_sub :
  funspec_sub (snd secp256k1_i128_eq_var_spec) (snd secp256k1_i128_eq_var_spec_alias).
Proof.
do_funspec_sub.
destruct w as [[r shr] r0].
entailer!.
destruct (slice.split_readable_share _ H0) as [sh1 [sh2 [Hsh1 [Hsh2 Hsh]]]].
Exists (((((r, sh1), r0), r), sh2), r0) emp.
unfold secp256k1_uint128_at.
rewrite <- (data_at_share_join _ _ _ _ _ _ Hsh), Z.eqb_refl.
entailer!.
intros.
entailer!.
Qed.

Lemma body_secp256k1_i128_check_pow2: semax_body Vprog Gprog f_secp256k1_i128_check_pow2 secp256k1_i128_check_pow2_spec.
Proof.
start_function.
unfold_Int128.
forward_verify_check.
 revert H2.
 convert_C_to_math.
 cbn.
 case Z.ltb_spec;[discriminate|lia].
forward_verify_check.
 forward_if (temp _t'1 (Vint (Int.repr 1)));
 [forward|forward;replace sign with (-1) by lia|]; try entailer!.
 forward_if;[discriminate|forward;entailer].
unfold secp256k1_uint128_at.
forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (r0 =? sign*2^n)))));[| |forward].
* assert (Hr0: r0 =? sign * 2 ^ n =
             ((Z.shiftr r0 64 =? sign * 2 ^ (n - 64)) && (r0 mod 2^64 =? 0))%bool).
   rewrite (Z_div_mod_eq_full r0 (2^64)) at 1.
   rewrite Z.mul_comm.
   replace n with (n - 64 + 64) at 1 by ring.
   rewrite <- (Z.add_0_r (sign * 2 ^ (n - 64 + 64))).
   change 0 with (0 mod 2^64).
   rewrite Z.pow_add_r, Z.mul_assoc, <- !Z.shiftl_mul_pow2, <- Z.shiftr_div_pow2 by lia.
   apply shiftl_mod_eqb_unique; lia.
  repeat progressC.
  - rewrite Hr0.
    replace (_ =? sign * 2 ^ _) with true;[reflexivity|].
    symmetry; rewrite Z.eqb_eq.
    revert H3.
    convert_C_to_math.
    rewrite Z.eqb_eq.
    apply (Z_mod_eq_bounded (-2^63) (2^63)); try solve_bounds.
    pose (Hpow := Z.pow_lt_mono_r 2 (n-64) 63).
    lia.
  - rewrite Hr0.
    case Z.eqb_spec; try reflexivity.
    intros Hr0n.
    elim H3.
    convert_C_to_math.
    congruence.
* assert (Hr0: r0 =? sign * 2 ^ n =
             ((Z.shiftr r0 64 =? Z.shiftr (sign - 1) 1) && (r0 mod 2^64 =? (sign * 2^n) mod 2^64))%bool).
   rewrite (Z_div_mod_eq_full r0 (2^64)) at 1.
   rewrite (Z_div_mod_eq_full (sign * 2^n) (2^64)) at 1.
   rewrite !(Z.mul_comm (2^64)).
   rewrite <- (Z.shiftl_mul_pow2 _ n), <- !(Z.shiftl_mul_pow2 _ 64), <- !Z.shiftr_div_pow2,
           Z.shiftr_shiftl_l by lia.
   replace (n - 64) with (-(64 - n)) by ring.
   rewrite Z.shiftl_opp_r.
   replace (Z.shiftr sign (64 - n)) with (Z.shiftr (sign - 1) 1).
   apply shiftl_mod_eqb_unique; lia.
   destruct H1 as [-> | ->];
   [rewrite Z_shiftr_neg1_l;[reflexivity|lia]|].
   rewrite (shiftr_small 1);[reflexivity|].
   split; try apply Z.pow_gt_1; lia.
  repeat progressC.
  - rewrite Hr0.
    replace (_ =? Z.shiftr _ _) with true;[reflexivity|].
    symmetry; rewrite Z.eqb_eq.
    revert H3.
    convert_C_to_math.
    rewrite Z.eqb_eq.
    apply (Z_mod_eq_bounded (-2^63) (2^63)); solve_bounds.
  - rewrite Hr0.
    case Z.eqb_spec; try reflexivity.
    intros Hr0n.
    elim H3.
    convert_C_to_math.
    congruence.
Qed.
