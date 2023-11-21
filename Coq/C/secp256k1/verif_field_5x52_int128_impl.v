Require Import VST.floyd.proofauto.
Require Import jets_secp256k1.
Require Import spec_int128.
Require Import spec_field_5x52.
Require Import extraMath.
Require Import extraVST.
Require Import progressC.
Require Import Setoid.

Opaque Z.shiftl Z.shiftr Z.pow.

Section Dettman.

Add Parametric Relation N : Z (eqm N)
 reflexivity proved by (eqm_refl N)
 symmetry proved by (eqm_sym N)
 transitivity proved by (eqm_trans N)
as eqm_Setoid.

Add Parametric Morphism N : Z.add
 with signature (eqm N ==> eqm N ==> eqm N) 
 as Zadd_eqm.
Proof.
apply Zplus_eqm.
Qed.

Add Parametric Morphism N : Z.mul
 with signature (eqm N ==> eqm N ==> eqm N) 
 as Zmul_eqm.
Proof.
apply Zmult_eqm.
Qed.

Definition dettman_reduce (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Z) : list Z :=
let c := p8 in
let d := p3 + 16 * secp256k1_R * (c mod 2^64) in
let c := Z.shiftr c 64 in
let t3 := d mod 2^52 in
let d := Z.shiftr d 52 + p4 + 2^16 * secp256k1_R * c in
let tx := Z.shiftr (d mod 2^52) 48 in
let t4 := d mod 2^48 in
let d := Z.shiftr d 52 + p5 in
let c := p0 + (Z.lor (d mod 2^52 * 2^4) tx) * secp256k1_R in
let r0 := c mod 2^52 in
let d := Z.shiftr d 52 + p6 in
let c := Z.shiftr c 52 + p1 + (d mod 2^52) * (secp256k1_R * 2^4) in
let r1 := c mod 2^52 in
let d := Z.shiftr d 52 + p7 in
let c := Z.shiftr c 52 + p2 + (secp256k1_R * 2^4) * (d mod 2^64) in
let r2 := c mod 2^52 in
let d := Z.shiftr d 64 in
let c := Z.shiftr c 52 + (secp256k1_R * 2^16) * d + t3 in
let r3 := c mod 2^52 in
let c := Z.shiftr c 52 in
let r4 := c + t4 in
[r0;r1;r2;r3;r4].

Lemma dettman_reduce_spec p0 p1 p2 p3 p4 p5 p6 p7 p8 : 
  eqm secp256k1_P (secp256k1_fe_array.from_array (dettman_reduce p0 p1 p2 p3 p4 p5 p6 p7 p8))
                  (secp256k1_fe_array.from_array [p0; p1; p2; p3; p4; p5; p6; p7; p8]).
Proof.
unfold dettman_reduce.
simpl (secp256k1_fe_array.from_array [p0; p1; p2; p3; p4; p5; p6; p7; p8]).
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
set (d0 := p3 + (16 * secp256k1_R) * (p8 mod (2^64))).
set (t3 := d0 mod 2^52).
set (d1 := d0 / 2^52 + p4 + (2^16 * secp256k1_R) * (p8 / 2^64)).
rewrite <- (Z.land_ones d1 52), <- (Z.shiftr_div_pow2 _ 48), Z.shiftr_land by lia.
change ((Z.shiftr (Z.ones 52) 48)) with (Z.ones 4).
set (tx := (Z.land (Z.shiftr d1 48) (Z.ones 4))).
set (t4 := d1 mod 2^48).
set (d2 := d1 / 2^52 + p5).
rewrite <- (Z.shiftl_mul_pow2 _ 4), <- (Z.land_ones d2 52) by lia.
assert (Hland : Z.land (Z.shiftl (Z.land d2 (Z.ones 52)) 4) tx = 0).
1:{
 apply Z.bits_inj'; intros n Hn.
 unfold tx.
 rewrite Z.bits_0, !Z.land_spec, Z.shiftl_spec, Z.land_spec, Z.shiftr_spec, !Z.testbit_ones; lia.
}
rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption.
clear Hland.
rewrite !Z.shiftl_mul_pow2, !Z.land_ones by lia.
set (c0 := p0 + (((d2 mod 2^52) * 2^4) + tx) * secp256k1_R).
set (d3 := d2 / 2^52 + p6).
set (c1 := c0 / 2^52 + p1 + (d3 mod 2^52) * (secp256k1_R * 2^4)).
set (d4 := d3 / 2^52 + p7).
set (c2 := c1 / 2^52 + p2 + (secp256k1_R * 2^4) * (d4 mod 2^64)).
set (d5 := d4 / 2^64).
set (c3 := c2 / 2^52 + (secp256k1_R * 2^16) * d5 + t3).
set (c4 := c3 / 2^52).
symmetry.
ring_simplify.
replace (_ + _ * p8) with
  ((2^156 * (p3 + 2^260 * p8) + 2^208 * p4) + 2^260 * p5 +
   p0 + 2^312 * p6 + 2^52 * p1 + 2^364 * p7 + 2^104 * p2)
 by ring.
rewrite (Z.div_mod p8 (2^64)) by lia.
replace (2 ^ 156 * (p3 + 2 ^ 260 * (2 ^ 64 * (p8 / 2^64) + p8 mod 2^64)) + 2^208 * p4)
 with (2 ^ 156 * (p3  + (16 * 2 ^ 256) * (p8 mod 2^64)) + 2^208 * (p4 + (2 ^ 256 * 2^16) * (p8 / 2^64)))
 by ring.
assert (HR : eqm secp256k1_P (2^256) secp256k1_R) by reflexivity.
setoid_rewrite HR.
fold d0.
rewrite (Z.div_mod d0 (2^52)) by lia.
fold t3.
replace (2 ^ 156 * (2 ^ 52 * (d0 / 2 ^ 52) + t3)
     + 2 ^ 208 * (p4 + secp256k1_R * 2 ^ 16 * (p8 / 2 ^ 64)))
 with (2 ^ 156 * t3 
     + 2 ^ 208 * ((d0 / 2 ^ 52) + p4 + 2 ^ 16 * secp256k1_R * (p8 / 2 ^ 64)))
 by ring.
fold d1.
rewrite (Z.div_mod d1 (2^52)), <- (Z.land_ones d1) by lia.
rewrite <- (Z.lor_ldiff_and (Z.land d1 _) (Z.ones 48)), <- Z.land_assoc.
change (Z.land (Z.ones 52) _) with (Z.ones 48).
rewrite (Z.land_comm _ (Z.ones 48)).
rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by (rewrite Z.land_assoc, Z.land_ldiff; apply Z.land_0_l).
rewrite (Z.land_comm (Z.ones 48)), Z.ldiff_ones_r, Z.shiftr_land by lia.
change ((Z.shiftr (Z.ones 52) 48)) with (Z.ones 4).
fold tx.
rewrite Z.shiftl_mul_pow2, Z.land_ones by lia.
fold t4.
replace (2 ^ 156 * t3 + 2 ^ 208 * (2 ^ 52 * (d1 / 2 ^ 52) + (tx * 2 ^ 48 + t4)) + 2 ^ 260 * p5)
 with (2 ^ 156 * t3 + 2 ^ 208 * t4 + ((2^4 * ((d1 / 2 ^ 52) + p5) + tx) * 2 ^ 256))
 by ring.
fold d2.
rewrite (Z.div_mod d2 (2^52)) by lia.
replace (2 ^ 156 * t3 + 2 ^ 208 * t4 + (2 ^ 4 * (2 ^ 52 * (d2 / 2 ^ 52) + d2 mod 2 ^ 52) + tx) * 2 ^ 256
     + p0 + 2 ^ 312 * p6)
 with (2 ^ 156 * t3 + 2 ^ 208 * t4 + (p0 + ((d2 mod 2 ^ 52) * 2 ^ 4 + tx) * 2 ^ 256)
     + 2 ^ 312 * (d2 / 2 ^ 52 + p6))
 by ring.
setoid_rewrite HR.
fold c0 d3.
set (X := secp256k1_fe_array.from_array _).
rewrite (Z.div_mod c0 (2^52)), (Z.div_mod d3 (2^52)) by lia.
replace (2 ^ 156 * t3 + 2 ^ 208 * t4 + (2 ^ 52 * (c0 / 2 ^ 52) + c0 mod 2 ^ 52)
     + 2 ^ 312 * (2 ^ 52 * (d3 / 2 ^ 52) + d3 mod 2 ^ 52) + 2 ^ 52 * p1 + 2 ^ 364 * p7)
 with (2 ^ 156 * t3 + 2 ^ 208 * t4 + c0 mod 2 ^ 52
     + 2 ^ 52 * (c0 / 2 ^ 52 + p1 + (d3 mod 2 ^ 52) * (2^256 * 2^4)) + 2 ^ 364 * ((d3 / 2 ^ 52) + p7))
 by ring.
setoid_rewrite HR.
fold c1 d4.
rewrite (Z.div_mod c1 (2^52)), (Z.div_mod d4 (2^64)) by lia.
replace (2 ^ 156 * t3 + 2 ^ 208 * t4 + c0 mod 2 ^ 52 + 2 ^ 52 * (2 ^ 52 * (c1 / 2 ^ 52) + c1 mod 2 ^ 52)
     + 2 ^ 364 * (2 ^ 64 * (d4 / 2 ^ 64) + d4 mod 2 ^ 64) + 2 ^ 104 * p2)
 with (2 ^ 156 * (t3 + 2^256 * 2^16 * (d4 / 2 ^ 64)) + 2 ^ 208 * t4 + c0 mod 2 ^ 52 + 2 ^ 52 * (c1 mod 2 ^ 52)
     + 2 ^ 104 * (c1 / 2 ^ 52 + p2 + (2^256 * 2^4) * (d4 mod 2 ^ 64)))
 by ring.
setoid_rewrite HR.
fold c2 d5.
rewrite (Z.div_mod c2 (2^52)) by lia.
replace (2 ^ 156 * (t3 + secp256k1_R * 2 ^ 16 * d5) + 2 ^ 208 * t4
     + c0 mod 2 ^ 52 + 2 ^ 52 * (c1 mod 2 ^ 52) + 2 ^ 104 * (2 ^ 52 * (c2 / 2 ^ 52) + c2 mod 2 ^ 52))
 with (2 ^ 156 * (c2 / 2 ^ 52 + secp256k1_R * 2 ^ 16 * d5+ t3 ) + 2 ^ 208 * t4
     + c0 mod 2 ^ 52 + 2 ^ 52 * (c1 mod 2 ^ 52) + 2 ^ 104 * (c2 mod 2 ^ 52))
  by ring.
fold c3.
rewrite (Z.div_mod c3 (2^52)) by lia.
fold c4.
unfold eqm, X.
f_equal.
simpl.
rewrite !Z.shiftl_mul_pow2 by lia.
ring.
Qed.

End Dettman.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog := ltac:(with_library prog
  [secp256k1_u128_mul_spec
  ;secp256k1_u128_accum_mul_spec
  ;secp256k1_u128_accum_u64_spec
  ;secp256k1_u128_rshift_spec
  ;secp256k1_u128_to_u64_spec
  ;secp256k1_u128_hi_u64_spec
  ;secp256k1_u128_from_u64_spec
  ;secp256k1_u128_check_bits_spec
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

  ;secp256k1_fe_mul_inner_spec
  ;secp256k1_fe_sqr_inner_spec
  ]).

Ltac forward_verify_bits_128 := forward_verify_check;
[forward_call;elim Z.ltb_spec0;[intros _|lia];
 forward_if;[discriminate|forward;entailer!!]
|].

Lemma body_secp256k1_fe_mul_inner: semax_body Vprog Gprog f_secp256k1_fe_mul_inner secp256k1_fe_mul_inner_spec.
Proof.
start_function.
destruct arra as [|a0 [|a1 [|a2 [|a3 [|a4 [|]]]]]]; try discriminate.
destruct arrb as [|b0 [|b1 [|b2 [|b3 [|b4 [|]]]]]]; try discriminate.
clear H H0.
destruct H1 as [H1 Ha4a].
inversion_clear H1 as [|x y Ha0 H].
inversion_clear H as [|x y Ha1 H0].
inversion_clear H0 as [|x y Ha2 H].
inversion_clear H as [|x y Ha3 H0].
inversion_clear H0 as [|x y [Ha4b _] _].
destruct H2 as [H2 Hb4a].
inversion_clear H2 as [|x y Hb0 H].
inversion_clear H as [|x y Hb1 H0].
inversion_clear H0 as [|x y Hb2 H].
inversion_clear H as [|x y Hb3 H0].
inversion_clear H0 as [|x y [Hb4b _] _].
simpl (nth _ _ _) in Ha4a, Hb4a.
assert (Ha4 := conj Ha4b Ha4a);
assert (Hb4 := conj Hb4b Hb4a);
clear Ha4a Ha4b Hb4a Hb4b.
change (Z.ones 52) with (2^52 - 1) in *|-.
change (Z.ones 48) with (2^48 - 1) in *|-.
do 5 (forward; unfold Znth; simpl (Int64.repr _)).
do 2 forward.
do 10 (forward_verify_check;
[forward; unfold Znth; simpl (Int64.repr _);
 forward_if;
 [revert H;
  convert_C_to_math;
  rewrite shiftr_small, Z.eqb_refl by lia;
  discriminate
 |forward; entailer!]
|]).
assert_PROP (a <> b) as Hab.
1:{
 destruct (Val.eq a b) as [->|Hneq];[|entailer!].
 sep_apply data_at_conflict_glb.
 entailer.
}
assert_PROP ((withOption a fst r) <> b) as Hrb.
1:{
 destruct r as [[r shr]|];[|entailer!].
 destruct (Val.eq r b) as [->|Hneq];[|entailer!].
 assert (nonempty_share (Share.glb shr shb)) by
  (apply nonempty_writable_glb; assumption).
 simpl (withOption _ _ _).
 rewrite !data_at__eq.
 sep_apply (data_at_conflict_glb shr shb).
 entailer!.
}
assert_PROP (isptr (withOption a fst r)) as Hptrr by
 (destruct r as [[r shr]|];simpl (withOption _ _ _) in *;entailer!).
assert_PROP (isptr a) as Hptra by entailer!.
assert_PROP (isptr b) as Hptrb by entailer!.
forward_verify_check.
1:{
 forward_if;
 [destruct r as [[r shr]|];simpl (withOption _ _ _) in *;entailer!
 | |forward;entailer!].
 revert H.
 rewrite force_sem_cmp_pp by assumption.
 destruct (eq_dec _ _);[congruence|discriminate].
}
forward_verify_check.
1:{
 revert H.
 rewrite force_sem_cmp_pp by assumption.
 destruct (eq_dec _ _);[congruence|discriminate].
}
assert (Hswap : withOption emp (fun '(v, sh) => data_at_ sh (tarray tulong 5) v) r *
   data_at sha (tarray tulong 5)
     (map (fun x : Z => Vlong (Int64.repr x)) [a0; a1; a2; a3; a4]) a
 |-- data_at_ (withOption sha snd r) (tarray tulong 5) (withOption a fst r) *
      withOption emp (fun _ => (data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) [a0; a1; a2; a3; a4]) a)) r)
 by (destruct r as [[r shr]|]; simpl (withOption _ _ _) in *;entailer!).
sep_apply Hswap.
Intros.
clear Hswap.
do 4 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
drop_LOCALs [_t'101; _t'102; _t'103; _t'104].
set (p3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0).
assert (Hp3 : 0 <= p3 < 2^114).
1:{
  assert (Ha0b3 := umul_bounds_tight _ _ _ _ Ha0 Hb3).
  assert (Ha1b2 := umul_bounds_tight _ _ _ _ Ha1 Hb2).
  assert (Ha2b1 := umul_bounds_tight _ _ _ _ Ha2 Hb1).
  assert (Ha3b0 := umul_bounds_tight _ _ _ _ Ha3 Hb0).
  lia.
}
forward_verify_bits_128.
do 1 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
drop_LOCALs [_t'99].
set (p8 := a4 * b4).
assert (Hp8 : 0 <= p8 <= 2^112 - 1).
1:{
  assert (Ha4b4 := umul_bounds_tight _ _ _ _ Ha4 Hb4).
  lia.
}
forward_verify_bits_128.
forward_call.
rewrite <-(Int64.repr_unsigned (Int64.repr p8)), Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
forward_call;[apply Z.mod_pos_bound; rep_lia|].
change (68719492368) with (16*secp256k1_R).
drop_LOCALs [_t'3].
set (d0 := p3 + 16 * secp256k1_R * (p8 mod 2^64)).
forward_call;[unfold Int128_modulus; lia|].
assert (Hd0 : 0 <= d0 <= 2^115 - 1).
1:{
 assert (Hmod := Z.mod_pos_bound p8 (2^64)).
 unfold d0, secp256k1_R.
 lia.
}
forward_verify_bits_128.
assert (Hp864 : 0 <= Z.shiftr p8 64 <= 2^48 - 1) by solve_bounds.
forward_verify_bits_128.
change 4503599627370495 with (Z.ones 52).
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 fold p3; change (p3 + _) with d0.
 clearbody d0.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd052 : 0 <= Z.shiftr d0 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
do 5 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr d0 52) _).
drop_LOCALs [_t'89; _t'90; _t'91; _t'92; _t'93; _t'6].
set (p4 := a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0).
assert (Hp4 : 0 <= Z.shiftr d0 52 + p4 < 2^115).
1:{
  assert (Ha0b4 := umul_bounds_tight _ _ _ _ Ha0 Hb4).
  assert (Ha1b3 := umul_bounds_tight _ _ _ _ Ha1 Hb3).
  assert (Ha2b2 := umul_bounds_tight _ _ _ _ Ha2 Hb2).
  assert (Ha3b1 := umul_bounds_tight _ _ _ _ Ha3 Hb1).
  assert (Ha4b0 := umul_bounds_tight _ _ _ _ Ha4 Hb0).
  lia.
}
forward_verify_bits_128.
forward_call.
forward_call;[rewrite Z.shiftl_mul_pow2; rep_lia|].
change (Z.shiftl _ _) with (2^16 * secp256k1_R).
drop_LOCALs [_t'9].
set (d1 := Z.shiftr d0 52 + p4 + 2^16 * secp256k1_R * (Z.shiftr p8 64)).
assert (Hd1 : 0 <= d1 <= 2^116 - 1).
1:{
 unfold d1, secp256k1_R.
 lia.
}
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ _ + _ + _) with d1.
 clearbody d1.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd152 : 0 <= Z.shiftr d1 52 <= 2^64 - 1) by solve_bounds.
forward_verify_bits_128.
forward.
drop_LOCALs [_t'11].
set (tx := Z.shiftr (d1 mod 2^52) 48).
replace (_ (Int64.repr (d1 mod 2 ^ 52)) _) with (Int64.repr tx) by
  (clearbody d1; convert_C_to_math; reflexivity).
forward.
set (t4 := d1 mod 2^48).
replace (Int64.and _ _) with (Int64.repr t4).
2:{
  clearbody d1; convert_C_to_math.
  change (Z.shiftr (Z.ones 52) 4) with (Z.ones 48).
  rewrite <- Z.land_ones, <- Z.land_assoc by lia.
  change (Z.land (Z.ones 52) (Z.ones 48)) with (Z.ones 48).
  rewrite Z.land_ones by lia.
  reflexivity.
}
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ 48) with tx.
 clearbody d1.
 convert_C_to_math.
 unfold tx.
 rewrite Z.shiftr_shiftr, Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
forward_verify_check.
1:{
 revert H.
 change (_ mod 2^48) with t4.
 clearbody d1.
 convert_C_to_math.
 unfold t4.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
unfold secp256k1_uint128_at at 2.
sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128 (Vlong (Int64.repr (Z.shiftr p8 64)),
     Vlong (Int64.repr (Z.shiftr (Z.shiftr p8 64) 64))) v_c).
do 1 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
drop_LOCALs [_t'82].
set (p0 := a0 * b0).
assert (Hp0 : 0 <= p0 <= 2^112 - 1).
1:{
  assert (Ha0b0 := umul_bounds_tight _ _ _ _ Ha0 Hb0).
  lia.
}
forward_verify_bits_128.
do 4 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr d1 52) _).
drop_LOCALs [_t'77; _t'78; _t'79; _t'80].
set (p5 := a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1).
set (d2 := Z.shiftr d1 52 + p5).
assert (Hd2 : 0 <= d2 < 2^114).
1:{
  assert (Ha1b4 := umul_bounds_tight _ _ _ _ Ha1 Hb4).
  assert (Ha2b3 := umul_bounds_tight _ _ _ _ Ha2 Hb3).
  assert (Ha3b2 := umul_bounds_tight _ _ _ _ Ha3 Hb2).
  assert (Ha4b1 := umul_bounds_tight _ _ _ _ Ha4 Hb1).
  lia.
}
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ _ + _) with d2.
 clearbody d2.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd252 : 0 <= Z.shiftr d2 52 <= 2^62 - 1) by solve_bounds.
forward_verify_bits_128.
forward.
drop_LOCALs [_t'15].
set (u0 := Z.lor (d2 mod 2^52 * 2^4) tx).
replace (Int64.or _ _) with (Int64.repr u0) by
  (clearbody d2; convert_C_to_math; reflexivity).
assert (Htx : 0 <= tx <= 2^56 - 1).
1:{
 unfold tx.
 solve_bounds.
}
assert (Hu0 : 0 <= u0 <= 2^56 - 1).
1:{
 assert (Hd2mod : 0 <= d2 mod 2 ^ 52 < 2 ^ 52) by (apply Z.mod_pos_bound; lia).
 unfold u0.
 split;[apply Z.lor_nonneg; lia|].
 destruct (Z_le_lt_dec (Z.lor (d2 mod 2 ^ 52 * 2 ^ 4) tx) 0);[lia|].
 cut (Z.lor (d2 mod 2 ^ 52 * 2 ^ 4) tx < 2 ^ 56);[lia|].
 rewrite Z.log2_lt_pow2, Z.log2_lor by lia.
 apply Z.max_lub_lt.
 * destruct (Z_le_lt_eq_dec _ _ (proj1 Hd2mod)) as [X| <-];[|simpl;lia].
   rewrite <-Z.log2_lt_pow2; lia.
 * destruct (Z_le_lt_eq_dec _ _ (proj1 Htx)) as [X| <-];[|simpl;lia].
   rewrite <-Z.log2_lt_pow2; lia.
}
forward_verify_check.
1:{
 revert H.
 change (Z.lor _ _) with u0.
 clearbody d2.
 convert_C_to_math.
 rewrite shiftr_small, Z.eqb_refl by lia.
 discriminate.
}
forward_call;[change (Z.shiftr _ _) with secp256k1_R; unfold secp256k1_R; rep_lia|].
set (c0 := p0 + u0 * secp256k1_R).
replace (p0 + _) with c0 by
  (clearbody u0; convert_C_to_math; reflexivity).
assert (Hc0 : 0 <= c0 < 2^113) by (unfold c0, secp256k1_R;lia).
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
drop_LOCALs [_t'18].
set (r0 := c0 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (a0 * b0 + _) with c0.
 clearbody c0.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc052 : 0 <= Z.shiftr c0 52 <= 2^61 - 1) by (unfold secp256k1_R in c0; solve_bounds).
forward_verify_bits_128.
do 2 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr c0 52) _).
drop_LOCALs [_t'67; _t'68].
set (p1 := a0 * b1 + a1 * b0).
assert (Hp1 : 0 <= Z.shiftr c0 52 + p1 < 2^114).
1:{
  assert (Ha0b1 := umul_bounds_tight _ _ _ _ Ha0 Hb1).
  assert (Ha1b0 := umul_bounds_tight _ _ _ _ Ha1 Hb0).
  lia.
}
forward_verify_bits_128.
do 3 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr d2 52) _).
drop_LOCALs [_t'63; _t'64; _t'65].
set (p6 := a2 * b4 + a3 * b3 + a4 * b2).
set (d3 := Z.shiftr d2 52 + p6).
assert (Hd3 : 0 <= d3 < 2^114).
1:{
  assert (Ha2b4 := umul_bounds_tight _ _ _ _ Ha2 Hb4).
  assert (Ha3b3 := umul_bounds_tight _ _ _ _ Ha3 Hb3).
  assert (Ha4b2 := umul_bounds_tight _ _ _ _ Ha4 Hb2).
  lia.
}
forward_verify_bits_128.
forward_call.
forward_call.
1:{
  clearbody d3.
  convert_C_to_math.
  rewrite <- Z.land_ones, <- Z.land_assoc by lia.
  change (Z.land (Z.ones 64) (Z.ones 52)) with (Z.ones 52).
  rewrite Z.land_ones by lia.
  assert (Hmod := Z.mod_pos_bound d3 (2^52)).
  lia.
}
drop_LOCALs [_t'22].
set (c1 := Z.shiftr c0 52 + p1 + (d3 mod 2^52) * (secp256k1_R * 2^4)).
replace (_ + _ * 68719492368) with c1.
2:{
 clearbody c0 d3.
 convert_C_to_math.
 rewrite <- Z.land_ones, <- Z.land_assoc by lia.
 change (Z.land (Z.ones 64) (Z.ones 52)) with (Z.ones 52).
 rewrite Z.land_ones by lia.
 reflexivity.
}
forward_call;[unfold Int128_modulus; lia|].
assert (Hd3mod : 0 <= d3 mod 2^52 <= 2^52 - 1) by solve_bounds.
assert (Hc1 : 0 <= c1 < 2^115) by (unfold c1, secp256k1_R;lia).
assert (Hd352 : 0 <= Z.shiftr d3 52 <= 2^62 - 1) by solve_bounds.
forward_verify_bits_128.
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
drop_LOCALs [_t'25].
set (r1 := c1 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + _ * (secp256k1_R * 2 ^ 4)) with c1.
 clearbody c1.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc152 : 0 <= Z.shiftr c1 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
do 3 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr c1 52) _).
drop_LOCALs [_t'54; _t'55; _t'56].
set (p2 := a0 * b2 + a1 * b1 + a2 * b0).
assert (Hp2 : 0 <= Z.shiftr c1 52 + p2 < 2^114).
1:{
  assert (Ha0b2 := umul_bounds_tight _ _ _ _ Ha0 Hb2).
  assert (Ha1b1 := umul_bounds_tight _ _ _ _ Ha1 Hb1).
  assert (Ha2b0 := umul_bounds_tight _ _ _ _ Ha2 Hb0).
  lia.
}
forward_verify_bits_128.
do 2 (forward; unfold Znth; simpl (Int64.repr _);forward_call).
rewrite <-!(Z.add_assoc (Z.shiftr d3 52) _).
drop_LOCALs [_t'51; _t'52].
set (p7 := a3 * b4 + a4 * b3).
set (d4 := Z.shiftr d3 52 + p7).
assert (Hd4 : 0 <= d4 < 2^114).
1:{
  assert (Ha3b4 := umul_bounds_tight _ _ _ _ Ha3 Hb4).
  assert (Ha4b3 := umul_bounds_tight _ _ _ _ Ha4 Hb3).
  lia.
}
forward_verify_bits_128.
forward_call.
rewrite <-(Int64.repr_unsigned (Int64.repr d4)), Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
forward_call;[apply Z.mod_pos_bound; rep_lia|].
drop_LOCALs [_t'29].
set (c2 := Z.shiftr c1 52 + p2 + (secp256k1_R * 2^4) * (d4 mod 2^64)).
change (_ + 68719492368 * _) with c2.
forward_call;[unfold Int128_modulus; lia|].
set (d5 := Z.shiftr d4 64).
assert (Hd4mod : 0 <= d4 mod 2^64 <= 2^64 - 1) by solve_bounds.
assert (Hc2 : 0 <= c2 < 2^115) by (unfold c2, secp256k1_R;lia).
assert (Hd5 : 0 <= d5 <= 2^50 - 1) by solve_bounds.
forward_verify_bits_128.
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
drop_LOCALs [_t'32].
set (r2 := c2 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + (secp256k1_R * 2 ^ 4) * _) with c2.
 clearbody c2; clear -c2.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc252 : 0 <= Z.shiftr c2 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
forward_call.
forward_call;[rewrite Z.shiftl_mul_pow2; rep_lia|].
assert (Hd0mod : 0 <= d0 mod 2^52 <= 2^52 - 1) by solve_bounds.
forward_call.
drop_LOCALs [_t'34].
set (c3 := Z.shiftr c2 52 + (secp256k1_R * 2^16) * d5 + d0 mod 2^52).
change (_ + d0 mod 2^52) with c3.
assert (Hc3 : 0 <= c3 < 2^100) by (unfold c3, secp256k1_R; lia).
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
drop_LOCALs [_t'36].
set (r3 := c3 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + _ mod 2^52) with c3.
 clearbody c3; clear -c3.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
set (c4 := Z.shiftr c3 52).
assert (Hc4 : 0 <= c4 <= 2^48 - 1) by (unfold c4;solve_bounds).
forward_verify_bits_128.
forward_call.
forward.
rewrite add64_repr.
drop_LOCALs [_t'38].
set (r4 := c4 + t4).
assert (Ht4 : 0 <= t4 <= 2^48 - 1) by (unfold t4;solve_bounds).
assert (Hr4 : 0 <= r4 <= 2^49 - 1) by (unfold r4;solve_bounds).
forward_verify_check.
forward.
match goal with
| |- semax _ ?E _ _ => forward_if E;[|forward;entailer!|]
end.
1:{
 revert H.
 change (_ + _ mod 2^48) with r4.
 clearbody r4; clear -r4 Hr4.
 convert_C_to_math.
 rewrite shiftr_small, Z.eqb_refl by lia.
 discriminate.
}
drop_LOCALs [_t'39].
set (arrr :=  [r0; r1; r2; r3; r4]).
change (upd_Znth 4 _ _) with (map (fun x : Z => Vlong (Int64.repr x)) arrr).
assert (Hr0 : 0 <= r0 <= 2^52 - 1) by (unfold r0; solve_bounds).
assert (Hr1 : 0 <= r1 <= 2^52 - 1) by (unfold r1; solve_bounds).
assert (Hr2 : 0 <= r2 <= 2^52 - 1) by (unfold r2; solve_bounds).
assert (Hr3 : 0 <= r3 <= 2^52 - 1) by (unfold r3; solve_bounds).
assert (Harrr : secp256k1_fe_array.boundBy 1 arrr) by
  (repeat constructor;try solve [simpl;rewrite ?Z.ones_equiv, <- ?Z.sub_1_r;lia]).
assert (eqm secp256k1_P
        (secp256k1_fe_array.from_array [a0; a1; a2; a3; a4]
           * secp256k1_fe_array.from_array [b0; b1; b2; b3; b4])
        (secp256k1_fe_array.from_array arrr)).
1:{
 change arrr with (dettman_reduce p0 p1 p2 p3 p4 p5 p6 p7 p8).
 rewrite <- secp256k1_fe_array.mul_spec.
 apply eqm_sym.
 eapply eqm_trans;[apply dettman_reduce_spec|].
 replace (secp256k1_fe_array.mul _ _) with [p0; p1; p2; p3; p4; p5; p6; p7; p8];[apply eqm_refl|].
 unfold p0, p1, p2, p3, p4, p5, p6, p7, p8.
 simpl;repeat apply (f_equal2 (@cons Z)); try ring.
 reflexivity.
}
forward.
unfold secp256k1_uint128_at.
Exists arrr.
entailer!!.
Qed.

Lemma body_secp256k1_fe_sqr_inner: semax_body Vprog Gprog f_secp256k1_fe_sqr_inner secp256k1_fe_sqr_inner_spec.
Proof.
start_function.
destruct arra as [|a0 [|a1 [|a2 [|a3 [|a4 [|]]]]]]; try discriminate.
clear H.
destruct H0 as [H1 Ha4a].
inversion_clear H1 as [|x y Ha0 H].
inversion_clear H as [|x y Ha1 H0].
inversion_clear H0 as [|x y Ha2 H].
inversion_clear H as [|x y Ha3 H0].
inversion_clear H0 as [|x y [Ha4b _] _].
simpl (nth _ _ _) in Ha4a.
assert (Ha4 := conj Ha4b Ha4a); clear Ha4a Ha4b.
change (Z.ones 52) with (2^52 - 1) in *|-.
change (Z.ones 48) with (2^48 - 1) in *|-.
do 5 (forward; unfold Znth; simpl (Int64.repr _)).
do 2 forward.
do 5 (forward_verify_check;
[forward; unfold Znth; simpl (Int64.repr _);
 forward_if;
 [revert H;
  convert_C_to_math;
  rewrite shiftr_small, Z.eqb_refl by lia;
  discriminate
 |forward; entailer!]
|]).
assert (Hswap : withOption emp (fun '(v, sh) => data_at_ sh (tarray tulong 5) v) r *
   data_at sha (tarray tulong 5)
     (map (fun x : Z => Vlong (Int64.repr x)) [a0; a1; a2; a3; a4]) a
 |-- data_at_ (withOption sha snd r) (tarray tulong 5) (withOption a fst r) *
      withOption emp (fun _ => (data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) [a0; a1; a2; a3; a4]) a)) r)
 by (destruct r as [[r shr]|]; simpl (withOption _ _ _) in *;entailer!).
sep_apply Hswap.
Intros.
clear Hswap.
do 2 (forward_call;try rep_lia;convert_C_to_math).
set (p3 := a0 * 2 * a3 + a1 * 2 * a2).
assert (Hp3 : 0 <= p3 < 2^114).
1:{
  assert (Ha0a3 := umul_bounds_tight _ _ _ _ Ha0 Ha3).
  assert (Ha1a2 := umul_bounds_tight _ _ _ _ Ha1 Ha2).
  lia.
}
forward_verify_bits_128.
do 1 (forward_call;try rep_lia;convert_C_to_math).
set (p8 := a4 * a4).
assert (Hp8 : 0 <= p8 <= 2^112 - 1).
1:{
  assert (Ha4a4 := umul_bounds_tight _ _ _ _ Ha4 Ha4).
  lia.
}
forward_verify_bits_128.
forward_call.
rewrite <-(Int64.repr_unsigned (Int64.repr p8)), Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
forward_call;[apply Z.mod_pos_bound; rep_lia|].
change (68719492368) with (16*secp256k1_R).
set (d0 := p3 + 16 * secp256k1_R * (p8 mod 2^64)).
forward_call;[unfold Int128_modulus; lia|].
assert (Hd0 : 0 <= d0 <= 2^115 - 1).
1:{
 assert (Hmod := Z.mod_pos_bound p8 (2^64)).
 unfold d0, secp256k1_R.
 lia.
}
forward_verify_bits_128.
assert (Hp864 : 0 <= Z.shiftr p8 64 <= 2^48 - 1) by solve_bounds.
forward_verify_bits_128.
change 4503599627370495 with (Z.ones 52).
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 fold p3; change (p3 + _) with d0.
 clearbody d0.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd052 : 0 <= Z.shiftr d0 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
forward.
do 3 (forward_call;try rep_lia;convert_C_to_math).
rewrite <-!(Z.add_assoc (Z.shiftr d0 52) _).
set (p4 := a0 * (a4 * 2) + a1 * 2 * a3 + a2 * a2).
assert (Hp4 : 0 <= Z.shiftr d0 52 + p4 < 2^115).
1:{
  assert (Ha0a4 := umul_bounds_tight _ _ _ _ Ha0 Ha4).
  assert (Ha1a3 := umul_bounds_tight _ _ _ _ Ha1 Ha3).
  assert (Ha2a2 := umul_bounds_tight _ _ _ _ Ha2 Ha2).
  lia.
}
forward_verify_bits_128.
forward_call.
forward_call;[rewrite Z.shiftl_mul_pow2; rep_lia|].
change (Z.shiftl _ _) with (2^16 * secp256k1_R).
set (d1 := Z.shiftr d0 52 + p4 + 2^16 * secp256k1_R * (Z.shiftr p8 64)).
assert (Hd1 : 0 <= d1 <= 2^116 - 1).
1:{
 unfold d1, secp256k1_R.
 lia.
}
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ _ + _ + _) with d1.
 clearbody d1.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd152 : 0 <= Z.shiftr d1 52 <= 2^64 - 1) by solve_bounds.
forward_verify_bits_128.
forward.
set (tx := Z.shiftr (d1 mod 2^52) 48).
replace (_ (Int64.repr (d1 mod 2 ^ 52)) _) with (Int64.repr tx) by
  (clearbody d1; convert_C_to_math; reflexivity).
forward.
set (t4 := d1 mod 2^48).
replace (Int64.and _ _) with (Int64.repr t4).
2:{
  clearbody d1; convert_C_to_math.
  change (Z.shiftr (Z.ones 52) 4) with (Z.ones 48).
  rewrite <- Z.land_ones, <- Z.land_assoc by lia.
  change (Z.land (Z.ones 52) (Z.ones 48)) with (Z.ones 48).
  rewrite Z.land_ones by lia.
  reflexivity.
}
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ 48) with tx.
 clearbody d1.
 convert_C_to_math.
 unfold tx.
 rewrite Z.shiftr_shiftr, Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
forward_verify_check.
1:{
 revert H.
 change (_ mod 2^48) with t4.
 clearbody d1.
 convert_C_to_math.
 unfold t4.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
unfold secp256k1_uint128_at at 2.
sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128 (Vlong (Int64.repr (Z.shiftr p8 64)),
     Vlong (Int64.repr (Z.shiftr (Z.shiftr p8 64) 64))) v_c).
do 1 (forward_call;try rep_lia;convert_C_to_math).
set (p0 := a0 * a0).
assert (Hp0 : 0 <= p0 <= 2^112 - 1).
1:{
  assert (Ha0a0 := umul_bounds_tight _ _ _ _ Ha0 Ha0).
  lia.
}
forward_verify_bits_128.
do 2 (forward_call;try rep_lia;convert_C_to_math).
rewrite <-!(Z.add_assoc (Z.shiftr d1 52) _).
set (p5 := a1 * (a4 * 2) + a2 * 2 * a3).
set (d2 := Z.shiftr d1 52 + p5).
assert (Hd2 : 0 <= d2 < 2^114).
1:{
  assert (Ha1a4 := umul_bounds_tight _ _ _ _ Ha1 Ha4).
  assert (Ha2a3 := umul_bounds_tight _ _ _ _ Ha2 Ha3).
  lia.
}
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 revert H.
 change (Z.shiftr _ _ + _) with d2.
 clearbody d2.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hd252 : 0 <= Z.shiftr d2 52 <= 2^62 - 1) by solve_bounds.
forward_verify_bits_128.
forward.
set (u0 := Z.lor (d2 mod 2^52 * 2^4) tx).
replace (Int64.or _ _) with (Int64.repr u0) by
  (clearbody d2; convert_C_to_math; reflexivity).
assert (Htx : 0 <= tx <= 2^56 - 1).
1:{
 unfold tx.
 solve_bounds.
}
assert (Hu0 : 0 <= u0 <= 2^56 - 1).
1:{
 assert (Hd2mod : 0 <= d2 mod 2 ^ 52 < 2 ^ 52) by (apply Z.mod_pos_bound; lia).
 unfold u0.
 split;[apply Z.lor_nonneg; lia|].
 destruct (Z_le_lt_dec (Z.lor (d2 mod 2 ^ 52 * 2 ^ 4) tx) 0);[lia|].
 cut (Z.lor (d2 mod 2 ^ 52 * 2 ^ 4) tx < 2 ^ 56);[lia|].
 rewrite Z.log2_lt_pow2, Z.log2_lor by lia.
 apply Z.max_lub_lt.
 * destruct (Z_le_lt_eq_dec _ _ (proj1 Hd2mod)) as [X| <-];[|simpl;lia].
   rewrite <-Z.log2_lt_pow2; lia.
 * destruct (Z_le_lt_eq_dec _ _ (proj1 Htx)) as [X| <-];[|simpl;lia].
   rewrite <-Z.log2_lt_pow2; lia.
}
forward_verify_check.
1:{
 revert H.
 change (Z.lor _ _) with u0.
 clearbody d2.
 convert_C_to_math.
 rewrite shiftr_small, Z.eqb_refl by lia.
 discriminate.
}
forward_call;[change (Z.shiftr _ _) with secp256k1_R; unfold secp256k1_R; rep_lia|].
set (c0 := p0 + u0 * secp256k1_R).
replace (p0 + _) with c0 by
  (clearbody u0; convert_C_to_math; reflexivity).
assert (Hc0 : 0 <= c0 < 2^113) by (unfold c0, secp256k1_R;lia).
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
drop_LOCALs [_t'18; _t'15; _t'11; _t'9; _t'6; _t'3].
set (r0 := c0 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (a0 * a0 + _) with c0.
 clearbody c0.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc052 : 0 <= Z.shiftr c0 52 <= 2^61 - 1) by (unfold secp256k1_R in c0; solve_bounds).
forward_verify_bits_128.
forward.
do 1 (forward_call;try rep_lia;convert_C_to_math).
set (p1 := a0 * 2 * a1).
assert (Hp1 : 0 <= Z.shiftr c0 52 + p1 < 2^114).
1:{
  assert (Ha0a1 := umul_bounds_tight _ _ _ _ Ha0 Ha1).
  lia.
}
forward_verify_bits_128.
do 2 (forward_call;try rep_lia;convert_C_to_math).
rewrite <-!(Z.add_assoc (Z.shiftr d2 52) _).
set (p6 := a2 * (a4 * 2) + a3 * a3).
set (d3 := Z.shiftr d2 52 + p6).
assert (Hd3 : 0 <= d3 < 2^114).
1:{
  assert (Ha2a4 := umul_bounds_tight _ _ _ _ Ha2 Ha4).
  assert (Ha3a3 := umul_bounds_tight _ _ _ _ Ha3 Ha3).
  lia.
}
forward_verify_bits_128.
forward_call.
forward_call.
1:{
  clearbody d3.
  convert_C_to_math.
  rewrite <- Z.land_ones, <- Z.land_assoc by lia.
  change (Z.land (Z.ones 64) (Z.ones 52)) with (Z.ones 52).
  rewrite Z.land_ones by lia.
  assert (Hmod := Z.mod_pos_bound d3 (2^52)).
  lia.
}
set (c1 := Z.shiftr c0 52 + p1 + (d3 mod 2^52) * (secp256k1_R * 2^4)).
replace (_ + _ * 68719492368) with c1.
2:{
 clearbody c0 d3.
 convert_C_to_math.
 rewrite <- Z.land_ones, <- Z.land_assoc by lia.
 change (Z.land (Z.ones 64) (Z.ones 52)) with (Z.ones 52).
 rewrite Z.land_ones by lia.
 reflexivity.
}
forward_call;[unfold Int128_modulus; lia|].
assert (Hd3mod : 0 <= d3 mod 2^52 <= 2^52 - 1) by solve_bounds.
assert (Hc1 : 0 <= c1 < 2^115) by (unfold c1, secp256k1_R;lia).
assert (Hd352 : 0 <= Z.shiftr d3 52 <= 2^62 - 1) by solve_bounds.
forward_verify_bits_128.
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
set (r1 := c1 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + _ * (secp256k1_R * 2 ^ 4)) with c1.
 clearbody c1.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc152 : 0 <= Z.shiftr c1 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
do 2 (forward_call;try rep_lia;convert_C_to_math).
rewrite <-!(Z.add_assoc (Z.shiftr c1 52) _).
set (p2 := a0 * 2 * a2 + a1 * a1).
assert (Hp2 : 0 <= Z.shiftr c1 52 + p2 < 2^114).
1:{
  assert (Ha0a2 := umul_bounds_tight _ _ _ _ Ha0 Ha2).
  assert (Ha1a1 := umul_bounds_tight _ _ _ _ Ha1 Ha1).
  lia.
}
forward_verify_bits_128.
do 1 (forward_call;try rep_lia;convert_C_to_math).
set (p7 := a3 * (a4 * 2)).
set (d4 := Z.shiftr d3 52 + p7).
assert (Hd4 : 0 <= d4 < 2^114).
1:{
  assert (Ha3a4 := umul_bounds_tight _ _ _ _ Ha3 Ha4).
  lia.
}
forward_verify_bits_128.
forward_call.
rewrite <-(Int64.repr_unsigned (Int64.repr d4)), Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
forward_call;[apply Z.mod_pos_bound; rep_lia|].
set (c2 := Z.shiftr c1 52 + p2 + (secp256k1_R * 2^4) * (d4 mod 2^64)).
change (_ + 68719492368 * _) with c2.
forward_call;[unfold Int128_modulus; lia|].
set (d5 := Z.shiftr d4 64).
assert (Hd4mod : 0 <= d4 mod 2^64 <= 2^64 - 1) by solve_bounds.
assert (Hc2 : 0 <= c2 < 2^115) by (unfold c2, secp256k1_R;lia).
assert (Hd5 : 0 <= d5 <= 2^50 - 1) by solve_bounds.
forward_verify_bits_128.
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
set (r2 := c2 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + (secp256k1_R * 2 ^ 4) * _) with c2.
 clearbody c2; clear -c2.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
assert (Hc252 : 0 <= Z.shiftr c2 52 <= 2^63 - 1) by solve_bounds.
forward_verify_bits_128.
forward_call.
forward_call;[rewrite Z.shiftl_mul_pow2; rep_lia|].
assert (Hd0mod : 0 <= d0 mod 2^52 <= 2^52 - 1) by solve_bounds.
forward_call.
set (c3 := Z.shiftr c2 52 + (secp256k1_R * 2^16) * d5 + d0 mod 2^52).
change (_ + d0 mod 2^52) with c3.
assert (Hc3 : 0 <= c3 < 2^100) by (unfold c3, secp256k1_R; lia).
forward_verify_bits_128.
forward_call.
forward; rewrite and64_repr, Z.land_ones by lia.
set (r3 := c3 mod 2 ^ 52).
forward_call;[unfold Int128_modulus; lia|].
forward_verify_check.
1:{
 forward;forward_if;[exfalso|forward;entailer!].
 revert H.
 change (_ + _ mod 2^52) with c3.
 clearbody c3; clear -c3.
 convert_C_to_math.
 rewrite Z.shiftr_div_pow2, Zmod_div, Z.eqb_refl by lia.
 discriminate.
}
set (c4 := Z.shiftr c3 52).
assert (Hc4 : 0 <= c4 <= 2^48 - 1) by (unfold c4;solve_bounds).
forward_verify_bits_128.
forward_call.
forward.
rewrite add64_repr.
drop_LOCALs [_t'38; _t'36; _t'34; _t'32; _t'29; _t'25; _t'22].
set (r4 := c4 + t4).
assert (Ht4 : 0 <= t4 <= 2^48 - 1) by (unfold t4;solve_bounds).
assert (Hr4 : 0 <= r4 <= 2^49 - 1) by (unfold r4;solve_bounds).
forward_verify_check.
forward.
match goal with
| |- semax _ ?E _ _ => forward_if E;[|forward;entailer!|]
end.
1:{
 revert H.
 change (_ + _ mod 2^48) with r4.
 clearbody r4; clear -r4 Hr4.
 convert_C_to_math.
 rewrite shiftr_small, Z.eqb_refl by lia.
 discriminate.
}
drop_LOCALs [_t'39].
set (arrr :=  [r0; r1; r2; r3; r4]).
change (upd_Znth 4 _ _) with (map (fun x : Z => Vlong (Int64.repr x)) arrr).
assert (Hr0 : 0 <= r0 <= 2^52 - 1) by (unfold r0; solve_bounds).
assert (Hr1 : 0 <= r1 <= 2^52 - 1) by (unfold r1; solve_bounds).
assert (Hr2 : 0 <= r2 <= 2^52 - 1) by (unfold r2; solve_bounds).
assert (Hr3 : 0 <= r3 <= 2^52 - 1) by (unfold r3; solve_bounds).
assert (Harrr : secp256k1_fe_array.boundBy 1 arrr) by
  (repeat constructor;try solve [simpl;rewrite ?Z.ones_equiv, <- ?Z.sub_1_r;lia]).
assert (eqm secp256k1_P
        (secp256k1_fe_array.from_array [a0; a1; a2; a3; a4] ^ 2)
        (secp256k1_fe_array.from_array arrr)).
1:{
 change arrr with (dettman_reduce p0 p1 p2 p3 p4 p5 p6 p7 p8).
 rewrite Z.pow_2_r, <- secp256k1_fe_array.mul_spec.
 apply eqm_sym.
 eapply eqm_trans;[apply dettman_reduce_spec|].
 replace (secp256k1_fe_array.mul _ _) with [p0; p1; p2; p3; p4; p5; p6; p7; p8];[apply eqm_refl|].
 unfold p0, p1, p2, p3, p4, p5, p6, p7, p8.
 simpl;repeat apply (f_equal2 (@cons Z)); try ring.
 reflexivity.
}
forward.
unfold secp256k1_uint128_at.
Exists arrr.
entailer!!.
Qed.
