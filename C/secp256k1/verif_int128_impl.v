Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import int128_impl.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Lemma Z_shiftr_neg1_l: forall n : Z, 0 <= n -> Z.shiftr (-1) n = -1.
Proof.
apply natlike_rec.
 reflexivity.
intros x Hx Hrec.
rewrite <- Z.add_1_r, <- Z.shiftr_shiftr, Hrec by auto with zarith.
reflexivity.
Qed.

Lemma Int64_low_is_nonneg (x : Z) :
 Int64.min_signed <= x <= Int64.max_signed ->
 x mod 2 ^ 64 < 2^63 -> 0 <= x < 2^63.
Proof.
intros [Hx0 Hx1] Hxmod.
destruct (Z.neg_nonneg_cases x) as [Hneg|Hpos].
* apply Zlt_not_le in Hxmod.
  elim Hxmod.
  change x with (2^64 mod 2^64 + x).
  rewrite Zplus_mod_idemp_l.
  rewrite Z.mod_small; rep_lia.
* rewrite Z.mod_small in Hxmod; rep_lia.
Qed.

Lemma Int64_high_is_neg (x : Z) :
 Int64.min_signed <= x <= Int64.max_signed ->
 2^63 <= x mod 2 ^ 64 -> -2^63 <= x < 0.
Proof.
intros [Hx0 Hx1] Hxmod.
destruct (Z.neg_nonneg_cases x) as [Hneg|Hpos].
* change x with (2^64 mod 2^64 + x) in Hxmod.
  rewrite Zplus_mod_idemp_l in Hxmod.
  rewrite Z.mod_small in Hxmod; rep_lia.
* apply Zlt_not_le in Hxmod;[contradiction|].
  rewrite Z.mod_small; rep_lia.
Qed.

Lemma mul128_tight x y (Hx : Int64.min_signed <= x <= Int64.max_signed) 
                       (Hy : Int64.min_signed <= y <= Int64.max_signed) :
                   -2^126+2^63 <= x * y <= 2^126.
Proof.
change (- 2 ^ 126 + 2 ^ 63) with (-(2^63 * (2^63 - 1))).
destruct (Z.neg_nonneg_cases y).
 change (2^126) with ((-2^63) * (-2^63)).
 split.
  rewrite Z.mul_comm, <- Z.mul_opp_r.
  transitivity ((2 ^ 63 - 1) * y);[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonpos_r];rep_lia.
 transitivity ((-2 ^ 63) * y);[apply Z.mul_le_mono_nonpos_r|];rep_lia.
change (2^62) with (2^63 * 2^63).
split.
 rewrite <- Z.mul_opp_l.
 transitivity ((-2 ^ 63) * y);[apply Z.mul_le_mono_nonpos_l|apply Z.mul_le_mono_nonneg_r];rep_lia.
transitivity ((2 ^ 63) * y);[apply Z.mul_le_mono_nonneg_r|];rep_lia.
Qed.

Ltac forward_verify_check :=
  match goal with |- semax _ ?E _ _ =>
    forward_loop E continue:E break:E
  end;[entailer!|try (forward_if;[elimtype False|forward;entailer!])|forward;entailer|].

Definition Int128_modulus : Z := 2^128.
Definition Int128_max_unsigned : Z := Int128_modulus - 1.
Definition Int128_max_signed : Z := 2^127 - 1.
Definition Int128_min_signed : Z := -2^127.

Definition t_secp256k1_uint128 := Tstruct _secp256k1_uint128 noattr.

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

(* (secp256k1_uint128_at sh x p) says that the structure pointed to by p
 * is equivalent to x modulo 2^128.
 *)
Definition secp256k1_uint128_at sh x :=
  data_at sh
    t_secp256k1_uint128 (Vlong (Int64.repr x), Vlong (Int64.repr (Z.shiftr x 64))).

Module secp256k1_uint128.

Record args :=
{ share : Share.t
; z : Z
; ptr : val
}.

Definition at_args (x : args) : mpred :=
  secp256k1_uint128_at (share x) (z x) (ptr x).

End secp256k1_uint128.

Definition secp256k1_umulh_spec : ident * funspec :=
DECLARE _secp256k1_umulh
  WITH a : Z, b : Z
  PRE [ tulong, tulong ]
    PROP(0 <= a < Int64.modulus;
         0 <= b < Int64.modulus)
    PARAMS(Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP()
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr (Z.shiftr (a * b) 64)))
  SEP().

Definition secp256k1_mulh_spec : ident * funspec :=
DECLARE _secp256k1_mulh
  WITH a : Z, b : Z
  PRE [ tlong, tlong ]
    PROP(Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed)
    PARAMS(Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP()
POST [ tlong ]
  PROP()
  RETURN(Vlong (Int64.repr (Z.shiftr (a * b) 64)))
  SEP().

Definition secp256k1_u128_mul_spec : ident * funspec :=
DECLARE _secp256k1_u128_mul
  WITH r : val, sh : share, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus;
         0 <= b < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * b) r).

Definition secp256k1_u128_accum_mul_spec : ident * funspec :=
DECLARE _secp256k1_u128_accum_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus;
         0 <= b < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a * b) r).

Definition secp256k1_u128_accum_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_accum_u64
  WITH r : val, sh : share, r0 : Z, a : Z
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a) r).

Definition secp256k1_u128_rshift_spec : ident * funspec :=
DECLARE _secp256k1_u128_rshift
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(writable_share sh;
         0 <= r0 < Int128_modulus;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftr r0 n) r).

Definition secp256k1_u128_to_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_to_u64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr r0))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_u128_hi_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_hi_u64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr (Z.shiftr r0 64)))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_u128_from_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_from_u64
  WITH r : val, sh : share, a : Z
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh a r).

Definition secp256k1_u128_check_bits_spec : ident * funspec :=
DECLARE _secp256k1_u128_check_bits
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(readable_share sh;
         0 <= r0 < 2^128;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if r0 <? 2^n then 1 else 0)))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_i128_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_mul
  WITH r : val, sh : share, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * b) r).

Definition secp256k1_i128_accum_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_accum_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int128_min_signed <= r0 <= Int128_max_signed;
         Int128_min_signed <= r0 + a * b <= Int128_max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a * b) r).

Definition secp256k1_i128_dissip_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_dissip_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int128_min_signed <= r0 <= Int128_max_signed;
         Int128_min_signed <= r0 - a * b <= Int128_max_signed)
   PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 - a * b) r).

Definition secp256k1_i128_det_spec : ident * funspec :=
DECLARE _secp256k1_i128_det
  WITH r : val, sh : share, a : Z, b : Z, c : Z, d : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int64.min_signed <= c <= Int64.max_signed;
         Int64.min_signed <= d <= Int64.max_signed;
         Int128_min_signed <= a * d - b * c <= Int128_max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b);
              Vlong (Int64.repr c); Vlong (Int64.repr d))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * d - b * c) r).

Definition secp256k1_i128_rshift_spec : ident * funspec :=
DECLARE _secp256k1_i128_rshift
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(writable_share sh;
         Int128_min_signed <= r0 <= Int128_max_signed;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftr r0 n) r).

Definition secp256k1_i128_to_i64_spec : ident * funspec :=
DECLARE _secp256k1_i128_to_i64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh;
         Int64.min_signed <= r0 <= Int64.max_signed)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tlong ]
  PROP()
  RETURN(Vlong (Int64.repr r0))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_i128_from_i64_spec : ident * funspec :=
DECLARE _secp256k1_i128_from_i64
  WITH r : val, sh : share, a : Z
  PRE [ tptr t_secp256k1_uint128, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh a r).

Definition secp256k1_i128_eq_var_spec : ident * funspec :=
DECLARE _secp256k1_i128_eq_var
  WITH ptrs : list secp256k1_uint128.args,
       r : secp256k1_uint128.args,
       s : secp256k1_uint128.args
    PRE [ tptr t_secp256k1_uint128, tptr t_secp256k1_uint128 ]
    PROP(In r ptrs;
         In s ptrs;
         readable_share (secp256k1_uint128.share r);
         readable_share (secp256k1_uint128.share s))
    PARAMS(secp256k1_uint128.ptr r; secp256k1_uint128.ptr s)
  SEP(iter_sepcon secp256k1_uint128.at_args ptrs)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if secp256k1_uint128.z r mod 2^128 =? secp256k1_uint128.z s mod 2^128 then 1 else 0)))
  SEP(iter_sepcon secp256k1_uint128.at_args ptrs).

(*
Definition secp256k1_i128_eq_var_spec : ident * funspec :=
DECLARE _secp256k1_i128_eq_var
  WITH r : val, shr : share, r0 : Z,
       s : val, shs : share, s0 : Z
  PRE [ tptr t_secp256k1_uint128, tptr t_secp256k1_uint128 ]
    PROP(readable_share shr;
         readable_share shs)
    PARAMS(r; s)
  SEP(secp256k1_uint128_at shr r0 r;
      secp256k1_uint128_at shs s0 s)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if r0 mod 2^128 =? s0 mod 2^128 then 1 else 0)))
  SEP(secp256k1_uint128_at shr r0 r
     ;secp256k1_uint128_at shs s0 s).
*)

Definition secp256k1_i128_check_bit_spec : ident * funspec :=
DECLARE _secp256k1_i128_check_bit
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(readable_share sh;
         0 <= n < 127)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if r0 mod 2^128 =? 2^n then 1 else 0)))
  SEP(secp256k1_uint128_at sh r0 r).

Definition Gprog := ltac:(with_library prog
  [secp256k1_umulh_spec
  ;secp256k1_mulh_spec
  ;secp256k1_u128_mul_spec
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
  ;secp256k1_i128_to_i64_spec
  ;secp256k1_i128_from_i64_spec
  ;secp256k1_i128_eq_var_spec
  ;secp256k1_i128_check_bit_spec
  ]).

Lemma body_secp256k1_umulh: semax_body Vprog Gprog f_secp256k1_umulh secp256k1_umulh_spec.
Proof.
start_function.
repeat forward.
assert (Ha : 0 <= a <= Int64.max_unsigned) by
 (unfold Int64.max_unsigned; lia).
assert (Hb : 0 <= b <= Int64.max_unsigned) by
 (unfold Int64.max_unsigned; lia).
rewrite !Int64.shru_div_two_p, !mul64_repr, !add64_repr.
rewrite (Int64.unsigned_repr a), (Int64.unsigned_repr b) by assumption.
rewrite (Int.unsigned_repr_eq a), (Int.unsigned_repr_eq b).
change (Int.modulus) with (2^32).
change (two_p (Int64.unsigned (Int64.repr 32))) with (2^32).
change (Int64.modulus) with (2^64) in *.
assert (Hadiv : 0 <= a / 2 ^ 32 < 2^32).
  split;[apply Z.div_pos; auto with *|].
  apply Z.div_lt_upper_bound;[|change (2^32*2^32) with (2^64)]; lia.
assert (Hbdiv : 0 <= b / 2 ^ 32 < 2^32).
  split;[apply Z.div_pos; auto with *|].
  apply Z.div_lt_upper_bound;[|change (2^32*2^32) with (2^64)]; lia.
assert (Hmul64ext : forall x y c d, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
                                    0 <= c < 2^32 -> 0 <= d < 2^32 ->
                                    0 <= x * y + c + d <= 2^64 - 1).
  intros x y c d Hx Hy Hc Hd.
  split;[lia|].
  change (2^64 - 1) with ((2^32 - 1)*(2^32 - 1) + (2^32 - 1) + (2^32 - 1)).
  repeat apply Z.add_le_mono; try lia.
  eapply Z.le_trans;[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r]; lia.
assert (Hmul64 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> 0 <= x * y <= 2^64 - 1).
  intros x y Hx Hy.
  replace (x * y) with (x * y + 0 + 0) by ring.
  apply Hmul64ext; auto; lia.
assert (Habdiv : 0 <= a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32 < 2 ^ 32).
  assert (Hamod := Z.mod_bound_pos a (2^32)).
  assert (Hbmod := Z.mod_bound_pos b (2^32)).
  split;[apply Z.div_pos; try apply Z.mul_nonneg_nonneg; auto with *|].
  apply Z.div_lt_upper_bound;[lia|change (2^32*2^32) with (2^64)].
  cut (a mod 2 ^ 32 * (b mod 2 ^ 32) <= 2 ^ 64 - 1);[lia|].
  apply Hmul64; lia.
rewrite (Int64.unsigned_repr (a mod 2^32 * _)), Int64.unsigned_repr by
 (apply Hmul64; try apply Z.mod_pos_bound; auto with *).
rewrite <- Z.div_add_l, Z.mul_add_distr_r by lia.
rewrite Int.unsigned_repr_eq; change Int.modulus with (2^32).
rewrite Int64.unsigned_repr by
 (apply Hmul64ext; try apply Z.mod_pos_bound;auto;lia).
rewrite <- Z.div_add_l, <- (Z.mul_assoc (a mod 2^32)), <- Z.mul_add_distr_l,
        (Z.mul_comm (b / 2^32)), <- Z_div_mod_eq by lia.
replace (a / 2 ^ 32 * (b / 2 ^ 32) * 2 ^ 32 +
               a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32 * 2 ^ 32 +
               (a mod 2 ^ 32 * b / 2 ^ 32 +
                (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32))
    with (a / 2 ^ 32 * (b / 2 ^ 32) * 2 ^ 32 +
               (2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) +
               (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32) + a mod 2 ^ 32 * b / 2 ^ 32)
    by ring.
rewrite <- Z_div_mod_eq by lia.
replace (a / 2 ^ 32 * (b / 2 ^ 32) * 2 ^ 32 +
               a / 2 ^ 32 * (b mod 2 ^ 32) + a mod 2 ^ 32 * b / 2 ^ 32)
    with (a / 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32) + b mod 2 ^ 32) + a mod 2 ^ 32 * b / 2 ^ 32)
    by ring.
rewrite <- Z_div_mod_eq, <- Z.div_add_l by lia.
replace (a / 2 ^ 32 * b * 2 ^ 32 + a mod 2 ^ 32 * b)
    with ((2 ^ 32 * (a / 2 ^ 32) + a mod 2 ^ 32) * b)
    by ring.
rewrite <- Z_div_mod_eq, <- !Z.shiftr_div_pow2, Z.shiftr_shiftr by lia.
entailer!.
Qed.

Lemma body_secp256k1_mulh: semax_body Vprog Gprog f_secp256k1_mulh secp256k1_mulh_spec.
Proof.
assert (Hmul64_tight : forall x y, -2^31 <= x <= 2^31 - 1 -> -2^31 <= y <= 2^31-1 -> -2^62+2^31 <= x * y <= 2^62).
  intros x y Hx Hy.
  change (-2^62 + 2^31) with (-(2^31 * (2^31 - 1))).
  destruct (Z.neg_nonneg_cases y).
   change (2^62) with ((-2^31) * (-2^31)).
   split.
    rewrite Z.mul_comm, <- Z.mul_opp_r.
    transitivity ((2 ^ 31 - 1) * y);[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonpos_r];lia.
   transitivity ((-2 ^ 31) * y);[apply Z.mul_le_mono_nonpos_r|];try lia.
  change (2^62) with (2^31 * 2^31).
  split.
   rewrite <- Z.mul_opp_l.
   transitivity ((-2 ^ 31) * y);[apply Z.mul_le_mono_nonpos_l|apply Z.mul_le_mono_nonneg_r];lia.
  transitivity ((2 ^ 31) * y);[apply Z.mul_le_mono_nonneg_r|];try lia.
assert (Hmul64 : forall x y, -2^31 <= x <= 2^31 - 1 -> 0 <= y < 2^32 -> -2^63 <= x * y <= 2^63 - 1).
  intros x y Hx Hy.
  change (2^63) with (2^31 * 2^32).
  split.
   rewrite <- Z.mul_opp_l.
   transitivity (-2^31 * y);[|apply Z.mul_le_mono_nonneg_r];lia.
  transitivity ((2^31 - 1)*(2^32));[|lia].
  transitivity ((2^31 - 1) * y);[apply Z.mul_le_mono_nonneg_r|];lia.
assert (Hdiv32bound : forall x, Int64.min_signed <= x <= Int64.max_signed ->
                      Int.min_signed <= x / 2 ^ 32 <= Int.max_signed).
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63 - 1).
  change Int.min_signed with (-2^31).
  change Int.max_signed with (2^31 - 1).
  intros x Hx.
  split;[apply Z.div_le_lower_bound;lia|].
  cut (x / 2^32 < 2^31);[lia|].
  apply Z.div_lt_upper_bound; lia.
assert (Hmod32 : forall x, 
                 Int.unsigned (Int.repr (Int64.unsigned (Int64.repr x))) = x mod 2^32).
 intros x.
 rewrite Int64.unsigned_repr_eq, Int.unsigned_repr_eq.
 rewrite <- Zmod_div_mod; try reflexivity.
 exists (2^32).
 reflexivity.
assert (Hdiv32 : forall x, Int64.min_signed <= x <= Int64.max_signed ->
                           Int64.signed (Int64.shr (Int64.repr x) (Int64.repr 32)) = x / 2^32).
 intros x Hx.
 rewrite Int64.shr_div_two_p, two_p_correct, (Int64.signed_repr x) by auto.
 apply Int64.signed_repr.
 specialize (Hdiv32bound x Hx).
 change Int64.min_signed with (-2^63).
 change Int64.max_signed with (2^63 - 1).
 change Int.min_signed with (-2^31) in *.
 change Int.max_signed with (2^31 - 1) in *.
 lia.
start_function.
assert (Hmod32a : 0 <= a mod 2^32 < 2^32) by (apply Z.mod_pos_bound;lia).
assert (Hmod32b : 0 <= b mod 2^32 < 2^32) by (apply Z.mod_pos_bound;lia).
assert (Hdiv32a : - 2 ^ 31 <= a / 2 ^ 32 <= 2 ^ 31 - 1).
split;
 change Int64.min_signed with (-2^63) in *;
 change Int64.max_signed with (2^63-1) in *.
 apply Z.div_le_lower_bound; lia.
 cut (a / 2^32 < 2^31);[lia|].
 apply Z.div_lt_upper_bound; lia.
assert (Hdiv32b : - 2 ^ 31 <= b / 2 ^ 32 <= 2 ^ 31 - 1).
split;
 change Int64.min_signed with (-2^63) in *;
 change Int64.max_signed with (2^63-1) in *.
 apply Z.div_le_lower_bound; lia.
 cut (b / 2^32 < 2^31);[lia|].
 apply Z.div_lt_upper_bound; lia.
assert (Hab32 : Int64.min_signed <= a / 2 ^ 32 * (b / 2 ^ 32) <= Int64.max_signed).
  change Int64.min_signed with (-2^63) in *;
  change Int64.max_signed with (2^63-1) in *.
  cut (-2^62+2^31 <= a / 2 ^ 32 * (b / 2 ^ 32) <= 2^62);[lia|].
  apply Hmul64_tight; lia.
forward.
rewrite !Hmod32, Int64.mul_signed, !Int64.signed_repr by
 (change Int64.min_signed with (-2^63);
 change Int64.max_signed with (2^63 - 1);
 lia).
forward.
 entailer!.
 rewrite Hmod32, Hdiv32 by auto.
 apply Hmul64;[apply Hdiv32bound|apply Z.mod_pos_bound]; lia.
change (Int.unsigned (Int.repr 32)) with 32.
rewrite !Int64.mul_signed, Hmod32, Hdiv32 by auto.
rewrite !Int64.signed_repr by
 (change Int64.min_signed with (-2^63);
 change Int64.max_signed with (2^63 - 1);
 lia).
forward.
change (Int.unsigned (Int.repr 32)) with 32.
rewrite !Int64.mul_signed, Hmod32, Hdiv32 by auto.
rewrite !Int64.signed_repr by
 (change Int64.min_signed with (-2^63);
 change Int64.max_signed with (2^63 - 1);
 lia).
forward.
change (Int.unsigned (Int.repr 32)) with 32.
rewrite !Hmod32.
rewrite Int64.shru_div_two_p, two_p_correct, !add64_repr.
change (Int64.unsigned (Int64.repr 32)) with 32.
rewrite Int64.unsigned_repr by
 (change Int64.max_unsigned with (2^64-1);
  cut (0 <= a mod 2 ^ 32 * (b mod 2 ^ 32) <= (2^32 - 1) * (2^32 + 1));[lia|];
  split;[auto with *|];
  transitivity (a mod 2^32 * (2^32 + 1));[|lia];
  apply Z.mul_le_mono_nonneg_l;lia).
assert (Hab2 : (- 2 ^ 62 + 2 ^ 31) + (- 2 ^ 31) <=
      a / 2 ^ 32 * (b / 2 ^ 32) + a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32  <=
      (2 ^ 62 + (2^31 - 1))).
 split;apply Zplus_le_compat;
  try (apply Hmul64_tight; lia).
  apply Z.div_le_lower_bound; try lia.
  apply Hmul64; lia.
 apply Z.div_le_upper_bound; try lia.
 rewrite Z.mul_comm.
 transitivity (b mod 2 ^ 32 * (2 ^ 31 - 1));
  [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r];lia.
set (Hab2body := a / 2 ^ 32 * (b / 2 ^ 32) + a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) in *.
assert (Hab3 : ((- 2 ^ 62 + 2 ^ 31) + (- 2 ^ 31)) + (- 2 ^ 31) <=
    Hab2body + a mod 2 ^ 32 * (b / 2 ^ 32) / 2 ^ 32 <=
    ((2 ^ 62 + (2^31 - 1)) + (2^31 - 1))).
 split;apply Zplus_le_compat;
  try (apply Hab2; lia).
  apply Z.div_le_lower_bound; try lia.
  rewrite (Z.mul_comm _ (_ / _)); apply Hmul64; lia.
 apply Z.div_le_upper_bound; try lia.
 transitivity (a mod 2 ^ 32 * (2 ^ 31 - 1));
  [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r];lia.
assert (Hab4: 0 <=
              a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32 +
              (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32 +
              (a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32 <= 2^32 + 2^32 + 2^32)
by (split;[
    repeat apply Z.add_nonneg_nonneg; try apply Z.mod_pos_bound; try apply Z.div_pos;try apply Z.mul_nonneg_nonneg; lia|];
    repeat apply Zplus_le_compat; try (apply Z.lt_le_incl;apply Z.mod_pos_bound;lia);
    apply Z.div_le_upper_bound;[|apply Zmult_le_compat]; lia).
assert (Hab5 : 0 <= (a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32 +
             (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32 +
             (a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) / 
            2 ^ 32 <= 3) by
 (split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia).
forward; change (Z.pow_pos 2 32) with (2^32);
 fold (a / 2^32); fold (b / 2^32); fold ((a mod 2 ^ 32 * (b mod 2 ^ 32)) / 2^32).
* rewrite Hdiv32 by (rewrite Z.mul_comm; apply Hmul64;auto).
  rewrite Hdiv32 by (apply Hmul64;auto).
  rewrite !Int64.mul_signed, !Int64.add_signed.
  rewrite !Hdiv32 by auto.
  rewrite Hdiv32 by (rewrite Z.mul_comm; apply Hmul64;auto).
  rewrite Int64.shru_div_two_p.
  change (two_p _) with (2^32).
  rewrite (Int64.signed_repr (_ * _)) by apply Hab32.
  rewrite (Int64.signed_repr ((_ * _) + _)) by 
   (change Int64.min_signed with (-2^63);
    change Int64.max_signed with (2^63 - 1);
    lia).
  fold Hab2body.
  rewrite (Int64.signed_repr (Hab2body + _)) by 
   (change Int64.min_signed with (-2^63);
    change Int64.max_signed with (2^63 - 1);
    lia).
  rewrite Int64.unsigned_repr by
   (change Int64.max_unsigned with (2^64 - 1); lia).
  rewrite Int64.signed_repr by
  (change Int64.min_signed with (-2^63);
   change Int64.max_signed with (2^63 - 1);
   lia).
  change Int64.min_signed with (-2^63);
  change Int64.max_signed with (2^63 - 1).
  entailer!.
* rewrite !Int64.mul_signed, !Int64.add_signed.
  repeat rewrite Hdiv32 by auto.
  rewrite Hdiv32 by (rewrite Z.mul_comm; apply Hmul64;auto).
  rewrite Int64.shru_div_two_p.
  change (two_p _) with (2^32).
  rewrite (Int64.signed_repr (_ * _)) by apply Hab32.
  rewrite (Int64.signed_repr ((_ * _) + _)) by 
   (change Int64.min_signed with (-2^63);
    change Int64.max_signed with (2^63 - 1);
    lia).
  fold Hab2body.
  rewrite (Int64.signed_repr (Hab2body + _)) by 
   (change Int64.min_signed with (-2^63);
    change Int64.max_signed with (2^63 - 1);
    lia).
  rewrite Int64.unsigned_repr by
   (change Int64.max_unsigned with (2^64 - 1); lia).
  rewrite Int64.signed_repr by
  (change Int64.min_signed with (-2^63);
   change Int64.max_signed with (2^63 - 1);
   lia).
  entailer!.
  do 2 f_equal.
  unfold Hab2body.
  change 64 with (32 + 32).
  rewrite <- Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2, <- Z.div_add_l by lia.
  f_equal.
  transitivity
   ((a / 2 ^ 32 * (b / 2 ^ 32)) * 2 ^ 32 +
      (2 ^ 32 * (a mod 2 ^ 32 * (b / 2 ^ 32) / 2 ^ 32) + (a mod 2 ^ 32 * (b / 2 ^ 32)) mod 2 ^ 32) +
    a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32 +
     (2 ^ 32 * (a / 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32) + (a / 2 ^ 32 * (b mod 2 ^ 32)) mod 2 ^ 32));
   [ring|].
  rewrite <- !Z_div_mod_eq by lia.
  transitivity
    (a / 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32) + (b mod 2 ^ 32)) +
     (a mod 2 ^ 32 * (b / 2 ^ 32) + a mod 2 ^ 32 * (b mod 2 ^ 32) / 2 ^ 32)
    );[ring|].
  rewrite <- Z_div_mod_eq, <- Z.div_add_l by lia.
  replace (a mod 2 ^ 32 * (b / 2 ^ 32) * 2 ^ 32 + a mod 2 ^ 32 * (b mod 2 ^ 32))
   with (a mod 2 ^ 32 * (2 ^ 32 * (b / 2 ^ 32)  +(b mod 2 ^ 32)))
   by ring.
  rewrite <- Z_div_mod_eq, <- Z.div_add_l by lia.
  f_equal.
  transitivity ((2 ^ 32 * (a / 2 ^ 32)  + a mod 2 ^ 32) * b);[ring|].
  rewrite <- Z_div_mod_eq by lia.
  reflexivity.
Qed.

Lemma body_secp256k1_u128_mul_spec: semax_body Vprog Gprog f_secp256k1_u128_mul secp256k1_u128_mul_spec.
Proof.
start_function.
forward_call.
do 2 forward.
rewrite mul64_repr.
entailer!.
Qed.

Lemma body_secp256k1_u128_accum_mul_spec: semax_body Vprog Gprog f_secp256k1_u128_accum_mul secp256k1_u128_accum_mul_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
forward.
forward_call.
do 5 forward.
rewrite mul64_repr, add64_repr.
rewrite <- (Int64.repr_unsigned (Int64.not (Int64.repr _))),
        Int64.unsigned_not,
        Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
case_eq (Int64.ltu (Int64.repr (Int64.max_unsigned - (a * b) mod 2 ^ 64)) (Int64.repr r0)).
* intros Hlt.
  entailer!.
  simpl.
  rewrite !add64_repr.
  change (Int.signed Int.one) with 1.
  apply ltu_inv64 in Hlt.
  unfold secp256k1_uint128_at.
  rewrite Z.add_assoc, !Z.shiftr_div_pow2 by lia.
  replace 1 with ((r0 mod 2 ^ 64 + (a * b) mod 2^64) / 2 ^ 64);[|apply Z.le_antisymm].
  - rewrite <- Z.div_add_l by lia.
    replace ((r0 / 2 ^ 64 + a * b / 2 ^ 64) * 2 ^ 64 +
              (r0 mod 2 ^ 64 + (a * b) mod 2 ^ 64))
       with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64 ) +
              (2 ^ 64 * (a * b / 2 ^ 64) + (a * b) mod 2 ^ 64))
       by ring.
    rewrite <- !Z_div_mod_eq by lia.
    entailer!.
  - apply Zlt_succ_le.
    apply Z.div_lt_upper_bound;[reflexivity|].
    change (2^64 * _) with (2^64 + 2^64).
    assert (Hmod := fun x => (proj2 (Z.mod_pos_bound x (2^64) (refl_equal _)))).
    apply Z.add_lt_mono; auto.
  - apply Z.div_le_lower_bound;[reflexivity|].
    change (2^64*1) with (2^64).
    apply Z.le_sub_le_add_r.
    unfold Int64.max_unsigned in Hlt.
    rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt;
      [change Int64.modulus with (2^64) in Hlt;lia|].
    change Int64.max_unsigned with (2^64-1).
    change Int64.modulus with (2^64).
    cut (0 <= (a * b) mod 2 ^ 64 < 2 ^ 64);[lia|].
    apply Z.mod_pos_bound; lia.
* intros Hnlt.
  entailer!.
  simpl.
  rewrite !add64_repr.
  change (Int.signed Int.zero) with 0.
  apply ltu_false_inv64 in Hnlt.
  unfold secp256k1_uint128_at.
  rewrite Z.add_assoc, !Z.shiftr_div_pow2 by lia.
  replace 0 with ((r0 mod 2 ^ 64 + (a * b) mod 2^64) / 2 ^ 64).
  - rewrite <- Z.div_add_l by lia.
    replace ((r0 / 2 ^ 64 + a * b / 2 ^ 64) * 2 ^ 64 +
              (r0 mod 2 ^ 64 + (a * b) mod 2 ^ 64))
       with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64 ) +
              (2 ^ 64 * (a * b / 2 ^ 64) + (a * b) mod 2 ^ 64))
       by ring.
    rewrite <- !Z_div_mod_eq by lia.
    entailer!.
  - apply Z.div_small.
    split.
    + assert (Hmod := fun x => (proj1 (Z.mod_pos_bound x (2^64) (refl_equal _)))).
      apply Z.add_nonneg_nonneg;auto.
    + rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hnlt;
      [unfold Int64.max_unsigned in Hnlt;
       change (Int64.modulus) with (2^64) in Hnlt;
       lia
      |].
      change Int64.max_unsigned with (2^64 - 1).
      cut (0 <= (a * b) mod 2 ^ 64 < 2^64);[lia|].
      apply Z.mod_pos_bound; lia.
Qed.

Lemma body_secp256k1_u128_accum_u64: semax_body Vprog Gprog f_secp256k1_u128_accum_u64 secp256k1_u128_accum_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
do 5 forward.
unfold secp256k1_uint128_at.
rewrite add64_repr, !Z.shiftr_div_pow2 by discriminate.
assert (Heq : (r0 + a) / 2^64 = r0 / 2^64 + (r0 mod 2^64 + a) / 2^64).
 rewrite (Z.div_mod r0 (2^64)) at 1 by discriminate.
 rewrite Z.mul_comm, <- Z.add_assoc.
 apply Z.div_add_l.
 discriminate.
rewrite Heq.
assert (H0' : 0 <= a <= Int64.max_unsigned) by
 (unfold Int64.max_unsigned; lia).
rewrite <- (Int64.repr_unsigned (Int64.not (Int64.repr a))),
        Int64.unsigned_not,
        Int64.unsigned_repr by assumption.
case_eq (Int64.ltu (Int64.repr (Int64.max_unsigned - a)) (Int64.repr r0)).
* intros Hlt.
  simpl (data_at _ _ _ _).
  change (Int.signed Int.one) with 1.
  change (Z.pow_pos 2 64) with (2^64).
  apply ltu_inv64 in Hlt.
  rewrite add64_repr.
  fold (r0 / 2^64).
  fold ((r0 mod 2 ^ 64 + a) / 2^64).
  replace ((r0 mod 2 ^ 64 + a) / 2 ^ 64) with 1;[entailer!|].
  apply Z.le_antisymm.
  - apply Z.div_le_lower_bound;[reflexivity|].
    change (2^64*1) with (2^64).
    apply Z.le_sub_le_add_r.
    rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt by lia.
    unfold Int64.max_unsigned in Hlt.
    change (Int64.modulus) with (2^64) in Hlt.
    lia.
  - apply Zlt_succ_le.
    apply Z.div_lt_upper_bound;[reflexivity|].
    change (2^64 * _) with (2^64 + 2^64).
    change (2^64) with (Int64.modulus).
    apply Z.add_lt_mono;[|lia].
    assert (Hmod := Z.mod_pos_bound r0 Int64.modulus).
    lia.
* intros Hnlt.
  simpl (data_at _ _ _ _).
  change (Int.signed Int.zero) with 0.
  change (Z.pow_pos 2 64) with (2^64).
  apply ltu_false_inv64 in Hnlt.
  rewrite add64_repr.
  fold (r0 / 2^64).
  fold ((r0 mod 2 ^ 64 + a) / 2^64).
  replace ((r0 mod 2 ^ 64 + a) / 2 ^ 64) with 0;[entailer!|].
  symmetry; apply Z.div_small.
  split.
  - apply Z.add_nonneg_nonneg;[|tauto].
    assert (Hmod := Z.mod_pos_bound r0 (2^64)).
    lia.
  - rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hnlt by lia.
    unfold Int64.max_unsigned in Hnlt.
    change (Int64.modulus) with (2^64) in Hnlt.
    lia.
Qed.

Lemma body_secp256k1_u128_rshift: semax_body Vprog Gprog f_secp256k1_u128_rshift secp256k1_u128_rshift_spec.
Proof.
start_function.
forward_verify_check.
 case_eq (Int.ltu (Int.repr n) (Int.repr 128));intros Hn;rewrite Hn in *;
 apply typed_true_of_bool in H1; try discriminate.
 apply ltu_false_inv in Hn.
 rewrite !Int.unsigned_repr in Hn by (change Int.max_unsigned with (2^32 - 1); lia).
 lia.
unfold secp256k1_uint128_at.
assert (H128int: 128 <= Int.max_unsigned) by discriminate.
assert (H128int64: 128 <= Int64.max_unsigned) by discriminate.
assert (Hr0: 0 <= Z.shiftr r0 64 <= Int64.max_unsigned);[split|].
1:apply Z.shiftr_nonneg; tauto.
1:{cut (Z.shiftr r0 64 < Int64.modulus).
   1:unfold Int64.max_unsigned;lia.
   rewrite Z.shiftr_div_pow2 by lia.
   apply Z.div_lt_upper_bound; try lia.
   rewrite Int64.modulus_power, two_p_equiv, <- Z.pow_add_r; auto.
   tauto.
}
repeat forward_if.
* do 2 forward.
  entailer!.
  1: apply Z.lt_sub_lt_add_r; tauto.
  forward.
  unfold Int64.shru.
  assert (Hn: 0 <= n - 64 < 64) by lia.
  rewrite sub_repr, Int.unsigned_repr, !Int64.unsigned_repr, !Z.shiftr_shiftr by lia.
  replace (64 + (n - 64)) with n by lia.
  replace (Z.shiftr r0 (n + 64)) with 0;[entailer!|].
  rewrite Z.shiftr_div_pow2. 2:lia.
  symmetry; apply Z.div_small;split. 1:lia.
  eapply Z.lt_le_trans with (2^128). 1:tauto.
  apply Z.pow_le_mono_r; lia.
* assert (Hn: 0 <= 64 - n < 64) by lia.
  assert (H02n: 0 < 2 ^ n) by auto with zarith.
  assert (H2n: 0 <= 2 ^ n - 1 <= Int64.max_unsigned).
  { cut (0 < 2^n <= Int64.modulus);[unfold Int64.max_unsigned;lia|].
    split;auto.
    unfold Int64.modulus.
    rewrite two_power_nat_equiv.
    apply Z.pow_le_mono_r;[lia|].
    simpl.
    lia.
  }
  assert (Hmod2n : forall x, 0 <= x mod 2 ^ n <= Int64.max_unsigned).
  { intros x.
    assert (Hbound := Z.mod_pos_bound x _ H02n).
    lia.
  }
  assert (Hshift : forall x, 0 <= Z.shiftl (x mod 2 ^ n) (64 - n) <= Int64.max_unsigned).
  { intros x.
    specialize (Hmod2n x).
    split;[apply Z.shiftl_nonneg; tauto|].
    rewrite Z.shiftl_mul_pow2 by tauto.
    unfold Int64.max_unsigned.
    cut (x mod 2 ^ n * 2 ^ (64 - n) < Int64.modulus);[lia|].
    change Int64.modulus with (2 ^ 64).
    replace 64 with (n + (64 - n)) at 2 by lia.
    rewrite Zpower_exp by lia.
    assert (Hmod := Z.mod_pos_bound x _ H02n).
    apply Zmult_lt_compat_r; auto with *.
  }
  assert (Hshiftr : 0 <= Z.shiftr (r0 mod 2 ^ 64) n <= Int64.max_unsigned).
  { assert (Hmod := Z.mod_pos_bound r0 (2^64)).
    split;[rewrite Z.shiftr_nonneg;lia|].
    unfold Int64.modulus.
    rewrite Z.shiftr_div_pow2 by lia.
    change Int64.max_unsigned with (2^64 - 1).
    transitivity (r0 mod 2^64);[|lia].
    apply Z.div_le_upper_bound;[lia|].
    rewrite <- (Z.mul_1_l (r0 mod 2 ^ 64)) at 1.
    apply Z.mul_le_mono_nonneg_r;lia.
  }
  do 3 forward.
  entailer!.
  split; eapply Z.lt_le_trans with 64;try tauto; reflexivity.
  do 2 forward.
  unfold Int64.shru, Int64.shl, Int64.and, Int64.or.
  rewrite sub_repr, sub64_repr, !Int.unsigned_repr by lia.
  rewrite (Int64.unsigned_repr n) by lia.
  rewrite (Int64.unsigned_repr (Z.shiftr r0 64)) by lia.
  rewrite !Z.shiftr_shiftr by lia.
  rewrite Z.add_comm.
  rewrite Int.signed_repr by tauto.
  rewrite (Int64.unsigned_repr 1) by tauto.
  rewrite (Int64.unsigned_repr (64 - n)) by lia.
  rewrite Z.shiftl_1_l.
  rewrite (Int64.unsigned_repr (2^n - 1)) by assumption.
  rewrite <- Z.shiftl_1_l.
  change (Z.shiftl 1 n - 1) with (Z.ones n).
  rewrite Z.land_ones by lia.
  rewrite (Int64.unsigned_repr (Z.shiftr r0 64 mod 2 ^ n)) by auto.
  rewrite (Int64.unsigned_repr (Z.shiftl (Z.shiftr r0 64 mod 2 ^ n) (64 - n))) by auto.
  rewrite (Int64.unsigned_repr_eq r0).
  change Int64.modulus with (2^64).
  rewrite (Int64.unsigned_repr (Z.shiftr (r0 mod 2 ^ 64) n)) by auto.
  replace (Int64.repr (Z.lor _ _)) with (Int64.repr (Z.shiftr r0 n));[entailer!|].
  apply Int64.eqm_samerepr.
  apply Int64.eqm_same_bits.
  change Int64.zwordsize with 64.
  intros i Hi.
  rewrite Z.lor_spec, Z.shiftl_spec, !Z.shiftr_spec by tauto.
  destruct (Z.neg_nonneg_cases (i - (64 - n))) as [Hneg|Hpos].
  - rewrite (Z.testbit_neg_r _ _ Hneg).
    rewrite Z.mod_pow2_bits_low; auto.
    lia.
  - rewrite Z.mod_pow2_bits_low, Z.mod_pow2_bits_high, Z.shiftr_spec, orb_false_r by lia.
    f_equal.
    lia.
* forward.
  replace n with 0 by lia.
  rewrite Z.shiftr_0_r.
  entailer!.
Qed.

Lemma body_secp256k1_u128_to_u64: semax_body Vprog Gprog f_secp256k1_u128_to_u64 secp256k1_u128_to_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
do 2 forward.
Qed.

Lemma body_secp256k1_u128_hi_u64: semax_body Vprog Gprog f_secp256k1_u128_hi_u64 secp256k1_u128_hi_u64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
do 2 forward.
Qed.

Lemma body_secp256k1_u128_from_u64: semax_body Vprog Gprog f_secp256k1_u128_from_u64 secp256k1_u128_from_u64_spec.
Proof.
start_function.
do 2 forward.
unfold secp256k1_uint128_at.
replace (Z.shiftr a 64) with 0;[entailer!|].
symmetry; apply Z.shiftr_eq_0; auto with *.
destruct H as [_ H].
eapply Z.le_lt_trans with (Z.log2 (2^64 - 1));[apply Z.log2_le_mono|reflexivity].
change (2^64) with Int64.modulus.
lia.
Qed.

Lemma body_secp256k1_u128_check_bits: semax_body Vprog Gprog f_secp256k1_u128_check_bits secp256k1_u128_check_bits_spec.
Proof.
start_function.
forward_verify_check.
 case_eq (Int.ltu (Int.repr n) (Int.repr 128));intros Hn;rewrite Hn in *;
 apply typed_true_of_bool in H1; try discriminate.
 apply ltu_false_inv in Hn.
 rewrite !Int.unsigned_repr in Hn by (change Int.max_unsigned with (2^32 - 1); lia).
 lia.
unfold secp256k1_uint128_at.
forward_if (PROP ( )
   LOCAL (temp _t'1 (Vint (Int.repr (if r0 <? 2^n then 1 else 0))))
   SEP (data_at sh t_secp256k1_uint128
          (Vlong (Int64.repr r0), Vlong (Int64.repr (Z.shiftr r0 64))) r));
   forward;[|forward_if].
* forward;entailer!;[change (Int.unsigned _) with 64;lia|].
  rewrite Int64.shru_div_two_p.
  assert (Hr0shift : 0 <= Z.shiftr r0 64 <= Int64.max_unsigned).
   rewrite Z.shiftr_div_pow2 by lia.
   change Int64.max_unsigned with (2^64 - 1).
   cut (0 <= r0 / 2^64 < 2^64);[lia|].
   split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia.
  assert (Hn64 : 0 <= n - 64 <= Int64.max_unsigned).
   change Int64.max_unsigned with (2^64 - 1).
   lia.
  rewrite !Int64.unsigned_repr, <- Zbits.Zshiftr_div_two_p by tauto.
  rewrite Z.shiftr_shiftr by lia.
  replace (64 + (n - 64)) with n by ring.
  destruct (Zaux.Zlt_bool_spec r0 (2^n)).
  - rewrite Z.shiftr_eq_0; try tauto.
    destruct (Zle_lt_or_eq _ _ (proj1 H)) as [H'|<-];[|simpl;lia].
    apply Z.log2_lt_pow2;lia.
  - rewrite Int64.eq_false; auto.
    intros Heq; revert H5; apply Zlt_not_le.
    rewrite Z.shiftr_div_pow2 in Heq by lia.
    assert (H2n : 0 < 2^n) by (apply Z.pow_pos_nonneg;lia).
    rewrite (Z_div_mod_eq r0 (2^n)) by lia.
    rewrite <- (Int64.unsigned_repr (r0 / 2^n)), Heq.
    + change (Int64.unsigned _) with 0.
      replace (_ * 0 + _) with (r0 mod 2^n) by ring.
      assert (Hmod := (Z.mod_pos_bound r0 (2^n) H2n)).
      tauto.
    + split;[apply Z.div_pos; lia|].
      change Int64.max_unsigned with (2^64 - 1).
      cut (r0 / 2^n < 2^64);[lia|].
      apply Z.div_lt_upper_bound; try lia.
      eapply Z.lt_le_trans;[apply (proj2 H)|].
      rewrite <- Z.pow_add_r by lia.
      apply Z.pow_le_mono_r; lia.
* do 3 forward.
  entailer!.
  assert (H2n : 0 < 2^n) by (apply Z.pow_pos_nonneg;lia).
  rewrite Z.shiftr_div_pow2 in H2 by lia.
  assert (Hr0 : r0 < 2^64).
    rewrite (Z_div_mod_eq r0 (2^64)) by lia.
    rewrite <- (Int64.unsigned_repr (r0 / 2^64)), H2.
      change (Int64.unsigned _) with 0.
      replace (_ * 0 + _) with (r0 mod 2^64) by ring.
      assert (Hmod := (Z.mod_pos_bound r0 (2^64) (refl_equal _))).
      tauto.
    split;[apply Z.div_pos; lia|].
    change Int64.max_unsigned with (2^64 - 1).
    cut (r0 / 2^64 < 2^64);[lia|].
    apply Z.div_lt_upper_bound; try lia.
  rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr, <- Zbits.Zshiftr_div_two_p by (change Int64.max_unsigned with (2^64 - 1); lia).
  destruct (Zaux.Zlt_bool_spec r0 (2^n)).
  - destruct (Zle_lt_or_eq _ _ (proj1 H)) as [H'|<-];
    [|rewrite Z.shiftr_0_l, Int64.eq_true; reflexivity].
    rewrite Z.shiftr_eq_0; try tauto.
    apply Z.log2_lt_pow2;lia.
  - rewrite Int64.eq_false; auto.
    intros Heq; revert H6; apply Zlt_not_le.
    rewrite Z.shiftr_div_pow2 in Heq by lia.
    rewrite (Z_div_mod_eq r0 (2^n)) by lia.
    rewrite <- (Int64.unsigned_repr (r0 / 2^n)), Heq.
    + change (Int64.unsigned _) with 0.
      replace (_ * 0 + _) with (r0 mod 2^n) by ring.
      assert (Hmod := (Z.mod_pos_bound r0 (2^n) H2n)).
      tauto.
    + split;[apply Z.div_pos; lia|].
      change Int64.max_unsigned with (2^64 - 1).
      cut (r0 / 2^n < 2^64);[lia|].
      apply Z.div_lt_upper_bound; try lia.
* forward.
  entailer!.
  destruct (Zaux.Zlt_bool_spec r0 (2^n));[|reflexivity].
  elim H2.
  f_equal.
  destruct (Zle_lt_or_eq _ _ (proj1 H)) as [H'|<-];[|apply Z.shiftr_0_l].
  apply Z.shiftr_eq_0; try tauto.
  etransitivity;[|apply H1].
  apply Z.log2_lt_pow2;lia.
Qed.

Lemma body_secp256k1_i128_mul_spec: semax_body Vprog Gprog f_secp256k1_i128_mul secp256k1_i128_mul_spec.
Proof.
start_function.
forward_call.
do 2 forward.
rewrite mul64_repr.
entailer!.
Qed.

Lemma body_secp256k1_i128_accum_mul_spec: semax_body Vprog Gprog f_secp256k1_i128_accum_mul secp256k1_i128_accum_mul_spec.
Proof.
start_function.
set (r1 := r0 + a * b) in *.
unfold secp256k1_uint128_at.
forward.
forward_call.
do 2 forward.
simpl (force_val _).
rewrite mul64_repr.
rewrite <- (Int64.repr_unsigned (Int64.not (Int64.repr _))),
        Int64.unsigned_not,
        Int64.unsigned_repr_eq.
change Int64.modulus with (2^64).
replace (Val.of_bool _) with (Vint (Int.repr (if Int64.max_unsigned - (a * b) mod 2 ^ 64 <? r0 mod 2^64 then 1 else 0))).
2:{
 case_eq (Int64.ltu (Int64.repr (Int64.max_unsigned - (a * b) mod 2 ^ 64)) (Int64.repr r0)).
 * intros Hlt.
   apply ltu_inv64 in Hlt.
   rewrite Int64.unsigned_repr in Hlt by
     (assert (Hmod := Z.mod_pos_bound (a * b) (2^64)); rep_lia).
   rewrite Int64.unsigned_repr_eq in Hlt.
   change Int64.modulus with (2^64) in *.
   apply Z.ltb_lt in Hlt.
   rewrite Hlt.
   reflexivity.
 * intros Hnlt.
   apply ltu_false_inv64 in Hnlt.
   rewrite Int64.unsigned_repr in Hnlt by
     (assert (Hmod := Z.mod_pos_bound (a * b) (2^64)); rep_lia).
   rewrite Int64.unsigned_repr_eq, Z.ge_le_iff in Hnlt.
   change Int64.modulus with (2^64) in *.
   apply Zaux.Zlt_bool_false in Hnlt.
   rewrite Hnlt.
   reflexivity.
}
simpl (force_val _).
change (Z.pow_pos 2 64) with (2^64).
rewrite !Z.shiftr_div_pow2 by lia.
rewrite add64_repr, Int.signed_repr by (destruct (Z.ltb _ _); rep_lia).
(*Below is ripe for abstraction.  It's been mostly copied from the unsigned version of this function. *)
replace (if _ <? _ then 1 else 0) with (((r0 mod 2 ^ 64 + (a * b) mod 2^64) / 2 ^ 64)).
2: {
 case (Z.ltb_spec0 _ _).
 * intros Hlt.
   apply Z.lt_sub_lt_add_l in Hlt.
   apply Z.le_antisymm.
  - apply Zlt_succ_le.
    apply Z.div_lt_upper_bound;[reflexivity|].
    change (2^64 * _) with (2^64 + 2^64).
    assert (Hmod := fun x => (proj2 (Z.mod_pos_bound x (2^64) (refl_equal _)))).
    apply Z.add_lt_mono; auto.
  - apply Z.div_le_lower_bound;[reflexivity|].
    change (2^64*1) with (2^64).
    apply Z.le_sub_le_add_r.
    change Int64.max_unsigned with (2^64-1) in Hlt.
    cut (0 <= (a * b) mod 2 ^ 64 < 2 ^ 64);[lia|].
    apply Z.mod_pos_bound; lia.
 * intros Hnlt.
   apply Z.div_small.
   split.
    + assert (Hmod := fun x => (proj1 (Z.mod_pos_bound x (2^64) (refl_equal _)))).
      apply Z.add_nonneg_nonneg;auto.
    + change Int64.max_unsigned with (2^64 - 1) in Hnlt.
      cut (0 <= (a * b) mod 2 ^ 64 < 2^64);[lia|].
      apply Z.mod_pos_bound; lia.
}
rewrite <- Z.div_add_l by lia.
replace (a * b / 2 ^ 64 * 2 ^ 64 +
                  (r0 mod 2 ^ 64 + (a * b) mod 2 ^ 64))
 with ((2 ^ 64 * (a * b / 2 ^ 64) + (a * b) mod 2 ^ 64) + r0 mod 2 ^ 64)
 by ring.
rewrite <- Z.div_mod by lia.
set (hi := (a * b + r0 mod 2 ^ 64) / 2 ^ 64).
assert (Hab_tight := mul128_tight _ _ H H0).
assert (Hhi_bound : Int64.min_signed <= hi <= Int64.max_signed).
 cut (Int64.min_signed <= hi < Int64.max_signed + 1);[lia|].
 unfold hi.
 assert (Hr0_bound : 0 <= r0 mod 2^64 < 2^64) by
   (apply Z.mod_pos_bound;lia).
 split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound]; rep_lia.
unfold Int128_min_signed, Int128_max_signed in *.
assert (Hr0hi : Int64.min_signed <= r0 / 2 ^ 64 <= Int64.max_signed).
 cut (Int64.min_signed <= r0 / 2 ^ 64 < Int64.max_signed + 1);[lia|].
 split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];rep_lia.


forward_verify_check.
 forward.
 forward_if (PROP ( )
   LOCAL (temp _t'11 (Vlong (Int64.repr (r0 / 2 ^ 64)));
   temp _hi (Vlong (Int64.repr hi)); temp _t'12 (Vlong (Int64.repr r0));
   temp _t'1 (Vlong (Int64.repr (a * b / 2 ^ 64)));
   temp _lo (Vlong (Int64.repr (a * b))); temp _r r;
   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b));
   temp _t'2 (Vint (Int.repr (if (((r0 / 2^64) mod 2^64 <=? 9223372036854775807) && (hi mod 2^64 <=? 9223372036854775807))%bool then 1 else 0:Z))))
   SEP (data_at sh t_secp256k1_uint128
          (Vlong (Int64.repr r0), Vlong (Int64.repr (r0 / 2 ^ 64))) r));
   try (forward; entailer!).
     apply ltu_false_inv64 in H3; apply Z.ge_le in H3.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in H3; try rep_lia.
     change (Z.pow_pos 2 64) with (2^64) in *.
     change Int64.modulus with (2^64) in *.
     fold (r0 / 2^64) in H3.
     rewrite (Zle_imp_le_bool _ _ H3).
     simpl (true && _)%bool.
     case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr hi)).
      intros Hlt; apply ltu_inv64 in Hlt.
      rewrite Zaux.Zle_bool_false; auto.
      rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt by rep_lia.
      assumption.
     intros Hnlt; apply ltu_false_inv64 in Hnlt; apply Z.ge_le in Hnlt.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in Hnlt by rep_lia.
     rewrite Zle_imp_le_bool; auto.
   apply ltu_inv64 in H3.
   rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3 by rep_lia.
   rewrite Zaux.Zle_bool_false; auto.
 forward.
 forward_if;[|forward];try entailer!.
 rewrite add64_repr in H3.
 change (Z.pow_pos 2 64) with (2^64) in *.
 revert H3.
 fold (r0 / 2^64).
 fold ((a * b + r0 mod 2 ^ 64) / 2^64).
 case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr
                            (r0 / 2 ^ 64 +
                             (a * b + r0 mod 2 ^ 64) / 2 ^ 64)));
 [|destruct (_ && _)%bool; discriminate].
 elim (Z.leb_spec _ _);[|discriminate].
 intros Hr0.
 elim (Z.leb_spec _ _);[|discriminate].
 intros Habr0.
 intros Hr1.
 apply ltu_inv64 in Hr1.
 apply Zlt_not_le in Hr1.
 elim Hr1.
 assert (Hr0hi_nonneg : 0 <= r0 / 2 ^ 64 < 2^63).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_low_is_nonneg;lia.
 assert (Habr0hi_nonneg : 0 <= hi < 2^63).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_low_is_nonneg;unfold hi; lia.
 rewrite !Int64.unsigned_repr by rep_lia.
 rewrite <- Z.div_add_l by lia.
 replace (r0 / 2 ^ 64 * 2 ^ 64 + (a * b + r0 mod 2 ^ 64))
  with (a * b + (2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64))
  by ring.
 rewrite <- Z.div_mod by lia.
 cut ((a * b + r0) / 2 ^ 64 < 2^63);[lia|].
 rewrite Z.add_comm.
 fold r1.
 apply Z.div_lt_upper_bound; rep_lia.

forward_verify_check.
 forward.
 forward_if (PROP ( )
   LOCAL (temp _t'8 (Vlong (Int64.repr (r0 / 2 ^ 64)));
   temp _hi (Vlong (Int64.repr hi)); temp _t'12 (Vlong (Int64.repr r0));
   temp _t'1 (Vlong (Int64.repr (a * b / 2 ^ 64)));
   temp _lo (Vlong (Int64.repr (a * b))); temp _r r;
   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b));
   temp _t'3 (Vint (Int.repr (if (((r0 / 2^64) mod 2^64 >? 9223372036854775807) && (hi mod 2^64 >? 9223372036854775807))%bool then 1 else 0:Z))))
   SEP (data_at sh t_secp256k1_uint128
          (Vlong (Int64.repr r0), Vlong (Int64.repr (r0 / 2 ^ 64))) r));
   try (forward; entailer!).
     apply ltu_inv64 in H3.
     rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3; try rep_lia.
     change (Z.pow_pos 2 64) with (2^64) in *.
     change Int64.modulus with (2^64) in *.
     rewrite !Z.gtb_ltb.
     fold (r0 / 2^64) in H3.
     rewrite (Zaux.Zlt_bool_true _ _ H3).
     simpl (true && _)%bool.
     case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr hi)).
      intros Hlt; apply ltu_inv64 in Hlt.
      rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt by rep_lia.
      rewrite Zaux.Zlt_bool_true; auto.
     intros Hnlt; apply ltu_false_inv64 in Hnlt; apply Z.ge_le in Hnlt.
     rewrite Zaux.Zlt_bool_false; auto.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in Hnlt by rep_lia.
     assumption.
   apply ltu_false_inv64 in H3.
   rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3 by rep_lia.
   apply Z.ge_le in H3.
   rewrite !Z.gtb_ltb.
   rewrite Zaux.Zlt_bool_false; auto.
 forward.
 forward_if;[|forward];try entailer!.
 rewrite add64_repr in H3.
 change (Z.pow_pos 2 64) with (2^64) in *.
 fold (r0 / 2^64) in H3.
 fold ((a * b + r0 mod 2 ^ 64) / 2^64) in H3.
 revert H3.
 case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr
                            (r0 / 2 ^ 64 +
                             (a * b + r0 mod 2 ^ 64) / 2 ^ 64)));
 [destruct (_ && _)%bool; discriminate|].
 elim (Z.gtb_spec _ _);[|discriminate].
 intros Hr0.
 elim (Z.gtb_spec _ _);[|discriminate].
 intros Habr0.
 intros Hr1.
 apply ltu_false_inv64 in Hr1.
 apply Z.ge_le in Hr1.
 apply Zle_not_lt in Hr1.
 elim Hr1.
 assert (Hr0hi_neg : -2^63 <= r0 / 2 ^ 64 < 0).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_high_is_neg;lia.
 assert (Habr0hi_neg : -2^63 <= hi < 0).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_high_is_neg;unfold hi; lia.
 fold hi.
 rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq by rep_lia.
 change (r0 / 2 ^ 64 + hi) with (2^64 mod 2^64 + (r0 / 2 ^ 64 + hi)).
 rewrite Zplus_mod_idemp_l.
 rewrite Z.mod_small by rep_lia.
 unfold hi.
 rewrite <- Z.div_add_l by lia.
 replace (r0 / 2 ^ 64 * 2 ^ 64 + (a * b + r0 mod 2 ^ 64))
  with (a * b + (2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64))
  by ring.
 rewrite <- Z.div_mod by lia.
 rewrite (Z.add_comm _ r0).
 fold r1.
 cut (-2^63 <= r1 / 2^64);[lia|].
 unfold Int128_min_signed in *.
 apply Z.div_le_lower_bound; rep_lia.

do 4 forward.
unfold secp256k1_uint128_at, r1, hi.
entailer!.
fold (2^64).
fold (r0 / 2^64).
rewrite <- Z.div_add_l by lia.
replace (r0 / 2 ^ 64 * 2 ^ 64 + (a * b + r0 mod 2 ^ 64))
 with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64) + a * b)
 by ring.
rewrite <- Z.div_mod by lia.
rewrite Z.shiftr_div_pow2;[entailer!|lia].
Qed.

Lemma body_secp256k1_i128_dissip_mul_spec: semax_body Vprog Gprog f_secp256k1_i128_dissip_mul secp256k1_i128_dissip_mul_spec.
Proof.
start_function.
set (r1 := r0 - a * b) in *.
unfold secp256k1_uint128_at.
forward.
forward_call.
rewrite mul64_repr.
do 2 forward.
simpl (force_val _).
replace (Val.of_bool _) with (Vint (Int.repr (if r0 mod 2^64 <? (a * b) mod 2 ^ 64 then 1 else 0))).
2:{
 case_eq (Int64.ltu (Int64.repr r0) (Int64.repr (a * b))).
 * intros Hlt.
   apply ltu_inv64 in Hlt.
   rewrite !Int64.unsigned_repr_eq in Hlt.
   change Int64.modulus with (2^64) in *.
   apply Z.ltb_lt in Hlt.
   rewrite Hlt.
   reflexivity.
 * intros Hnlt.
   apply ltu_false_inv64 in Hnlt.
   rewrite Int64.unsigned_repr_eq in Hnlt.
   rewrite Int64.unsigned_repr_eq, Z.ge_le_iff in Hnlt.
   change Int64.modulus with (2^64) in *.
   apply Zaux.Zlt_bool_false in Hnlt.
   rewrite Hnlt.
   reflexivity.
}
simpl (force_val _).
change (Z.pow_pos 2 64) with (2^64).
rewrite !Z.shiftr_div_pow2 by lia.
rewrite add64_repr, Int.signed_repr by (destruct (Z.ltb _ _); rep_lia).
replace (if _ <? _ then 1 else 0) with (-((r0 mod 2 ^ 64 - (a * b) mod 2^64) / 2 ^ 64)).
2: {
 assert (Hmodr0 := (Z.mod_pos_bound r0 (2^64) (refl_equal _))).
 assert (Hmodab := (Z.mod_pos_bound (a*b) (2^64) (refl_equal _))).
 case (Z.ltb_spec0 _ _).
 * intros Hlt.
   rewrite Z.eq_opp_l.
   apply Z.le_antisymm.
   - apply Zlt_succ_le.
     apply Z.div_lt_upper_bound;[reflexivity|].
     change (2^64 * _) with (0).
     lia.
   - apply Z.div_le_lower_bound;[reflexivity|].
     lia.
 * intros Hnlt.
   rewrite Z.eq_opp_l.
   apply Z.div_small.
   lia.
}
rewrite Z.add_opp_r, <- Z.add_opp_l, <- Z.opp_sub_distr, <- Z.add_opp_l.
rewrite <- Z.div_add_l by lia.
replace (-(a * b / 2 ^ 64) * 2 ^ 64 +
                  (r0 mod 2 ^ 64 - (a * b) mod 2 ^ 64))
 with (-(2 ^ 64 * (a * b / 2 ^ 64) + (a * b) mod 2 ^ 64) + r0 mod 2 ^ 64)
 by ring.
rewrite <- Z.div_mod, Z.add_opp_l by lia.
set (hi := -((r0 mod 2 ^ 64 - a * b) / 2 ^ 64)).
assert (Hab_tight := mul128_tight _ _ H H0).
assert (Hhi_bound : Int64.min_signed <= hi <= Int64.max_signed).
 cut (Int64.min_signed - 1 < hi <= Int64.max_signed);[lia|].
 unfold hi.
 assert (Hr0_bound : 0 <= r0 mod 2^64 < 2^64) by
   (apply Z.mod_pos_bound;lia).
 split.
  rewrite Z.opp_lt_mono, Z.opp_involutive.
  apply Z.div_lt_upper_bound;rep_lia.
 rewrite Z.opp_le_mono, Z.opp_involutive.
 apply Z.div_le_lower_bound;rep_lia.
unfold Int128_min_signed, Int128_max_signed in *.
assert (Hr0hi : Int64.min_signed <= r0 / 2 ^ 64 <= Int64.max_signed).
 cut (Int64.min_signed <= r0 / 2 ^ 64 < Int64.max_signed + 1);[lia|].
 split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];rep_lia.

forward_verify_check.
 forward.
 forward_if (PROP ( )
   LOCAL (temp _t'11 (Vlong (Int64.repr (r0 / 2 ^ 64)));
   temp _hi (Vlong (Int64.repr hi)); temp _t'12 (Vlong (Int64.repr r0));
   temp _t'1 (Vlong (Int64.repr (a * b / 2 ^ 64)));
   temp _lo (Vlong (Int64.repr (a * b))); temp _r r;
   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b));
   temp _t'2 (Vint (Int.repr (if (((r0 / 2^64) mod 2^64 <=? 9223372036854775807) && (hi mod 2^64 >? 9223372036854775807))%bool then 1 else 0:Z))))
   SEP (data_at sh t_secp256k1_uint128
          (Vlong (Int64.repr r0), Vlong (Int64.repr (r0 / 2 ^ 64))) r));
   try (forward; entailer!).
     apply ltu_false_inv64 in H3; apply Z.ge_le in H3.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in H3; try rep_lia.
     change (Z.pow_pos 2 64) with (2^64) in *.
     change Int64.modulus with (2^64) in *.
     fold (r0 / (2 ^ 64)) in H3.
     rewrite (Zle_imp_le_bool _ _ H3).
     rewrite !Z.gtb_ltb.
     simpl (true && _)%bool.
     case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr hi)).
      intros Hlt; apply ltu_inv64 in Hlt.
      rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt by rep_lia.
      rewrite Zaux.Zlt_bool_true; auto.
     intros Hnlt; apply ltu_false_inv64 in Hnlt; apply Z.ge_le in Hnlt.
     rewrite Zaux.Zlt_bool_false; auto.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in Hnlt by rep_lia.
     assumption.
   apply ltu_inv64 in H3.
   rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3 by rep_lia.
   rewrite Zaux.Zle_bool_false; auto.
 forward.
 forward_if;[|forward];try entailer!.
 revert H3.
 change (Z.pow_pos 2 64) with (2^64) in *.
 rewrite sub64_repr.
 fold (r0 / 2^64).
 fold ((r0 mod 2 ^ 64 - a * b) / 2^64).
 fold hi.
 case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr
                            (r0 / 2 ^ 64 - hi)));
 [|destruct (_ && _)%bool; discriminate].
 elim (Z.leb_spec _ _);[|discriminate].
 intros Hr0.
 elim (Z.gtb_spec _ _);[|discriminate].
 intros Habr0.
 intros Hr1.
 apply ltu_inv64 in Hr1.
 apply Zlt_not_le in Hr1.
 elim Hr1.
 assert (Hr0hi_nonneg : 0 <= r0 / 2 ^ 64 < 2^63).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_low_is_nonneg;lia.
 assert (Habr0hi_neg : -2^63 <= hi < 0).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_high_is_neg;unfold hi in *; lia.
 rewrite !Int64.unsigned_repr by rep_lia.
 unfold hi.
 rewrite Z.sub_opp_r, <- Z.div_add_l by lia.
 replace (r0 / 2 ^ 64 * 2 ^ 64 + (r0 mod 2 ^ 64 - a * b))
  with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64) - a * b)
  by ring.
 rewrite <- Z.div_mod by lia.
 cut ((r0 - a * b) / 2 ^ 64 < 2^63);[lia|].
 fold r1.
 apply Z.div_lt_upper_bound; rep_lia.

forward_verify_check.
 forward.
 forward_if (PROP ( )
   LOCAL (temp _t'8 (Vlong (Int64.repr (r0 / 2 ^ 64)));
   temp _hi (Vlong (Int64.repr hi)); temp _t'12 (Vlong (Int64.repr r0));
   temp _t'1 (Vlong (Int64.repr (a * b / 2 ^ 64)));
   temp _lo (Vlong (Int64.repr (a * b))); temp _r r;
   temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr b));
   temp _t'3 (Vint (Int.repr (if (((r0 / 2^64) mod 2^64 >? 9223372036854775807) && (hi mod 2^64 <=? 9223372036854775807))%bool then 1 else 0:Z))))
   SEP (data_at sh t_secp256k1_uint128
          (Vlong (Int64.repr r0), Vlong (Int64.repr (r0 / 2 ^ 64))) r));
   try (forward; entailer!).
     apply ltu_inv64 in H3.
     rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3; try rep_lia.
     change (Z.pow_pos 2 64) with (2^64) in *.
     change Int64.modulus with (2^64) in *.
     rewrite !Z.gtb_ltb.
     fold (r0 / 2^64) in H3.
     rewrite (Zaux.Zlt_bool_true _ _ H3).
     simpl (true && _)%bool.
     case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr hi)).
      intros Hlt; apply ltu_inv64 in Hlt.
      rewrite Zaux.Zle_bool_false; auto.
      rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in Hlt by rep_lia.
      assumption.
     intros Hnlt; apply ltu_false_inv64 in Hnlt; apply Z.ge_le in Hnlt.
     rewrite Int64.unsigned_repr_eq, Int64.unsigned_repr in Hnlt by rep_lia.
     rewrite Zle_imp_le_bool; auto.
   apply ltu_false_inv64 in H3.
   rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq in H3 by rep_lia.
   apply Z.ge_le in H3.
   rewrite !Z.gtb_ltb.
   rewrite Zaux.Zlt_bool_false; auto.
 forward.
 forward_if;[|forward];try entailer!.
 revert H3.
 change (Z.pow_pos 2 64) with (2^64) in *.
 rewrite sub64_repr.
 fold (r0 / 2^64).
 fold ((r0 mod 2 ^ 64 - a * b) / 2^64).
 fold hi.
 case_eq (Int64.ltu (Int64.repr 9223372036854775807) (Int64.repr
                            (r0 / 2 ^ 64 - hi)));
 [destruct (_ && _)%bool; discriminate|].
 elim (Z.gtb_spec _ _);[|discriminate].
 intros Hr0.
 elim (Z.leb_spec _ _);[|discriminate].
 intros Habr0.
 intros Hr1.
 apply ltu_false_inv64 in Hr1.
 apply Z.ge_le in Hr1.
 apply Zle_not_lt in Hr1.
 elim Hr1.
 assert (Hr0hi_neg : -2^63 <= r0 / 2 ^ 64 < 0).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_high_is_neg;lia.
 assert (Habr0hi_nonneg : 0 <= hi < 2^63).
  unfold Int128_min_signed in *.
  unfold Int128_max_signed in *.
  apply Int64_low_is_nonneg;unfold hi in *; lia.
 rewrite Int64.unsigned_repr, Int64.unsigned_repr_eq by rep_lia.
 change (r0 / 2 ^ 64 - hi) with (2^64 mod 2^64 + (r0 / 2 ^ 64 - hi)).
 rewrite Zplus_mod_idemp_l.
 rewrite Z.mod_small by rep_lia. unfold hi.
 rewrite Z.sub_opp_r, <- Z.div_add_l by lia.
 replace (r0 / 2 ^ 64 * 2 ^ 64 + (r0 mod 2 ^ 64 - a*b))
  with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64)- a*b)
  by ring.
 rewrite <- Z.div_mod by lia.
 fold r1.
 cut (-2^63 <= r1 / 2^64);[lia|].
 unfold Int128_min_signed in *.
 apply Z.div_le_lower_bound; rep_lia.

do 4 forward.
unfold secp256k1_uint128_at, r1, hi.
entailer!.
fold (2^64).
fold (r0 / 2^64).
rewrite Z.sub_opp_r, <- Z.div_add_l by lia.
replace (r0 / 2 ^ 64 * 2 ^ 64 + (r0 mod 2 ^ 64 - a * b))
 with ((2 ^ 64 * (r0 / 2 ^ 64) + r0 mod 2 ^ 64) - a * b)
 by ring.
rewrite <- Z.div_mod by lia.
rewrite Z.shiftr_div_pow2;[entailer!|lia].
Qed.

Lemma body_secp256k1_i128_det: semax_body Vprog Gprog f_secp256k1_i128_det secp256k1_i128_det_spec.
Proof.
start_function.
forward_call.
forward_call.
 unfold Int128_min_signed, Int128_max_signed.
 assert (Htight := mul128_tight _ _ H H2).
 lia.
entailer!.
Qed.

Lemma body_secp256k1_i128_rshift: semax_body Vprog Gprog f_secp256k1_i128_rshift secp256k1_i128_rshift_spec.
Proof.
start_function.
forward_verify_check.
 revert H1.
 case_eq (Int.ltu (Int.repr n) (Int.repr 128));[discriminate|].
 intros Hltu _.
 apply ltu_false_inv in Hltu. 
 change (Int.unsigned (Int.repr 128)) with 128 in Hltu.
 rewrite Int.unsigned_repr in Hltu; rep_lia.
unfold secp256k1_uint128_at.
assert (Hr064 : Int64.min_signed <= Z.shiftr r0 64 <= Int64.max_signed).
 rewrite Zbits.Zshiftr_div_two_p, two_p_correct by lia.
 unfold Int128_min_signed in H.
 unfold Int128_max_signed in H.
 split.
  apply Z.div_le_lower_bound; rep_lia.
 cut (r0 / 2 ^ 64 < Int64.max_signed + 1);[lia|].
 apply Z.div_lt_upper_bound; rep_lia.
assert (Hr0127 : {Z.shiftr r0 127 = 0} + {Z.shiftr r0 127 = -1}).
 rewrite Zbits.Zshiftr_div_two_p, two_p_correct by lia.
 destruct (Z.eq_dec (r0 / 2 ^ 127) 0).
  left; assumption.
 right.
 unfold Int128_min_signed in H.
 unfold Int128_max_signed in H.
 destruct (Z.neg_nonneg_cases r0).
  apply Z.le_antisymm.
   cut (r0 / 2 ^ 127 < 0);[|apply Z.div_lt_upper_bound];lia.
  apply Z.div_le_lower_bound;lia.
 elim n0.
 apply Z.div_small.
 lia.
repeat forward_if.
+ do 2 forward.
   entailer!.
   change (Int.unsigned Int64.iwordsize') with 64; lia.
  do 2 forward.
  entailer!.
  rewrite !Int64.shr_div_two_p, <- !Zbits.Zshiftr_div_two_p,
          !Int64.unsigned_repr, Int64.signed_repr, !Z.shiftr_shiftr by rep_lia.
  replace (64 + (n - 64)) with n by ring.
  change (64 + 63) with 127.
  replace (n + 64) with (127 + (n - 63)) by ring.
  rewrite <- Z.shiftr_shiftr by rep_lia.
  destruct Hr0127 as [->| ->].
   rewrite Z.shiftr_0_l; entailer!.
  rewrite Z_shiftr_neg1_l by lia; entailer!.
+ do 3 forward.
   entailer!.
   change (Int.unsigned Int64.iwordsize') with 64; lia.
  do 2 forward.
  entailer!.
  rewrite (Int64.shl_mul_two_p (Int64.repr 1)), mul64_repr, Z.mul_1_l, sub64_repr.
  rewrite Int64.shr_div_two_p, <- Zbits.Zshiftr_div_two_p by rep_lia.
  rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr, Int64.signed_repr, !Z.shiftr_shiftr by rep_lia.
  rewrite Int64.unsigned_repr_eq.
  rewrite and64_repr, Int64.shl_mul_two_p, mul64_repr, or64_repr.
  rewrite <- Zbits.Zshiftr_div_two_p, <- Zbits.Zshiftl_mul_two_p by rep_lia.
  rewrite Int64.unsigned_repr by rep_lia.
  replace (64 + n) with (n + 64) by ring.
  replace (Int64.repr _) with (Int64.repr (Z.shiftr r0 n));[entailer!|].
  apply Int64.same_bits_eq.
  intros i Hi.
  change (0 <= i < 64) in Hi.
  rewrite !Int64.testbit_repr by assumption.
  rewrite Z.lor_spec, Z.shiftl_spec, Z.land_spec, !(Z.shiftr_spec _ n) by tauto.
  replace (i - (64 - n)) with (i + n - 64) by ring.
  change Int64.modulus with (2^64).
  case (Z.neg_nonneg_cases (i + n - 64)) as [Hin|Hin].
   rewrite (Z.testbit_neg_r _ _ Hin), Z.mod_pow2_bits_low by lia.
   reflexivity.
  rewrite Z.shiftr_spec, Zbits.Ztestbit_two_p_m1, Z.mod_pow2_bits_high by lia.
  destruct (zlt _ _) as [_|Hin64];[|lia].
  rewrite andb_true_r, orb_false_r.
  replace (i + n - 64 + 64) with (i + n) by ring.
  reflexivity.
+ forward.
  replace n with 0;[|lia].
  entailer!.
Qed.

Lemma body_secp256k1_i128_to_i64: semax_body Vprog Gprog f_secp256k1_i128_to_i64 secp256k1_i128_to_i64_spec.
Proof.
start_function.
unfold secp256k1_uint128_at.
forward.
forward.
Qed.

Lemma body_secp256k1_i128_from_i64: semax_body Vprog Gprog f_secp256k1_i128_from_i64 secp256k1_i128_from_i64_spec.
Proof.
start_function.
do 2 forward.
unfold secp256k1_uint128_at.
entailer!.
replace (Int64.shr (Int64.repr a) (Int64.repr 63)) with (Int64.repr (Z.shiftr a 64)).
 entailer!.
change 64 with (63 + 1).
rewrite <- Z.shiftr_shiftr, !Z.shiftr_div_pow2, Int64.shr_div_two_p, two_p_correct, Int64.unsigned_repr by rep_lia.
f_equal.
rewrite Int64.signed_repr by rep_lia.
destruct (Z.neg_nonneg_cases a).
+ replace (a/2^63) with (-1);[reflexivity|].
  cut (0 = a / 2^63 + 1);[lia|].
  rewrite <- Z_div_plus, Z.mul_1_l by lia.
  rewrite Zdiv_small;[reflexivity|rep_lia].
+ rewrite (Zdiv_small a);[reflexivity|rep_lia].
Qed.

Lemma body_secp256k1_i128_eq_var: semax_body Vprog Gprog f_secp256k1_i128_eq_var secp256k1_i128_eq_var_spec.
Proof.
start_function.
destruct r as [shr r0 r].
destruct s as [shs s0 s].
simpl in SH, SH0.
rename H into Hr.
rename H0 into Hs.
rewrite (iter_sepcon_wand_in _ _ _ _ Hr);
unfold secp256k1_uint128.at_args at 1 2; simpl;
unfold secp256k1_uint128_at;
Intros;
forward;
sep_apply modus_ponens_wand.
rewrite (iter_sepcon_wand_in _ _ _ _ Hs);
unfold secp256k1_uint128.at_args at 1 2; simpl;
unfold secp256k1_uint128_at;
Intros;
forward;
sep_apply modus_ponens_wand.
assert (Hrs: r0 mod 2 ^ 128 =? s0 mod 2 ^ 128 = 
             (((Z.shiftr r0 64) mod 2 ^ 64 =? (Z.shiftr s0 64) mod 2 ^ 64) &&
                (r0 mod 2^64 =? s0 mod 2^64))%bool).
 change (2^128) with (2^64 * 2^64).
 rewrite !Zmod_recombine, !Zbits.Zshiftr_div_two_p, two_p_correct by lia.
 elim (Z.eqb_spec _ (s0 mod 2 ^ 64)).
  intros ->.
  elim (Z.eqb_spec _ ((s0 / 2 ^ 64) mod 2 ^ 64)).
   intros ->.
   apply Z.eqb_refl.
  intros Hneq.
  apply <- Z.eqb_neq.
  lia.
 intros Hneq.
 rewrite andb_false_r.
 apply <- Z.eqb_neq.
 intros Heq.
 apply Hneq; clear Hneq.
 apply (f_equal (fun x => x mod 2^64)) in Heq.
 repeat rewrite Z.add_comm, Z_mod_plus_full, Zmod_mod in Heq.
 assumption.
forward_if 
  (PROP ( )
   LOCAL (temp _t'1 (Vint (Int.repr (if r0 mod 2^128 =? s0 mod 2^128  then 1 else 0))))
   SEP (iter_sepcon secp256k1_uint128.at_args ptrs)).
+ rewrite (iter_sepcon_wand_in _ _ _ _ Hr);
  unfold secp256k1_uint128.at_args at 1 2; simpl;
  unfold secp256k1_uint128_at;
  Intros;
  forward;
  sep_apply modus_ponens_wand.
  rewrite (iter_sepcon_wand_in _ _ _ _ Hs);
  unfold secp256k1_uint128.at_args at 1 2; simpl;
  unfold secp256k1_uint128_at;
  Intros;
  forward;
  sep_apply modus_ponens_wand.
  forward.
  entailer!.
  rewrite Hrs.
  apply Int64.same_if_eq in H.
  apply (f_equal Int64.unsigned) in H.
  rewrite !Int64.unsigned_repr_eq in H.
  change Int64.modulus with (2^64) in *.
  rewrite H, Z.eqb_refl, andb_true_l.
  case_eq (Int64.eq (Int64.repr r0) (Int64.repr s0)).
   intros Heq.
   apply Int64.same_if_eq in Heq.
   apply (f_equal Int64.unsigned) in Heq.
   rewrite !Int64.unsigned_repr_eq in Heq.
   change Int64.modulus with (2^64) in *.
   rewrite Heq, Z.eqb_refl.
   reflexivity.
  intros Hneq.
  apply int64_eq_false_e in Hneq.
  elim Z.eqb_spec;[|reflexivity].
  intros Heq.
  elim Hneq; clear Hneq.
  rewrite <- Int64.repr_unsigned, Int64.unsigned_repr_eq.
  rewrite <- (Int64.repr_unsigned (Int64.repr r0)), Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  f_equal.
  assumption.
+ forward.
  entailer!.
  rewrite Hrs.
  elim Z.eqb_spec;[|reflexivity].
  intros; elim H.
  rewrite <- Int64.repr_unsigned, Int64.unsigned_repr_eq.
  rewrite <- (Int64.repr_unsigned (Int64.repr (Z.shiftr r0 64))), Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  f_equal.
  assumption.
+ forward.
Qed.

Lemma body_secp256k1_i128_check_bit: semax_body Vprog Gprog f_secp256k1_i128_check_bit secp256k1_i128_check_bit_spec.
Proof.
start_function.
forward_verify_check.
 revert H0.
 case_eq (Int.ltu (Int.repr n) (Int.repr 127));[discriminate|].
 intros Hltu _.
 apply ltu_false_inv in Hltu.
 apply Z.ge_le_iff in Hltu.
 apply (Zle_not_lt _ _ Hltu).
 change (Int.unsigned (Int.repr 127)) with 127.
 rewrite Int.unsigned_repr; rep_lia.
unfold secp256k1_uint128_at.
forward_if 
  (PROP ( )
   LOCAL (temp _t'1 (Vint (Int.repr (if r0 mod 2^128 =? 2^n then 1 else 0))))
   SEP (secp256k1_uint128_at sh r0 r));forward.
- assert (Hr0: r0 mod 2 ^ 128 =? 2 ^ n = 
             (((Z.shiftr r0 64) mod 2 ^ 64 =? 2 ^ (n - 64)) && (r0 mod 2^64 =? 0))%bool).
   change (2^128) with (2^64 * 2^64).
   rewrite Zmod_recombine by lia.
   replace n with (n - 64 + 64) at 1 by ring.
   rewrite Z.pow_add_r, Z.shiftr_div_pow2 by lia.
   elim Z.eqb_spec.
    intros Heq.
    replace (r0 mod 2 ^ 64) with 0;
    [|rewrite Z.mul_comm in Heq;
      symmetry in Heq;
      apply Zdiv.Zmod_unique in Heq;[rewrite Heq, Z_mod_mult; reflexivity|apply Z.mod_pos_bound;lia]].
    apply (f_equal (fun x => x / 2^64)) in Heq.
    rewrite Z_div_mult, Z.div_add_l in Heq by lia.
    rewrite <- Heq, Zmod_div, Z.add_0_r, !Z.eqb_refl by lia.
    reflexivity.
   elim (Z.eqb_spec _ 0);[|rewrite andb_false_r;reflexivity].
   intros ->.
   rewrite Z.add_0_r, andb_true_r.
   intros Hneq.
   symmetry.
   apply Z.eqb_neq.
   intros Heq.
   apply Hneq; clear Hneq.
   rewrite Heq; reflexivity.
  assert (Hn: 0 <= 2 ^ (n - 64) < 2^64).
   split;[apply Z.pow_nonneg|apply Z.pow_lt_mono_r];lia.
  forward_if.
  + entailer!.
    change (Int.unsigned Int64.iwordsize') with 64.
    lia.
  + do 3 forward; entailer!.
    apply Int64.same_if_eq in H1.
    rewrite Int64.shl_mul_two_p, mul64_repr, Z.mul_1_l, Int64.int_unsigned_repr in H1.
    rewrite Int.unsigned_repr in H1 by rep_lia.
    apply (f_equal Int64.unsigned) in H1.
    rewrite Int64.unsigned_repr_eq in H1.
    change Int64.modulus with (2^64) in H1.
    rewrite Hr0, H1, two_p_correct.
    rewrite Int64.unsigned_repr, Z.eqb_refl, andb_true_l by rep_lia.
    elim (Z.eqb_spec _ 0).
     intros <-.
     rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned, Int64.eq_true.
     reflexivity.
    intros Hneq.
    case_eq (Int64.eq (Int64.repr r0) (Int64.repr 0));[|reflexivity].
    intros Heq.
    apply Int64.same_if_eq in Heq.
    elim Hneq.
    rewrite <- Int64.unsigned_repr_eq, Heq.
    reflexivity.
  + forward;entailer!.
    rewrite Hr0.
    elim (Z.eqb_spec _ _);[|reflexivity].
    intros Heq.
    elim H1.
    etransitivity;[|apply Int64.repr_unsigned].
    etransitivity;[symmetry;apply Int64.repr_unsigned|].
    f_equal.
    rewrite Int64.unsigned_repr_eq.
    change Int64.modulus with (2^64).
    rewrite Heq.
    rewrite Int64.shl_mul_two_p, mul64_repr, Z.mul_1_l, Int64.int_unsigned_repr, Int.unsigned_repr by rep_lia.
    rewrite two_p_correct, Int64.unsigned_repr by rep_lia.
    reflexivity.
- assert (Hr0: r0 mod 2 ^ 128 =? 2 ^ n = 
             (((Z.shiftr r0 64) mod 2 ^ 64 =? 0) && (r0 mod 2^64 =? 2^n))%bool).
   change (2^128) with (2^64 * 2^64).
   rewrite Zmod_recombine by lia.
   elim Z.eqb_spec.
    intros Heq.
    assert (Hr0 : (r0 / 2 ^ 64) mod 2 ^ 64 = 0).
     apply (f_equal (fun x => x / 2^64)) in Heq.
     rewrite Z.div_add_l, Zmod_div, Z.add_0_r in Heq by lia.
     rewrite Heq.
     apply Zdiv_small.
     split;[apply Z.pow_nonneg|apply Z.pow_lt_mono_r];lia.
    rewrite Hr0, Z.mul_0_l, Z.add_0_l in Heq.
    rewrite Zbits.Zshiftr_div_two_p, two_p_correct, Hr0, Heq, !Z.eqb_refl by lia.
    reflexivity.
   intros Hneq.
   elim (Z.eqb_spec _ (2^n));[rewrite andb_true_r|rewrite andb_false_r;reflexivity].
   intros Heq.
   rewrite Heq in Hneq; clear Heq.
   symmetry; apply Z.eqb_neq.
   rewrite Zbits.Zshiftr_div_two_p, two_p_correct by lia.
   intros Heq.
   apply Hneq.
   rewrite Heq.
   ring.
  forward_if; repeat forward; entailer!.
  + rewrite Hr0.
    apply (f_equal Int64.unsigned) in H1.
    rewrite Int64.unsigned_repr_eq in H1.
    change Int64.modulus with (2^64) in *.
    rewrite H1, Z.eqb_refl, andb_true_l.
    rewrite Int64.shl_mul_two_p, mul64_repr, Z.mul_1_l, two_p_correct, Int64.unsigned_repr by rep_lia.
    elim (Z.eqb_spec _ (2^n)).
     intros Heq.
     rewrite <- (Int64.repr_unsigned (Int64.repr r0)), Int64.unsigned_repr_eq.
     change Int64.modulus with (2^64).
     rewrite Heq, Int64.eq_true.
     reflexivity.
    intros Hneq.
    case_eq (Int64.eq (Int64.repr r0) (Int64.repr (2^n)));[|reflexivity].
    intros Heq.
    apply Int64.same_if_eq in Heq.
    elim Hneq.
    rewrite <- Int64.unsigned_repr_eq, Heq.
    apply Int64.unsigned_repr.
    split;[apply Z.pow_nonneg;lia|].
    cut (2^n < 2^64);[rep_lia|].
    apply Z.pow_lt_mono_r;lia.
  + rewrite Hr0.
    elim (Z.eqb_spec _ 0);[|reflexivity].
    intros Heq.
    elim H1.
    rewrite <- (Int64.repr_unsigned (Int64.repr (Z.shiftr r0 64))), Int64.unsigned_repr_eq.
    change Int64.modulus with (2^64).
    f_equal.
    assumption.
Qed.

Require Import VST.floyd.VSU.

Definition Int128ASI:funspecs := 
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
  ;secp256k1_i128_to_i64_spec
  ;secp256k1_i128_from_i64_spec
  ;secp256k1_i128_eq_var_spec
  ;secp256k1_i128_check_bit_spec
  ].

(*
Definition Int128VSU: @VSU NullExtension.Espec 
      nil nil ltac:(QPprog prog) Int128ASI emp.
Proof.
mkVSU prog Int128ASI.
+ solve_SF_internal body_secp256k1_umulh.
Qed.
*)
