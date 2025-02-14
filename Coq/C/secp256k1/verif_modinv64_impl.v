Require Import VST.floyd.proofauto.
Require Import jets_secp256k1.
Require Import spec_int128.
Require Import spec_modinv64.
Require Import extraMath.
Require Import progressC.
Require Import divsteps.divsteps_theory.
Require Import divsteps.divsteps724.
Require Import modinv.
Require divstep.

Opaque Z.shiftl Z.shiftr Z.pow.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_secp256k1_modinv64_trans2x2 := Tstruct _secp256k1_modinv64_trans2x2 noattr.

Definition Trans_repr (m: divstep.Trans.M2x2) : reptype t_secp256k1_modinv64_trans2x2 :=
( Vlong (Int64.repr (divstep.Trans.u m))
, (Vlong (Int64.repr (divstep.Trans.v m))
, (Vlong (Int64.repr (divstep.Trans.q m))
, Vlong (Int64.repr (divstep.Trans.r m))
))).

Definition secp256k1_ctz64_var_debruijn_spec : ident * funspec :=
DECLARE _secp256k1_ctz64_var_debruijn
  WITH a : Z, sh_debruijn : share, gv : globals
  PRE [ tulong ]
    PROP(0 <= a < Int64.modulus; readable_share sh_debruijn)
    PARAMS(Vlong (Int64.repr a))
    GLOBALS(gv)
    SEP(debruijn64_array sh_debruijn gv)
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (Z_ctz a)))
    SEP(debruijn64_array sh_debruijn gv).

(* secp256k1_ctz64_var is undefined for 0. *)
Definition secp256k1_ctz64_var_spec : ident * funspec :=
DECLARE _secp256k1_ctz64_var
  WITH a : Z, sh_debruijn : share, gv : globals
  PRE [ tulong ]
    PROP(0 < a < Int64.modulus; readable_share sh_debruijn)
    PARAMS(Vlong (Int64.repr a))
    GLOBALS(gv)
    SEP(debruijn64_array sh_debruijn gv)
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (Z_ctz a)))
    SEP(debruijn64_array sh_debruijn gv).

Definition secp256k1_modinv64_abs_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_abs
  WITH a : Z
  PRE [ tlong ]
    PROP(Int64.min_signed < a <= Int64.max_signed)
    PARAMS(Vlong (Int64.repr a))
    SEP()
  POST [ tlong ]
    PROP()
    RETURN(Vlong (Int64.repr (Z.abs a)))
    SEP().

Definition secp256k1_modinv64_mul_62_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_mul_62
  WITH a : Z, alen : nat, factor : Z,
       ptrr : val, ptra : val, shr : share, sha : share
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_signed62
      , tint
      , tlong
      ]
    PROP( (1 <= alen <= 5)%nat
        ; -2^(62 * Z.of_nat alen + 1) <= a <= 2^(62 * Z.of_nat alen + 1) - 1
        ; -2^311 <= a * factor <= 2^311 - 1
        ; Int64.min_signed <= factor <= Int64.max_signed
        ; writable_share shr
        ; readable_share sha
        )
    PARAMS(ptrr; ptra; Vint (Int.repr (Z.of_nat alen)); Vlong (Int64.repr factor))
    SEP( data_at_ shr t_secp256k1_modinv64_signed62 ptrr
       ; data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
       )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP( data_at shr t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (a*factor))) ptrr
       ; data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
       ).

Definition secp256k1_modinv64_mul_cmp_62_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_mul_cmp_62
  WITH a : Z, alen : nat, b : Z, factor : Z,
       ptra : val, ptrb : val, sha : share, shb : share
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tint
      , tptr t_secp256k1_modinv64_signed62
      , tlong
      ]
    PROP( (1 <= alen <= 5)%nat
        ; -2^(62 * Z.of_nat alen + 1) <= a <= 2^(62 * Z.of_nat alen + 1) - 1
        ; -2^311 <= b <= 2^311 - 1
        ; -2^311 <= b * factor <= 2^311 - 1
        ; Int64.min_signed <= factor <= Int64.max_signed
        ; readable_share sha
        ; readable_share shb
        )
    PARAMS(ptra; Vint (Int.repr (Z.of_nat alen)); ptrb; Vlong (Int64.repr factor))
    SEP( data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
       ; data_at shb t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 b)) ptrb
       )
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (Z_of_comparison (a ?= b * factor))))
    SEP( data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
       ; data_at shb t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 b)) ptrb
       ).

Definition secp256k1_modinv64_det_check_pow2_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_det_check_pow2
  WITH m : divstep.Trans.M2x2, t : val, sh : share, n : Z, abs_flag : bool
  PRE [ tptr t_secp256k1_modinv64_trans2x2, tuint, tint ]
    PROP(divstep.Trans.bounded (2^62) m;
         0 <= n < 127;
         readable_share sh)
    PARAMS(t; Vint (Int.repr n); Vint (Int.repr (Z.b2z abs_flag)))
    SEP(data_at sh t_secp256k1_modinv64_trans2x2 (Trans_repr m) t)
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (Z.b2z 
      ((if abs_flag then Z.abs else id) (divstep.Trans.det m) =? 2^n))))
    SEP(data_at sh t_secp256k1_modinv64_trans2x2 (Trans_repr m) t).

Definition secp256k1_modinv64_normalize_62_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_normalize_62
  WITH r : Z, sign : int64, m : Z,
       ptrr : val, ptrm : val, shr : share, shm : share
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tlong
      , tptr t_secp256k1_modinv64_modinfo
      ]
    PROP( 0 <= m <= 2^310 - 2 ^ 248
        ; -2^310 + 2^248 <= r
        ; -2 * m < r < m
        ; writable_share shr
        ; readable_share shm
        )
    PARAMS(ptrr; Vlong sign; ptrm)
    SEP( data_at shr t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 r)) ptrr
       ; data_at shm t_secp256k1_modinv64_modinfo (make_modinfo m) ptrm
       )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP( data_at shr t_secp256k1_modinv64_signed62
           (map Vlong (Signed62.reprn 5 ((if Int64.signed sign <? 0 then -r else r) mod m))) ptrr
       ; data_at shm t_secp256k1_modinv64_modinfo (make_modinfo m) ptrm
       ).

Definition secp256k1_modinv64_divsteps_62_var_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_divsteps_62_var
  WITH st : divstep.State, t : val, sh : share,
       sh_debruijn : share, gv : globals
  PRE [ tlong, tulong, tulong, tptr t_secp256k1_modinv64_trans2x2 ]
    PROP(-683 <= divstep.eta st < 683;
         writable_share sh;
         readable_share sh_debruijn)
    PARAMS(Vlong (Int64.repr (divstep.eta st)); Vlong (Int64.repr (divstep.f st)); Vlong (Int64.repr (divstep.g st)); t)
    GLOBALS(gv)
    SEP(data_at_ sh t_secp256k1_modinv64_trans2x2 t;
        debruijn64_array sh_debruijn gv)
  POST [ tlong ]
    PROP()
    RETURN(Vlong (Int64.repr (divstep.eta (fst (divstep.stepN 62 st)))))
    SEP(data_at sh t_secp256k1_modinv64_trans2x2 (Trans_repr (divstep.Trans.transN 62 st)) t;
        debruijn64_array sh_debruijn gv).

Definition secp256k1_modinv64_update_de_62_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_update_de_62
  WITH d : Z, e : Z, mtx : divstep.Trans.M2x2, m : Z,
       ptrd : val, ptre : val, ptrt : val, ptrm : val, shd : share, she : share, sht : share, shm : share
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_trans2x2
      , tptr t_secp256k1_modinv64_modinfo
      ]
    PROP( Z.Odd m
        ; 0 <= m <= 2^308
        ; -2 * m < d < m
        ; -2 * m < e < m
        ; divstep.Trans.bounded (2 ^ 62) mtx
        ; writable_share shd
        ; writable_share she
        ; readable_share sht
        ; readable_share shm
        )
    PARAMS(ptrd; ptre; ptrt; ptrm)
    SEP( data_at shd t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d)) ptrd
       ; data_at she t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e)) ptre
       ; data_at sht t_secp256k1_modinv64_trans2x2 (Trans_repr mtx) ptrt
       ; data_at shm t_secp256k1_modinv64_modinfo (make_modinfo m) ptrm
       )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP( data_at shd t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (fst (divstep.update_de m d e mtx)))) ptrd
       ; data_at she t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (snd (divstep.update_de m d e mtx)))) ptre
       ; data_at sht t_secp256k1_modinv64_trans2x2 (Trans_repr mtx) ptrt
       ; data_at shm t_secp256k1_modinv64_modinfo (make_modinfo m) ptrm
       ).

Definition secp256k1_modinv64_update_fg_62_var_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_update_fg_62_var
  WITH len : nat, st : divstep.State,
       ptrf : val, ptrg : val, ptrt : val, shf : share, shg : share, sht : share
  PRE [ tint
      , tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_trans2x2
      ]
    PROP((1 <= len <= 5)%nat
        ; -2^(62 * Z.of_nat len + 1) <= divstep.f st <= 2^(62 * Z.of_nat len + 1) - 1
        ; -2^(62 * Z.of_nat len + 1) <= divstep.g st <= 2^(62 * Z.of_nat len + 1) - 1
        ; writable_share shf
        ; writable_share shg
        ; readable_share sht)
    PARAMS(Vint (Int.repr (Z.of_nat len)); ptrf; ptrg; ptrt)
    SEP( data_at shf t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.f st))) ptrf
       ; data_at shg t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.g st))) ptrg
       ; data_at sht t_secp256k1_modinv64_trans2x2 (Trans_repr (divstep.Trans.transN 62 st)) ptrt
       )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP( data_at shf t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.f (fst (divstep.stepN 62 st))))) ptrf
       ; data_at shg t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.g (fst (divstep.stepN 62 st))))) ptrg
       ; data_at sht t_secp256k1_modinv64_trans2x2 (Trans_repr (divstep.Trans.transN 62 st)) ptrt
       ).

Definition Gprog := ltac:(with_library prog
  [(*secp256k1_u128_load_spec *)
   secp256k1_u128_mul_spec
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

  ;secp256k1_ctz64_var_debruijn_spec
  ;secp256k1_ctz64_var_spec
  ;secp256k1_modinv64_signed62_assign_spec
  ;secp256k1_modinv64_abs_spec
  ;secp256k1_modinv64_mul_62_spec
  ;secp256k1_modinv64_mul_cmp_62_spec
  ;secp256k1_modinv64_det_check_pow2_spec
  ;secp256k1_modinv64_normalize_62_spec
  ;secp256k1_modinv64_divsteps_62_var_spec
  ;secp256k1_modinv64_update_de_62_spec
  ;secp256k1_modinv64_update_fg_62_var_spec
  ;secp256k1_modinv64_var_spec
  ]).

Lemma body_secp256k1_modinv64_signed62_assign: semax_body Vprog Gprog f_secp256k1_modinv64_signed62_assign secp256k1_modinv64_signed62_assign_spec.
Proof.
start_function.
assert (Hlenx := Signed62.reprn_Zlength 5 x).
fastforward 10.
entailer!!.
Qed.

Lemma body_secp256k1_ctz64_var_debruijn: semax_body Vprog Gprog f_secp256k1_ctz64_var_debruijn secp256k1_ctz64_var_debruijn_spec.
Proof.
start_function.
unfold_C.
unfold debruijn64_array.
set (l64 := cons (Vint (Int.repr 0)) _).
assert (Hctz64: 0 <= Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod 2 ^ 64) 58 < 64)
  by (rewrite strict_bounds; solve_bounds).
assert_PROP (force_val
   (sem_add_ptr_long tuchar (gv _debruijn)
      (Vlong
         (Int64.shru
            (Int64.mul
               (Int64.and (Int64.repr a)
                  (Int64.neg (Int64.repr a)))
               (Int64.repr 157587932685088877))
            (Int64.repr 58)))) =
 field_address (tarray tuchar 64)
   [ArraySubsc (Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod (2^64)) 58)]
   (gv _debruijn)).
  convert_C_to_math.
  entailer!.
  rewrite arr_field_address; auto; simpl.
  destruct (Zle_lt_or_eq _ _ (proj1 H)) as [H0a|<-];[|reflexivity].
  rewrite Z_x_and_opp_x, Z.mul_comm, Z.mul_1_l by lia.
  rewrite Z.shiftl_mul_pow2;[reflexivity|apply Z_ctz_non_neg].
assert (Hctz : 0 <= Z_ctz a < 64).
  split;[apply Z_ctz_non_neg|].
  destruct (Zle_lt_or_eq _ _ (proj1 H)) as [Ha0|<-];[|simpl;lia].
  apply Z_ctz_bound; lia.
assert (Hl64 :
  (@Znth val Vundef (Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod 2 ^ 64) 58) l64) =
  (Vint (Int.repr (Z_ctz a)))).
  revert Hctz.
  generalize (Z_ctz a).
  intros z [Hz Hz64].
  do 64 (
    apply Zle_lt_or_eq in Hz;
    destruct Hz as [Hz|<-];[|reflexivity];
    apply Zlt_le_succ in Hz; simpl in Hz).
  lia.
forward.
rewrite Hl64.
entailer!;rep_lia.
entailer!.
rewrite H0.
apply field_address_isptr.
apply arr_field_compatible; auto.
forward.
fold l64; rewrite Hl64.
entailer!.
Qed.

Lemma body_secp256k1_ctz64_var: semax_body Vprog Gprog f_secp256k1_ctz64_var secp256k1_ctz64_var_spec.
Proof.
start_function.
forward_verify_check.
 revert H0.
 convert_C_to_math.
 destruct (Z.eqb_spec a 0);[lia|cbn].
 discriminate.
forward_call.
forward.
Qed.

Lemma body_secp256k1_modinv64_abs: semax_body Vprog Gprog f_secp256k1_modinv64_abs secp256k1_modinv64_abs_spec.
Proof.
start_function.
forward_verify_check.
 revert H0.
 convert_C_to_math.
 elim Z.ltb_spec; try discriminate; lia.
forward_if; revert H0; convert_C_to_math; intros H0; progressC;
do 2 f_equal; lia.
Qed.

Lemma body_secp256k1_modinv64_mul_62: semax_body Vprog Gprog f_secp256k1_modinv64_mul_62 secp256k1_modinv64_mul_62_spec.
Proof.
start_function.
progressC.
change (Z.shiftr (-1 mod 2 ^ 64) 2) with (2^62 - 1).
forward_call (v_c, Tsh, 0).
assert (Hlen := Signed62.reprn_length alen a).
assert (HZlen : Zlength (Signed62.reprn alen a) = Z.of_nat alen) by (rewrite Zlength_correct; lia).
    assert (Hstep : forall i, 0 <= i < Z.of_nat alen -> Signed62.signed (firstn (Z.to_nat i) (Signed62.reprn alen a)) * factor / 2 ^ (62 * i) 
              + Int64.signed (Znth i (Signed62.reprn alen a)) * factor =
            Signed62.signed (firstn (Z.to_nat (Z.succ i)) (Signed62.reprn alen a)) * factor / 2 ^ (62 * i)).
      clear - H Hlen HZlen.
      intros i Hi.
      rewrite (app_removelast_last (l:=firstn (Z.to_nat (Z.succ i)) _) default) by
        (rewrite <- length_zero_iff_nil, firstn_length; lia).
      rewrite Signed62.app_signed.
      rewrite Z2Nat.inj_succ, <- removelast_firstn, <- nth_last, removelast_firstn_len,
              Zlength_correct, !firstn_length, !min_l, Nat.sub_1_r, Z.mul_add_distr_r, <- Z.mul_assoc,
              firstn_firstn, nth_firstn_low by lia.
      change (Nat.pred (S (Z.to_nat i)))%nat with (Z.to_nat i).
      rewrite nth_Znth, Z2Nat.id by lia.
      rewrite (Z.mul_comm i 62), (Z.mul_comm (2^(62*i))), Z_div_plus_full by lia.
      simpl (Signed62.signed [Znth i (Signed62.reprn alen a)]).
      rewrite Z.mul_0_r, Z.add_0_r.
      reflexivity.
forward_for_simple_bound 4 (EX i:Z,
  PROP ( )
  LOCAL ( lvar _d (Tstruct _secp256k1_uint128 noattr) v_d
        ; lvar _c (Tstruct _secp256k1_uint128 noattr) v_c
        ; temp _M62 (Vlong (Int64.repr (2 ^ 62 - 1)))
        ; temp _r ptrr
        ; temp _a ptra
        ; temp _alen (Vint (Int.repr (Z.of_nat alen)))
        ; temp _factor (Vlong (Int64.repr factor))
        )
  SEP( data_at_ Tsh (Tstruct _secp256k1_uint128 noattr) v_d
     ; secp256k1_uint128_at Tsh ((Signed62.signed (firstn (Z.to_nat i) (Signed62.reprn alen a)))*factor / 2^(62*i)) v_c
     ; data_at shr t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn (Z.to_nat i) (a*factor mod 2^(62*i)))) ptrr
     ; data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
     )
)%assert.
1:{
  rewrite Z.div_1_r, Z.mul_0_l.
  change (Signed62.pad (Signed62.reprn 5 _)) with (repeat Vundef 5).
  entailer!!.
}
1:{
(* TODO Make this an external lemma. *)
  assert (Hfirst : forall i, 0 <= i -> -2 ^ (62 * i + 1) <= Signed62.signed (firstn (Z.to_nat i) (Signed62.reprn alen a)) <= 2 ^ (62 * i + 1) - 1).
  1:{
    clear -H0.
    intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat alen)).
    - rewrite Signed62.signed_firstn_reprn, Z2Nat.id, Z.mul_comm, Z.pow_add_r by lia.
      eapply weaken_bounds;[setoid_rewrite <- strict_bounds;apply Z.mod_pos_bound| |]; try lia.
    - rewrite firstn_same by (rewrite Signed62.reprn_length; lia).
      destruct alen;[simpl;lia|].
      rewrite Signed62.signed_reprn by lia.
      eapply weaken_bounds;[apply H0|apply -> Z.opp_le_mono|apply Z.sub_le_mono_r];apply Z.pow_le_mono_r; lia.
  }
  forward_if (
  PROP ( )
  LOCAL ( temp _i (Vint (Int.repr i))
        ; lvar _d (Tstruct _secp256k1_uint128 noattr) v_d
        ; lvar _c (Tstruct _secp256k1_uint128 noattr) v_c
        ; temp _M62 (Vlong (Int64.repr (2 ^ 62 - 1)))
        ; temp _r ptrr
        ; temp _a ptra
        ; temp _alen (Vint (Int.repr (Z.of_nat alen)))
        ; temp _factor (Vlong (Int64.repr factor))
        )
  SEP( data_at_ Tsh (Tstruct _secp256k1_uint128 noattr) v_d
     ; secp256k1_uint128_at Tsh ((Signed62.signed (firstn (Z.to_nat (Z.succ i)) (Signed62.reprn alen a)))*factor / 2^(62*i)) v_c
     ; data_at shr t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn (Z.to_nat i) (a*factor mod 2^(62*i)))) ptrr
     ; data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
     )
)%assert.
  2:{
    forward.
    rewrite !firstn_same by lia.
    entailer!.
  }
  1:{
    forward; rewrite Signed62.pad_nth by lia;[entailer!|].
    rewrite <- (Int64.repr_signed (Znth i (Signed62.reprn alen a))).
    forward_call;rewrite Hstep by lia;[|entailer!].
    split;
      unfold Int128_min_signed, Int128_max_signed;
      (setoid_rewrite <- strict_bounds';apply div_bounds;rewrite strict_bounds;[lia|];
      eapply weaken_bounds;[
        apply smul_bounds;[apply Hfirst;lia|apply H2]
      | |]); rewrite ?Z.mul_succ_r, !Z.pow_add_r; lia.
  }
  set (c:= _ / _).
  forward_call.
  forward.
  forward_call.
  1:{
    unfold c, Int128_min_signed, Int128_max_signed.
    setoid_rewrite <- strict_bounds';apply div_bounds;rewrite strict_bounds;[lia|].
    eapply weaken_bounds;[
      apply smul_bounds;[apply Hfirst;lia|apply H2]
    | |]; rewrite ?Z.mul_succ_r, !Z.pow_add_r; lia.
  }
  entailer!.
  unfold c at 1.
  rewrite <- Z.add_1_r, Z.shiftr_div_pow2, Zdiv_Zdiv, <- Z.pow_add_r by lia.
  replace (62 * (i + 1)) with (62 * i + 62) by ring.
  entailer!.
  erewrite <- (Z2Nat.id i), <- Signed62.reprn_length, <- Zlength_correct at 1 by lia.
  rewrite Signed62.pad_upd_Znth_end by (rewrite Signed62.reprn_length; lia).
  replace (2^62 - 1) with (Z.ones 62) by apply Z.ones_equiv.
  rewrite Z.land_ones, Z2Nat.inj_add, Nat.add_1_r, Signed62.reprn_succ, Z2Nat.id, Z.pow_add_r by lia.
  rewrite <- Zmod_div_mod, Z.shiftr_div_pow2 by (try lia; auto with *).
  destruct (Z.lt_ge_cases (Z.succ i) (Z.of_nat alen)); unfold c.
  * rewrite Signed62.signed_firstn_reprn, Z2Nat.id, Z.mul_succ_r, Z.pow_add_r,
            <- Zaux.Zdiv_mod_mult, Zmult_mod_idemp_l by lia.
    entailer!.
  * rewrite Zfirstn_same, Signed62.signed_reprn, <- Zaux.Zdiv_mod_mult by lia.
    entailer!.
}
forward_if (
PROP ( )
LOCAL ( lvar _d (Tstruct _secp256k1_uint128 noattr) v_d
      ; lvar _c (Tstruct _secp256k1_uint128 noattr) v_c
      ; temp _M62 (Vlong (Int64.repr (2 ^ 62 - 1)))
      ; temp _r ptrr
      ; temp _a ptra
      ; temp _alen (Vint (Int.repr (Z.of_nat alen)))
      ; temp _factor (Vlong (Int64.repr factor))
      )
SEP( data_at_ Tsh (Tstruct _secp256k1_uint128 noattr) v_d
   ; secp256k1_uint128_at Tsh (a*factor / 2^(62*4)) v_c
   ; data_at shr t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn (Z.to_nat 4) (a*factor mod 2^(62*4)))) ptrr
   ; data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra
   )
)%assert.
2:{
  forward.
  entailer!.
  rewrite Zfirstn_same, Signed62.signed_reprn by lia.
  entailer!.
}
1:{
  forward; rewrite Signed62.pad_nth by lia;[entailer|].
  rewrite <- (Int64.repr_signed (Znth 4 (Signed62.reprn alen a))).
  forward_call;rewrite Hstep by lia;
  [|rewrite Zfirstn_same, Signed62.signed_reprn by lia; entailer!].
  rewrite Signed62.signed_firstn_reprn, Zfirstn_same, Signed62.signed_reprn by lia.
  simpl (62 * _).
  unfold Int128_min_signed, Int128_max_signed.
  split;setoid_rewrite <- strict_bounds';apply div_bounds;rewrite strict_bounds; try lia.
  eapply weaken_bounds;[
        apply usmul_bounds_tight;[setoid_rewrite <- strict_bounds; apply Z.mod_pos_bound|apply H2]
      | |]; lia.
}
forward_call;
[setoid_rewrite <- strict_bounds';apply div_bounds;rewrite strict_bounds; lia|].
rewrite <- Z.shiftr_div_pow2 by lia.
forward_call (v_d, Tsh, (Z.shiftr (a * factor) (62 * 4)));[solve_bounds|].
forward_verify_check.
1:{
  simpl (62 * 4).
  set (n := Z.shiftr (a * factor) 248).
  forward_call.
  rewrite Z.eqb_refl.
  unfold n; clear n.
  forward_if;[discriminate|forward].
  entailer!.
}
forward_call;[solve_bounds|].
forward.
unfold secp256k1_uint128_at.
replace (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 (a * factor))).
* do 2 sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128 (Vlong (Int64.repr (Z.shiftr (a * factor) (62 * 4))),
        Vlong (Int64.repr (Z.shiftr (Z.shiftr (a * factor) (62 * 4)) 64)))).
  entailer!!.
* unfold Signed62.pad, upd_Znth, sublist.
  simpl.
  rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2,
          <- !Zaux.Zdiv_mod_mult, <- !Z.pow_add_r by lia.
  repeat (rewrite <- Zmod_div_mod; try lia; 
  [|match goal with
   |- (2 ^ ?a | 2 ^ ?b) => exists (2^(b - a)); reflexivity
  end]).
  reflexivity.
Qed.

Lemma body_secp256k1_modinv64_mul_cmp_62: semax_body Vprog Gprog f_secp256k1_modinv64_mul_cmp_62 secp256k1_modinv64_mul_cmp_62_spec.
Proof.
start_function.
assert (H311: 2 ^ (62 * Z.of_nat alen + 1) <= 2^311) by
  (apply Z.pow_le_mono_r; lia).
forward_call;[lia|].
forward_call (b, 5%nat, factor, v_bm, ptrb, Tsh, shb).
change (a * Int.signed (Int.repr 1)) with (a * 1).
set (bf := b * factor) in *.
rewrite Z.mul_1_r.
match goal with
| |- semax _ ?E _ _ => forward_for_simple_bound 4 (EX _:Z, E)
end.
1: entailer!.
1: {
  assert (H5a := Signed62.reprn_Zlength 5 a).
  assert (H5b := Signed62.reprn_Zlength 5 bf).
  forward_verify_check;[|forward_verify_check];(
    forward;
    rewrite Signed62.reprn_Znth by lia;
    match goal with
    | |- semax _ ?E _ _ => forward_if E
    end;try (try forward;entailer!);elimtype False;
    revert H5; convert_C_to_math;
    rewrite shiftr_small, Z.eqb_refl;[discriminate|];
    apply Z.mod_pos_bound; lia;
    forward;entailer!).
}
forward_for (fun i:Z =>
   PROP ( -1 <= i < 5 /\ (i = 4 \/ (i < 4 /\ Z.shiftr a (62*(i + 1)) = Z.shiftr bf (62*(i + 1)))) )
   LOCAL (temp _i (Vint (Int.repr i));
   lvar _bm (Tstruct _secp256k1_modinv64_signed62 noattr) v_bm;
   lvar _am (Tstruct _secp256k1_modinv64_signed62 noattr) v_am; 
   temp _a ptra; temp _alen (Vint (Int.repr (Z.of_nat alen))); 
   temp _b ptrb; temp _factor (Vlong (Int64.repr factor)))
   SEP (data_at shb t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn 5 b)) ptrb;
   data_at sha t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn alen a)) ptra;
   data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 bf)) v_bm;
   data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 a)) v_am)).
1: forward; Exists 4; entailer!.
1: entailer!.
2: {
  forward.
  replace x with (-1) in * by lia.
  rewrite !Z.shiftr_0_r in H4.
  destruct H4 as [_ [|[_ ->]]];[lia|].
  rewrite Z.compare_refl.
  entailer!.
}
assert (Ha := Signed62.reprn_Zlength 5 a).
assert (Hbf := Signed62.reprn_Zlength 5 bf).
do 2 forward.
destruct H4 as [Hx [H4|[Hx4 H4]]];forward_if;repeat forward;try forward_if;repeat forward;try entailer!!.
* unfold Znth in H5; simpl in H5.
  revert H5;convert_C_to_math;intros H5.
  rewrite Z.ltb_lt, !Z.shiftr_shiftr in H5 by lia.
  simpl in H5.
  rewrite !Z.shiftr_div_pow2 in H5 by lia.
  rewrite (proj2 (Z.compare_lt_iff _ _));[reflexivity|].
  apply Z.nle_gt; intro; revert H5; apply Z.le_ngt.
  apply Z.div_le_mono; lia.
* unfold Znth in H6; simpl in H6.
  revert H6;convert_C_to_math;intros H6.
  rewrite Z.ltb_lt, !Z.shiftr_shiftr in H6 by lia.
  simpl in H6.
  rewrite !Z.shiftr_div_pow2 in H6 by lia.
  rewrite (proj2 (Z.compare_gt_iff _ _));[reflexivity|].
  apply Z.nle_gt; intro; revert H6; apply Z.le_ngt.
  apply Z.div_le_mono; lia.
* Exists 3.
  entailer!.
  right.
  unfold Znth in H5,H6; simpl in H5,H6.
  revert H5 H6;convert_C_to_math.
  rewrite !Z.ltb_ge, !Z.shiftr_shiftr by lia.
  simpl; unfold bf.
  lia.
* rewrite (proj2 (Z.compare_lt_iff _ _));[reflexivity|].
  rewrite (Z_div_mod_eq_full a (2^(62 * (x + 1)))).
  rewrite (Z_div_mod_eq_full bf (2^(62 * (x + 1)))).
  change (cons (Int64.repr (a mod 2 ^ 62)) _) with (Signed62.reprn 5 a) in H5.
  change (cons _ _) with (Signed62.reprn 5 bf) in H5.
  rewrite !Signed62.reprn_Znth in H5 by lia.
  revert H5;convert_C_to_math;intros H5.
  rewrite Z.ltb_lt, !Z.shiftr_div_pow2, <- !Zaux.Zdiv_mod_mult, <- Z.pow_add_r in H5 by lia.
  replace (62 * x + 62) with (62 * (x + 1)) in H5 by lia.
  rewrite !Z.shiftr_div_pow2 in H4 by lia.
  rewrite H4.
  apply Z.add_le_lt_mono; [lia|].
  apply Z.nle_gt; intro; revert H5; apply Z.le_ngt.
  apply Z.div_le_mono; lia.
* rewrite (proj2 (Z.compare_gt_iff _ _));[reflexivity|].
  rewrite (Z_div_mod_eq_full a (2^(62 * (x + 1)))).
  rewrite (Z_div_mod_eq_full bf (2^(62 * (x + 1)))).
  change (cons (Int64.repr (a mod 2 ^ 62)) _) with (Signed62.reprn 5 a) in H6.
  change (cons _ _) with (Signed62.reprn 5 bf) in H6.
  rewrite !Signed62.reprn_Znth in H6 by lia.
  revert H6;convert_C_to_math;intros H6.
  rewrite Z.ltb_lt, !Z.shiftr_div_pow2, <- !Zaux.Zdiv_mod_mult, <- Z.pow_add_r in H6 by lia.
  replace (62 * x + 62) with (62 * (x + 1)) in H6 by lia.
  rewrite !Z.shiftr_div_pow2 in H4 by lia.
  rewrite H4.
  apply Z.add_le_lt_mono; [lia|].
  apply Z.nle_gt; intro; revert H6; apply Z.le_ngt.
  apply Z.div_le_mono; lia.
* Exists (x-1).
  entailer!.
  right.
  split;[lia|].
  replace (x - 1 + 1) with x by ring.
  rewrite (Z_div_mod_eq_full (Z.shiftr a _) (2^62)).
  rewrite (Z_div_mod_eq_full (Z.shiftr bf _) (2^62)).
  rewrite <- !Z.shiftr_div_pow2, !Z.shiftr_shiftr by lia.
  replace (62 * x + 62) with (62 * (x + 1)) by lia.
  change (cons (Int64.repr (a mod 2 ^ 62)) _) with (Signed62.reprn 5 a) in *.
  change (cons _ _) with (Signed62.reprn 5 bf) in *.
  rewrite !Signed62.reprn_Znth in H5, H6 by lia.
  revert H5 H6;convert_C_to_math.
  rewrite !Z.ltb_ge;lia.
Qed.

Lemma body_secp256k1_modinv64_det_check_pow2: semax_body Vprog Gprog f_secp256k1_modinv64_det_check_pow2 secp256k1_modinv64_det_check_pow2_spec.
Proof.
start_function.
destruct m as [u v q r].
unfold divstep.Trans.bounded in H.
simpl in H.
destruct H as [[Huv _] [Hqr _]].
unfold Trans_repr.
simpl (data_at _ _ _ _).
assert (Hur : -((2 ^ 62 + 1) * (2 ^ 62 + 1))  <= u * r <= (2 ^ 62 + 1) * (2 ^ 62 + 1)) by
  (apply smul_bounds; lia).
assert (Hvq : -((2 ^ 62 + 1) * (2 ^ 62 + 1))  <= v * q <= (2 ^ 62 + 1) * (2 ^ 62 + 1)) by
  (apply smul_bounds; lia).
fastforward 4.
forward_call (v_a, Tsh, u, v, q, r).
forward_call;[unfold Int128_min_signed, Int128_max_signed; lia|].
forward_if.
1: {
  unfold secp256k1_uint128_at.
  sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128
          (Vlong (Int64.repr (u * r - v * q)),
           Vlong (Int64.repr (Z.shiftr (u * r - v * q) 64))) v_a).
  forward; entailer!!.
  revert H.
  elim Z.eqb_spec; cbn; try lia.
  intros -> _.
  rewrite Z.mul_1_l.
  elim Z.eqb_spec; try reflexivity.
  intros e; elim e.
  destruct abs_flag; try reflexivity.
  auto with *.
}
forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (abs_flag && (u * r - v * q =? -2^n)))))).
1: {
  forward_call;[unfold Int128_min_signed, Int128_max_signed; lia|].
  forward; entailer!.
}
1: {
  forward; entailer!.
}
forward_if.
1: {
  unfold secp256k1_uint128_at.
  sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128
          (Vlong (Int64.repr (u * r - v * q)),
           Vlong (Int64.repr (Z.shiftr (u * r - v * q) 64))) v_a).
  forward; entailer!!.
  destruct abs_flag; try discriminate. 
  revert H1.
  elim Z.eqb_spec; unfold Int.zero; cbn; try congruence.
  intros -> _.
  rewrite Z.abs_opp.
  elim Z.eqb_spec; try reflexivity.
  intros e; elim e.
  auto with *.
}
unfold secp256k1_uint128_at.
sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128
        (Vlong (Int64.repr (u * r - v * q)),
         Vlong (Int64.repr (Z.shiftr (u * r - v * q) 64))) v_a).
forward; entailer!!.
cbn.
elim Z.eqb_spec; try reflexivity.
destruct abs_flag;
[replace (2^n) with (Z.abs (2^n)) by auto with *; intros Habs; destruct (Z.abs_eq_cases _ _ Habs)|cbn; intros H5];
try (rewrite H5, Z.mul_1_l, Z.eqb_refl in H; discriminate).
rewrite H5, Z.eqb_refl in H1; discriminate.
Qed.

Lemma body_secp256k1_modinv64_normalize_62: semax_body Vprog Gprog f_secp256k1_modinv64_normalize_62 secp256k1_modinv64_normalize_62_spec.
Proof.
start_function.
assert (H5r := Signed62.reprn_Zlength 5 r).
assert (H5m := Signed62.reprn_Zlength 5 m).
assert (Hrbound : -(2 ^ 62 - 1) <= Z.shiftr r 248 <= 2 ^ 62 - 1) by solve_bounds.
assert (Hmbound : 0 <= Z.shiftr m 248 <= 2 ^ 62 - 1) by solve_bounds.
set (rl := Signed62.reprn 5 r) in *.
set (ml := Signed62.reprn 5 m) in *.
progressC.
change (Z.shiftr (-1 mod 2 ^ 64) 2) with (2^62 - 1). 
fastforward 5.
match goal with
 |- semax _ ?E _ _ => forward_for_simple_bound 5 (EX i:Z, E)
end;[entailer| |].
1:{
  forward_verify_check;[|forward_verify_check].
  1:{
   forward; forward_if;[entailer!; cbn; lia| | forward;entailer].
   revert H3.
   change (Znth i _) with (Znth i (Signed62.reprn 5 r)).
   destruct (Z.lt_ge_cases i 4) as [Hi|Hi].
   * rewrite Signed62.reprn_Znth by lia.
     convert_C_to_math.
     elim Z.ltb_spec0; try discriminate.
     intros H3.
     assert (Hr:=Z.mod_pos_bound (Z.shiftr r (62 * i)) (2 ^ 62)).
     lia.
   * replace i with 4 by lia.
     change 4 with (Zlength (Signed62.reprn 5 r) - 1).
     rewrite Znth_last, Signed62.reprn_last by lia.
     convert_C_to_math.
     elim Z.ltb_spec0; try discriminate.
     cbn;lia.
  }
  1:{
   forward.
   match goal with
    |- semax _ ?E _ _ => forward_if E
   end;[|forward;entailer|forward;entailer].
   revert H3.
   change (Znth i _) with (Znth i (Signed62.reprn 5 r)).
   destruct (Z.lt_ge_cases i 4) as [Hi|Hi].
   * rewrite Signed62.reprn_Znth by lia.
     convert_C_to_math.
     elim Z.ltb_spec0; try discriminate.
     intros H3.
     assert (Hr:=Z.mod_pos_bound (Z.shiftr r (62 * i)) (2 ^ 62)).
     lia.
   * replace i with 4 by lia.
     change 4 with (Zlength (Signed62.reprn 5 r) - 1).
     rewrite Znth_last, Signed62.reprn_last by lia.
     convert_C_to_math.
     elim Z.ltb_spec0; try discriminate.
     cbn;lia.
  }
}
unfold make_modinfo.
assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm) by entailer.
forward_verify_check.
1:{
  forward_call (r, 5%nat, m, -2, ptrr, (field_address t_secp256k1_modinv64_modinfo (DOT _modulus)
        ptrm), shr, shm);
  [rewrite field_address_offset by assumption;entailer!
  |unfold_data_at (data_at _ _ _ ptrm);entailer!|].
  forward_if.
  1:{
    rewrite Zaux.Zcompare_Gt in H3; try discriminate.
    lia.
  }
  forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ ptrm);entailer!.
}
forward_verify_check.
1:{
  forward_call (r, 5%nat, m, 1, ptrr, (field_address t_secp256k1_modinv64_modinfo (DOT _modulus)
        ptrm), shr, shm);
  [rewrite field_address_offset by assumption;entailer!
  |unfold_data_at (data_at _ _ _ ptrm);entailer!|].
  forward_if.
  1:{
    rewrite Zaux.Zcompare_Lt in H3; try discriminate.
    lia.
  }
  forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ ptrm);entailer!.
}
progressC.
change 4 with (Zlength rl - 1);rewrite Znth_last.
unfold rl.
rewrite Signed62.reprn_last by lia.
repeat (rewrite Signed62.reprn_Znth by lia).
convert_C_to_math.
rewrite Z.shiftr_shiftr by lia.
simpl (62 * (Z.of_nat 5 - 1) + 63).
assert (-1 <= Z.shiftr r 311 <= 0) by solve_bounds.
replace (Z.shiftr r 311) with (if r <? 0 then -1 else 0) by
 (elim Z.ltb_spec;
  [rewrite <- (Z.shiftr_neg r 311); intros Hr; replace (Z.shiftr r 311) with (-1) by lia; reflexivity
  |rewrite <- (Z.shiftr_nonneg r 311); intros Hr; replace (Z.shiftr r 311) with 0 by lia; reflexivity]).
assert (Hand : forall (b:bool) x, Z.land x (if b then -1 else 0) =
                                  if b then x else 0) by
  (intros [|] x;rewrite ?Z.land_m1_r, ?Z.land_0_r; reflexivity).
unfold ml in H5m.
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC.
change 4 with (Zlength ml - 1);rewrite Znth_last.
rewrite Signed62.reprn_last by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
rewrite !Hand.
progressC.
assert (-1 <= Z.shiftr (Int64.signed sign) 63 <= 0) by solve_bounds.
replace (Z.shiftr (Int64.signed sign) 63) with (if Int64.signed sign <? 0 then -1 else 0) by
(elim Z.ltb_spec;
 [rewrite <- (Z.shiftr_neg (Int64.signed sign) 63); intros Hsign; replace (Z.shiftr (Int64.signed sign) 63) with (-1) by lia; reflexivity
 |rewrite <- (Z.shiftr_nonneg (Int64.signed sign) 63); intros Hsign; replace (Z.shiftr (Int64.signed sign) 63) with 0 by lia; reflexivity]).
assert (Hxor : forall (b:bool) x, Z.lxor x (if b then -1 else 0) = if b then (-x-1) else x) by
 (intros [|] x; rewrite ?Z_neg_lnot, ?Z.lxor_m1_r, ?Z.lxor_0_r; ring).
progressC;rewrite Hxor;
[destruct (Int64.signed sign <? 0);rewrite ?Z.sub_0_r;convert_C_to_math;solve_bounds|].
progressC;rewrite Hxor;
[destruct (Int64.signed sign <? 0);rewrite ?Z.sub_0_r;convert_C_to_math;solve_bounds|].
progressC;rewrite Hxor;
[destruct (Int64.signed sign <? 0);rewrite ?Z.sub_0_r;convert_C_to_math;solve_bounds|].
progressC;rewrite Hxor;
[destruct (Int64.signed sign <? 0);rewrite ?Z.sub_0_r;convert_C_to_math;solve_bounds|].
progressC;rewrite Hxor;
[destruct (Int64.signed sign <? 0);rewrite ?Z.sub_0_r;convert_C_to_math;solve_bounds|].
assert (Hsub : forall (b:bool) x y, (if b then x - 1 else y) - (if b then -1 else 0) =
                                    if b then x else y) by
 (intros [|] x y; ring).
rewrite !Hsub.
rewrite (Z.sub_1_r (2^_)), <- Z.ones_equiv.
set (s4 := if Int64.signed sign <? 0 then _ else _).
set (s3 := if Int64.signed sign <? 0 then _ else _).
set (s2 := if Int64.signed sign <? 0 then _ else _).
set (s1 := if Int64.signed sign <? 0 then _ else _).
set (s0 := if Int64.signed sign <? 0 then _ else _).
assert (Hs0 : -2^63 + 2 <= s0 <= 2^63 - 2) by solve_bounds.
assert (Hs1 : -2^63 + 2 <= s1 <= 2^63 - 2) by solve_bounds.
assert (Hs2 : -2^63 + 2 <= s2 <= 2^63 - 2) by solve_bounds.
assert (Hs3 : -2^63 + 2 <= s3 <= 2^63 - 2) by solve_bounds.
assert (Hs4 : -2^63 + 2 <= s4 <= 2^63 - 2) by solve_bounds.
do 8 progressC.
rewrite !Z.land_ones by lia.
pose (s' := s0 + s1 * 2 ^ 62 + s2 * 2 ^ 62 * 2 ^ 62 + s3 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62
      + s4 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62).
replace (s4 + _) with (Z.shiftr s' (62 * 4)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
reflexivity.
}
replace ((s3 + _) mod 2^62) with ((Z.shiftr s' (62 * 3)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
unfold s'.
rewrite <- !Z.mul_assoc;
change (2 ^ 62 * (2 ^ 62 * 2 ^ 62)) with (2 ^ (62 * 3));
rewrite !Z.mul_assoc.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace ((s2 + _) mod 2^62) with ((Z.shiftr s' (62 * 2)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
unfold s'.
rewrite <- !Z.mul_assoc;
change (2 ^ 62 * 2 ^ 62) with (2 ^ (62 * 2));
rewrite !Z.mul_assoc.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace ((s1 + _) mod 2^62) with ((Z.shiftr s' (62 * 1)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus by lia.
unfold s'.
rewrite Z.mul_1_r.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace (s0 mod 2^62) with ((Z.shiftr s' (62 * 0)) mod (2^62)).
2:{
change (Z.shiftr s' (62 * 0)) with s'.
unfold s'.
rewrite !Z_mod_plus_full by lia.
reflexivity.
}
pose (s := if Int64.signed sign <? 0 then -(r + if r <? 0 then m else 0) else r + if r <? 0 then m else 0).
replace s' with s by
(unfold s, s';
destruct (Int64.signed sign <? 0) in *; destruct (r <? 0) in *;
change r with (Z.shiftr r 0);
change m with (Z.shiftr m 0);
do 4 rewrite (Z_div_mod_eq (Z.shiftr r _) (2^62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
try do 4 rewrite (Z_div_mod_eq (Z.shiftr m _) (2^62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
unfold s0, s1, s2, s3, s4; cbn; ring
).
clear s' Hs0 Hs1 Hs2 Hs3 Hs4 s0 s1 s2 s3 s4.
assert (Hsbound : -(2 ^ 62 - 1) <= Z.shiftr s (62 * 4) <= 2 ^ 62 - 1) by
  (unfold s; elim (Z.ltb_spec r); intro; solve_bounds).
progressC.
rewrite Z.shiftr_shiftr by lia.
simpl (62 * _ + 63).
assert (-1 <= Z.shiftr s 311 <= 0) by (unfold s; elim (Z.ltb_spec r); intro; solve_bounds).
replace (Z.shiftr s 311) with (if s <? 0 then -1 else 0) by
 (elim Z.ltb_spec;
  [rewrite <- (Z.shiftr_neg s 311); intros Hr; replace (Z.shiftr s 311) with (-1) by lia; reflexivity
  |rewrite <- (Z.shiftr_nonneg s 311); intros Hr; replace (Z.shiftr s 311) with 0 by lia; reflexivity]).
cbn in Hsbound.
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC;rewrite Signed62.reprn_Znth by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
progressC.
change 4 with (Zlength ml - 1);rewrite Znth_last.
unfold ml.
rewrite Signed62.reprn_last by lia.
progressC;[rewrite Hand;convert_C_to_math;solve_bounds|].
rewrite !Hand.
set (t4 := Z.shiftr s _ + _).
set (t3 := _ mod _ + _).
set (t2 := _ mod _ + _).
set (t1 := _ mod _ + _).
set (t0 := _ mod _ + _).
assert (Ht0 : -2^63 + 2 <= t0 <= 2^63 - 2) by solve_bounds.
assert (Ht1 : -2^63 + 2 <= t1 <= 2^63 - 2) by solve_bounds.
assert (Ht2 : -2^63 + 2 <= t2 <= 2^63 - 2) by solve_bounds.
assert (Ht3 : -2^63 + 2 <= t3 <= 2^63 - 2) by solve_bounds.
cbn in t4.
assert (Ht4 : -2^63 + 2 <= t4 <= 2^63 - 2) by solve_bounds.
do 8 progressC.
rewrite !Z.land_ones by lia.
pose (t' := t0 + t1 * 2 ^ 62 + t2 * 2 ^ 62 * 2 ^ 62 + t3 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62
      + t4 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62).
replace (t4 + _) with (Z.shiftr t' (62 * 4)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
reflexivity.
}
replace ((t3 + _) mod 2^62) with ((Z.shiftr t' (62 * 3)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
unfold t'.
rewrite <- !Z.mul_assoc;
change (2 ^ 62 * (2 ^ 62 * 2 ^ 62)) with (2 ^ (62 * 3));
rewrite !Z.mul_assoc.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace ((t2 + _) mod 2^62) with ((Z.shiftr t' (62 * 2)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus, !Zdiv_Zdiv by lia.
unfold t'.
rewrite <- !Z.mul_assoc;
change (2 ^ 62 * 2 ^ 62) with (2 ^ (62 * 2));
rewrite !Z.mul_assoc.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace ((t1 + _) mod 2^62) with ((Z.shiftr t' (62 * 1)) mod (2^62)).
2:{
rewrite !Z.shiftr_div_pow2, !(Z.add_comm _ (_ / _)), <- !Z_div_plus by lia.
unfold t'.
rewrite Z.mul_1_r.
rewrite !Z_div_plus_full, !Z_mod_plus_full by lia.
reflexivity.
}
replace (t0 mod 2^62) with ((Z.shiftr t' (62 * 0)) mod (2^62)).
2:{
change (Z.shiftr t' (62 * 0)) with t'.
unfold t'.
rewrite !Z_mod_plus_full by lia.
reflexivity.
}
pose (t := (if Int64.signed sign <? 0 then -r else r) mod m).
assert (Hrm : -m < r + (if r <? 0 then m else 0) < m) by 
 (elim Z.ltb_spec; lia).
assert (Hsm : -m < s < m) by
 (unfold s; elim Z.ltb_spec; lia).
replace t' with t.
2:{
 transitivity (if s <? 0 then s + m else s);
 [|unfold t';
  destruct (s <? 0) in *;
  change s with (Z.shiftr s 0);
  change m with (Z.shiftr m 0);
  do 4 rewrite (Z_div_mod_eq (Z.shiftr s _) (2^62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
  try do 4 rewrite (Z_div_mod_eq (Z.shiftr m _) (2^62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
  unfold t0, t1, t2, t3, t4; cbn;ring
 ].
 unfold t.
 apply Zdivide_mod_minus.
 * elim Z.ltb_spec; lia.
 * unfold s; destruct (_ <? 0); destruct (_ <? 0); destruct (_ <? 0);
   match goal with
   | |- (m | ?x) => ring_simplify x
   end;
   solve [auto with *].
}
clear t' Ht0 Ht1 Ht2 Ht3 Ht4 t0 t1 t2 t3 t4.
do 5 progressC.

do 5 (forward_verify_check;[
 revert H6; convert_C_to_math;
 elim Z.eqb_spec; try discriminate;
 intros H6 _; apply H6;
 apply shiftr_small; rewrite strict_bounds;
 solve_bounds
|]).
change (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 t)).
assert (Ht0: 0 <= t < m) by (apply Z.mod_pos_bound; lia).
forward_verify_check.
1:{
  forward_call (t, 5%nat, m, 0, ptrr, (field_address t_secp256k1_modinv64_modinfo (DOT _modulus)
        ptrm), shr, shm);
  [rewrite field_address_offset by assumption;entailer!
  |unfold_data_at (data_at _ _ _ ptrm);entailer!|].
  forward_if.
  1:{
    revert H6.
    fold t.
    elim Z.compare_spec; try discriminate.
    lia.
  }
  forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ ptrm);entailer!.
}
forward_verify_check.
1:{
  forward_call (t, 5%nat, m, 1, ptrr, (field_address t_secp256k1_modinv64_modinfo (DOT _modulus)
        ptrm), shr, shm);
  [rewrite field_address_offset by assumption;entailer!
  |unfold_data_at (data_at _ _ _ ptrm);entailer!|].
  match goal with
   |- semax _ ?E _ _ => forward_if E
  end.
  * revert H6.
    fold t.
    rewrite Zaux.Zcompare_Lt; try discriminate.
    lia.
  * forward. entailer!.
  * forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ ptrm);entailer!.
}
Qed.

Lemma body_secp256k1_modinv64_divsteps_62_var: semax_body Vprog Gprog f_secp256k1_modinv64_divsteps_62_var secp256k1_modinv64_divsteps_62_var_spec.
Proof.
start_function.
do 7 forward.
forward_loop (EX i:nat, EX j:nat, EX u:Z, EX v:Z, EX f:Z, EX g:Z,
 PROP ( Z.of_nat j <= Z.of_nat i <= 62
      ; divstep.Trans.u (divstep.Trans.transN i st) = (u * 2^(Z.of_nat j))%Z
      ; divstep.Trans.v (divstep.Trans.transN i st) = (v * 2^(Z.of_nat j))%Z
      ; eqm (2^(64 - Z.of_nat i)) f (divstep.f (fst (divstep.stepN i st)))
      ; eqm (2^(64 - Z.of_nat i)) g (divstep.g (fst (divstep.stepN i st)))
      )
  LOCAL (temp _i (Vint (Int.repr (62 - Z.of_nat i + Z.of_nat j)));
   temp _g (Vlong (Int64.repr (g * 2^(Z.of_nat j))));
   temp _f (Vlong (Int64.repr f));
   temp _r (Vlong (Int64.repr (divstep.Trans.r (divstep.Trans.transN i st))));
   temp _q (Vlong (Int64.repr (divstep.Trans.q (divstep.Trans.transN i st))));
   temp _v (Vlong (Int64.repr v));
   temp _u (Vlong (Int64.repr u)); 
   gvars gv; temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.stepN i st)) + Z.of_nat j)));
   temp _f0 (Vlong (Int64.repr (divstep.f st)));
   temp _g0 (Vlong (Int64.repr (divstep.g st))); temp _t t)
 SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
   debruijn64_array sh_debruijn gv)
)%assert
break:(
 PROP ( )
  LOCAL (
   temp _r (Vlong (Int64.repr (divstep.Trans.r (divstep.Trans.transN 62 st))));
   temp _q (Vlong (Int64.repr (divstep.Trans.q (divstep.Trans.transN 62 st))));
   temp _v (Vlong (Int64.repr (divstep.Trans.v (divstep.Trans.transN 62 st))));
   temp _u (Vlong (Int64.repr (divstep.Trans.u (divstep.Trans.transN 62 st)))); 
   gvars gv; temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.stepN 62 st)))));
   temp _t t)
 SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
   debruijn64_array sh_debruijn gv)
)%assert.
* Exists 0%nat; Exists 0%nat;
  Exists (divstep.Trans.u (divstep.Trans.transN 0 st)); Exists (divstep.Trans.v (divstep.Trans.transN 0 st));
  Exists (divstep.f (fst (divstep.stepN 0 st)));Exists (divstep.g (fst (divstep.stepN 0 st)));
  entailer!.
* Intros n j u v f g;
  rename H4 into Hg;
  rename H3 into Hf;
  rename H2 into Hv;
  rename H1 into Hu;
  rename H0 into Hn.
  assert (Hmask : 0 <> (-1 * 2 ^ (62 - Z.of_nat n + Z.of_nat j)) mod (2^64)).
  1:{
    intros Hzero; symmetry in Hzero.
    apply Zmod_divide in Hzero; try lia.
    replace 64 with ((2 + Z.of_nat n - Z.of_nat j) + (62 - Z.of_nat n + Z.of_nat j)) in Hzero by ring.
    rewrite !Z.pow_add_r, Z.mul_divide_cancel_r, (Z.divide_opp_r _ 1) in Hzero by lia.
    apply Z.divide_1_r_nonneg in Hzero; try lia.
    replace (2 + Z.of_nat n - Z.of_nat j) with (2 + (Z.of_nat n - Z.of_nat j)) in Hzero by ring.
    rewrite Z.pow_add_r in Hzero by lia.
    lia.
  }
  assert (Hbound := Z.mod_pos_bound (-1 * 2 ^ (62 - Z.of_nat n + Z.of_nat j)) (2 ^ 64)).
  assert (Heta := divstep.etaBounds 683 n st H).
  assert (Hfodd : Zodd f).
  1:{
    apply Zodd_bool_iff.
    assert (Hf0 := Zmod_odd f).
    revert Hf0.
    destruct (Z.odd f); try reflexivity.
    assert (H2 : (2 | 2 ^ (64 - Z.of_nat n))) by (apply Zpow_facts.Zpower_divide; lia).
    rewrite (Zmod_div_mod 2 (2 ^ (64 - Z.of_nat n))), Hf, <- (Zmod_div_mod 2 (2 ^ (64 - Z.of_nat n)))
      by (try lia; assumption).
    assert (Hfodd := divstep.oddF (fst (divstep.stepN n st))).
    apply Zodd_bool_iff in Hfodd.
    assert (Hmod := Zmod_odd (divstep.f (fst (divstep.stepN n st)))).
    rewrite Hfodd in Hmod.
    rewrite Hmod.
    discriminate.
  }
  assert (Hgcd : forall z a, Zodd z -> 0 <= a -> Z.gcd z (2 ^ a) = 1).
  1:{
    intros z a Hz Ha.
    apply Zgcd_1_rel_prime.
    apply Zpow_facts.rel_prime_Zpower_r;[lia|].
    apply rel_prime_mod_rev;[lia|].
    rewrite Zmod_odd.
    replace (Z.odd z) with true;[apply rel_prime_1|].
    symmetry; apply Zodd_bool_iff.
    assumption.
  }
  forward_call.
  1:{ change (Int.unsigned Int64.iwordsize') with 64; lia. }
  1:{ split;
      [|unfold_C; rewrite Z_log2_lt_pow2, Z.log2_lor, Z.max_lub_lt_iff, <- !Z_log2_lt_pow2; rep_lia].
      apply Z_lor_pos; try rep_lia.
      convert_C_to_math.
      lia.
  }
  convert_C_to_math.
  set (g' := g * _).
  assert (Hgbound := Z.mod_pos_bound g' (2 ^ 64)).
  set (zeros := (Z_ctz _)).
  assert (Hzeros_pos : 0 <= zeros) by apply Z_ctz_non_neg.
  assert (Hzeros62 : zeros <= 62 - Z.of_nat n + Z.of_nat j).
  1:{
   unfold zeros.
   rewrite Z.lor_comm.
   etransitivity.
   * apply Z_ctz_lor_l.
     lia.
   * apply Z.nlt_ge.
     intros Hctz.
     apply Z_ctz_testbit_false in Hctz.
     rewrite Z.mod_pow2_bits_low, <- two_p_equiv, Z.mul_comm, <- Z.opp_eq_mul_m1,
             Zbits.Ztestbit_neg_two_p in Hctz by lia.
     destruct zlt in Hctz; lia.
  }
  assert (Hg'zeros : (2^zeros | g')).
  1:{
   apply Zmod_divide;[auto with *|].
   apply Z.bits_inj_0; intros k.
   destruct (Z_le_lt_dec 0 k);[|auto using Z.testbit_neg_r].
   rewrite <- two_p_equiv, Zbits.Ztestbit_mod_two_p by lia.
   destruct zlt as [Hk|Hk];[|reflexivity].
   rewrite <- (Z.mod_pow2_bits_low _ 64) by lia.
   destruct (Z.eq_dec (g' mod 2^64) 0) as [->|Hne];[apply Z.bits_0|].
   apply Z_ctz_testbit_false.
   eapply Z.lt_le_trans;[apply Hk|].
   apply Z_ctz_lor_l; assumption.
  }
  assert (Hzeros_opt: forall i, (2^i | g') -> i <= 62 - Z.of_nat n + Z.of_nat j -> i <= zeros).
  1:{
    intros i Hig Hi62.
    apply Z.lt_pred_le.
    apply Z_testbit_false_ctz;[apply Z_lt_neq;apply Z_lor_pos; lia|].
    intros k Hk.
    destruct Hig as [m ->].
    rewrite Z.lor_spec, orb_false_iff, !Z.mod_pow2_bits_low, Z.mul_pow2_bits_low by lia.
    rewrite <- two_p_equiv, Z.mul_comm, <- Z.opp_eq_mul_m1, Zbits.Ztestbit_neg_two_p by lia.
    elim zlt; lia.
  }
  do 5 progressC.
  unfold g'.
  replace 64 with (zeros + (64 - zeros)) by ring.
  rewrite Z.pow_add_r, (Z.shiftr_div_pow2 _ zeros), Zaux.Zdiv_mod_mult by lia.
  replace zeros with (Z.of_nat j + (zeros - Z.of_nat j)) by ring.
  set (k := zeros - Z.of_nat j).
  assert (Hk : 0 <= k).
  1:{
    apply Z.nlt_ge.
    intros Hk.
    cut (zeros + 1 <= zeros);[lia|].
    apply Hzeros_opt;[|lia].
    etransitivity;[|apply Z.divide_factor_r].
    apply Zmod_divide;try lia.
    replace (Z.of_nat j) with ((-1 - k) + (zeros + 1)) by (unfold k; ring).
    rewrite Z.pow_add_r by lia.
    apply Z_mod_mult.
  }
  rewrite !Z.pow_add_r, !Z.mul_assoc, <- Hu, <- Hv by lia.
  clear u v Hu Hv.
  replace (62 - Z.of_nat n + Z.of_nat j - (Z.of_nat j + k))
   with (62 - Z.of_nat n - k) by ring.
  replace (divstep.eta (fst (divstep.stepN n st)) + Z.of_nat j - (Z.of_nat j + k))
   with (divstep.eta (fst (divstep.stepN n st)) - k) by ring.
  rewrite (Z.mul_comm g), Zdiv_mult_cancel_l by lia.
  assert (Hkn : (2 ^ k | 2 ^ (64 - Z.of_nat n))).
  1:{
    replace (64 - Z.of_nat n) with (k + (64 - Z.of_nat n - k)) by ring.
    rewrite Z.pow_add_r by lia.
    apply Z.divide_factor_l.
  }
  assert (Hgzeros : (2 ^ k | divstep.g (fst (divstep.stepN n st)))).
  1:{
    apply Zmod_divide; try lia.
    rewrite (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n))), <- Hg, <-Zmod_div_mod by (try lia; assumption).
    apply Zdivide_mod.
    eapply Z.mul_divide_cancel_r;[|etransitivity;[|apply Hg'zeros]];[lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (k + Z.of_nat j) with zeros by (unfold k; ring).
    reflexivity.
  }
  rewrite <- (Z2Nat.id _ Hk) in Hgzeros |- *.
  rewrite <- divstep.etaHs by assumption.
  set (g1 := ((g / _) mod _)).
  assert (Hg1 : eqm (2 ^ (64 - Z.of_nat n - k)) g1 (divstep.g (fst (divstep.stepN (Z.to_nat k) (fst (divstep.stepN n st)))))).
  1:{
    rewrite divstep.gHs by assumption.
    unfold eqm, g1.
    rewrite (Z2Nat.id _ Hk).
    rewrite <- Zmod_div_mod; try lia.
    2:{
      replace (64 - (Z.of_nat j + k)) with ((64 - Z.of_nat n - k) + (0 - Z.of_nat j + Z.of_nat n)) by ring. 
      rewrite Z.pow_add_r by lia.
      apply Z.divide_factor_l.
    }
    rewrite <- !Zaux.Zdiv_mod_mult by lia.
    rewrite <- Z.pow_add_r by lia.
    replace (k + (64 - Z.of_nat n - k)) with (64 - Z.of_nat n) by ring.
    f_equal.
    assumption.
  }
  assert (Hf1 : eqm (2 ^ (64 - Z.of_nat n - k)) f (divstep.f (fst (divstep.stepN (Z.to_nat k) (fst (divstep.stepN n st)))))).
  1:{
    rewrite divstep.fHs by assumption.
    unfold eqm.
    rewrite (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n - k + k)) (divstep.f _)),
            (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n - k + k))) by (try lia;rewrite Z.pow_add_r by lia; apply Z.divide_factor_l).
    f_equal.
    replace (64 - Z.of_nat n - k + k) with (64 - Z.of_nat n) by ring.
    assumption.
  }
  rewrite <- divstep.stepN_app_fst in *.
  assert (trans_n_k := divstep.Trans.transN_stepN (Z.to_nat k) n st).
  rewrite divstep.Trans.transHs in trans_n_k by assumption.
  unfold divstep.Trans.mul in trans_n_k.
  cbn in trans_n_k.
  rewrite !Z.mul_0_l, !Z.mul_1_l, !Z.add_0_r in trans_n_k.
  replace (divstep.Trans.v (divstep.Trans.transN n st) * 2 ^ Z.of_nat (Z.to_nat k))
   with (divstep.Trans.v (divstep.Trans.transN (Z.to_nat k + n) st))
   by (rewrite <- trans_n_k; cbn; ring).
  replace (divstep.Trans.u (divstep.Trans.transN n st) * 2 ^ Z.of_nat (Z.to_nat k))
   with (divstep.Trans.u (divstep.Trans.transN (Z.to_nat k + n) st))
   by (rewrite <- trans_n_k; cbn; ring).
  replace (divstep.Trans.r (divstep.Trans.transN n st))
   with (divstep.Trans.r (divstep.Trans.transN (Z.to_nat k + n) st))
   by (rewrite <- trans_n_k; reflexivity).
  replace (divstep.Trans.q (divstep.Trans.transN n st))
   with (divstep.Trans.q (divstep.Trans.transN (Z.to_nat k + n) st))
   by (rewrite <- trans_n_k; reflexivity).
  replace (62 - Z.of_nat n - Z.of_nat (Z.to_nat k))
   with (62 - Z.of_nat (Z.to_nat k + n)) by lia.
  replace (64 - Z.of_nat n - k)
   with (64 - Z.of_nat (Z.to_nat k + n)) in * by lia.
  set (n1 := (Z.to_nat k + n)%nat) in *.
  assert (Hn1 : 0 <= Z.of_nat n1 <= 62) by lia.
  assert (Hg1odd : Zodd g1 \/ n1 = 62%nat).
  1:{
    destruct (Zeven_odd_dec g1) as [Hg1even|Hg1odd];[|tauto].
    right.
    apply Zeven_div2 in Hg1even.
    rewrite (Z_div_mod_eq_full g1 2) in Hg1even at 1.
    rewrite Z.div2_div in Hg1even.
    assert (Hgeven : g1 mod 2 = 0) by lia.
    clear Hg1even.
    unfold g1 in Hgeven.
    rewrite <- Zmod_div_mod, (* <- Zaux.Zdiv_mod_mult, *) (Z2Nat.id _ Hk) in Hgeven; try lia.
    2:apply Zpow_facts.Zpower_divide; lia.
    cut (2 ^ (zeros + 1) | g').
    1:intros Hg';specialize (Hzeros_opt (zeros + 1) Hg');lia.
    apply Zmod_divide; try lia.
    apply Zdivide_mod in Hg'zeros.
    rewrite Z.pow_add_r, Z.rem_mul_r, Hg'zeros, Z.add_0_l by lia.
    replace 0 with (2 ^ zeros * 0) by ring.
    rewrite Z.mul_cancel_l by lia.
    unfold g'.
    replace zeros with (k + Z.of_nat j) by lia.
    rewrite Z.pow_add_r, Zdiv_mult_cancel_r by lia.
    assumption.
  }
  clearbody n1 k g1.
  clear zeros Hzeros_pos Hzeros62 Hg'zeros Hzeros_opt Hk Hkn Hgzeros g' Hgbound Hf Hg g Hmask Hbound Hn n Heta trans_n_k.
  forward_if;change (62 - _) with (62 - Z.of_nat n1) in H0.
  1:{
    rewrite H0.
    replace n1 with 62%nat by lia.
    forward.
    entailer!.
  }
  assert (Hn162 : Z.of_nat n1 < 62) by lia.
  clear H0.
  destruct Hg1odd as [Hg1odd|Hg1odd];[|lia].
  forward_verify_check.
  1:{
    revert H0.
    convert_C_to_math.
    change (Z.land f 1) with (Z.land f (Z.ones 1)).
    rewrite Z.land_ones by lia.
    change (2^1) with 2.
    rewrite (Zmod_div_mod 2 (2 ^ (64 - Z.of_nat n1)))
     by (try lia; apply Zpow_facts.Zpower_divide; lia).
    rewrite Hf1.
    rewrite <- (Zmod_div_mod 2)
     by (try lia; apply Zpow_facts.Zpower_divide; lia).
    rewrite Zmod_odd.
    assert (Hf1odd := divstep.oddF (fst (divstep.stepN n1 st))).
    rewrite <- Zodd_bool_iff in Hf1odd.
    rewrite Hf1odd, Z.eqb_refl.
    cbn.
    discriminate.
  }
  forward_verify_check.
  1:{
    revert H0.
    convert_C_to_math.
    change (Z.land g1 1) with (Z.land g1 (Z.ones 1)).
    rewrite Z.land_ones by lia.
    change (2^1) with 2.
    rewrite Zmod_odd.
    rewrite <- Zodd_bool_iff in Hg1odd.
    rewrite Hg1odd, Z.eqb_refl.
    cbn.
    discriminate.
  }
  assert (Hstepn := divstep.Trans.transN_step n1 st).
  injection Hstepn; intros Hstepng Hstepnf; clear Hstepn.
  assert (Hshift : 62 - (62 - Z.of_nat n1) < 64) by lia.
  forward_verify_check.
  1:{
    assert (Hfshift : eqm (2^64) (2 ^ Z.of_nat n1 * f) (2 ^ Z.of_nat n1 * divstep.f (fst (divstep.stepN n1 st)))).
    1:{
      unfold eqm.
      replace 64 with (Z.of_nat n1 + (64 - Z.of_nat n1)) by ring.
      rewrite Z.pow_add_r, !Zmult_mod_distr_l, Hf1; lia.
    }
    rewrite Hstepnf in Hfshift.
    revert H0.
    convert_C_to_math.
    replace (62 - _) with (Z.of_nat n1) by ring.
    rewrite <- Hfshift, (Z.mul_comm f), Z.eqb_refl.
    discriminate.
  }
  forward_verify_check.
  1:{
    assert (Hgshift : eqm (2^64) (2 ^ Z.of_nat n1 * g1) (2 ^ Z.of_nat n1 * divstep.g (fst (divstep.stepN n1 st)))).
    1:{
      unfold eqm.
      replace 64 with (Z.of_nat n1 + (64 - Z.of_nat n1)) by ring.
      rewrite Z.pow_add_r, !Zmult_mod_distr_l, Hg1; lia.
    }
    rewrite Hstepng in Hgshift.
    revert H0.
    convert_C_to_math.
    replace (62 - _) with (Z.of_nat n1) by ring.
    rewrite <- Hgshift, (Z.mul_comm g1), Z.eqb_refl.
    discriminate.
  }
  clear Hstepng Hstepnf.
  assert (Heta := divstep.etaBounds 683 n1 st H).
  forward_verify_check.
  1:{
    forward_if (temp _t'2 (Vint Int.one));
    [| |forward_if; try discriminate; forward; entailer!];
    forward; entailer!; revert H0; convert_C_to_math;
    try lia.
    cbn; convert_C_to_math.
    elim Z.ltb_spec0; try lia; reflexivity.
  }
  forward_if (EX n2 : nat, EX u:Z, EX v:Z, EX f2:Z, EX g2:Z, EX w: int,
  PROP ( 1 <= Z.of_nat n2 <= 62 - Z.of_nat n1; Z.of_nat n2 <= 32
      ; divstep.Trans.u (divstep.Trans.transN (n1 + n2) st) = (u * 2^(Z.of_nat n2))%Z
      ; divstep.Trans.v (divstep.Trans.transN (n1 + n2) st) = (v * 2^(Z.of_nat n2))%Z
      ; eqm (2^(64 - Z.of_nat (n1 + n2))) f2 (divstep.f (fst (divstep.stepN (n1 + n2) st)))
      ; eqm (2^(64 - Z.of_nat (n1 + n2))) g2 (divstep.g (fst (divstep.stepN (n1 + n2) st)))
      )
  LOCAL (temp _i (Vint (Int.repr (62 - Z.of_nat n1)));
   temp _g (Vlong (Int64.repr (g2 * 2^(Z.of_nat n2) - f2 * Int.unsigned w)));
   temp _f (Vlong (Int64.repr f2));
   temp _r (Vlong (Int64.repr (divstep.Trans.r (divstep.Trans.transN (n1 + n2) st) - v * Int.unsigned w)));
   temp _q (Vlong (Int64.repr (divstep.Trans.q (divstep.Trans.transN (n1 + n2) st) - u * Int.unsigned w)));
   temp _v (Vlong (Int64.repr v));
   temp _u (Vlong (Int64.repr u)); 
   temp _m (Vlong (Int64.repr (Z.ones (Z.of_nat n2))));
   temp _w (Vint w);
   gvars gv; temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.stepN (n1 + n2) st)) + Z.of_nat n2)));
   temp _f0 (Vlong (Int64.repr (divstep.f st)));
   temp _g0 (Vlong (Int64.repr (divstep.g st)));
   temp _t t)
 SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
   debruijn64_array sh_debruijn gv)
)%assert.
  1:{
    do 10 progressC.
    forward_if (temp _t'3 (Vint (Int.repr (Z.min (62 - Z.of_nat n1) ((-divstep.eta (fst (divstep.stepN n1 st))) + 1)))));
    try (progressC; revert H1; rewrite <- add_repr);
    try rewrite Int_repr_Int64_Z_mod_modulus;
    try entailer;
    try rewrite add_repr;
    convert_C_to_math;
    try lia;
    try (intros H1;first [rewrite Z.min_l by lia|rewrite Z.min_r by lia];reflexivity).
    progressC.
    forward_verify_check.
    1:{
      forward_if (temp _t'4 (Vint Int.one)); try lia.
      1:{
        progressC.
        destruct (zlt _ _); try lia.
        reflexivity.
      }
      forward_if; try discriminate.
      forward; entailer!.
    }
    replace ((Z.of_nat j + Z.of_nat (Z.to_nat k)
               + (64 - (Z.of_nat j + Z.of_nat (Z.to_nat k))))) with 64 by ring.
    progressC.
    change 63 with (Z.ones 6).
    rewrite <- Z.land_ones, Z.land_m1_l, Z_shiftr_ones, subsub1, Z_land_ones_min by lia.
    set (n2 := (Z.min _ 6)).
    pose (w := (modInv (-g1) (2^n2) * (-f)) mod (2^n2)).
    progressC.
    Exists (Z.to_nat n2) (divstep.Trans.q (divstep.Trans.transN n1 st)) (divstep.Trans.r (divstep.Trans.transN n1 st)) g1
           ((-f + g1 * w) / 2^n2)
           (Int.repr w).
    entailer!.
    rewrite Nat.add_comm.
    rewrite <- divstep.Trans.transN_stepN.
    assert (Hgn1 : Zodd (divstep.g (fst (divstep.stepN n1 st)))).
    1:{
      rewrite <- Zodd_bool_iff, <- Z.bit0_odd in *|-*.
      change (Z.testbit (divstep.g (fst (divstep.stepN n1 st))) 0)
       with (true && (Z.testbit (divstep.g (fst (divstep.stepN n1 st))) 0))%bool.
      rewrite <- (Z.ones_spec_low (64 - Z.of_nat n1) 0) at 1 by lia.
      rewrite <- Z.land_spec, Z.land_comm, Z.land_ones, <- Hg1,
              <- Z.land_ones, Z.land_comm, Z.land_spec, Z.ones_spec_low by lia.
      assumption.
    }
    rewrite divstep.Trans.transDs;
    try solve [assumption|unfold divstep.eta in H0; unfold n2, divstep.eta; lia].
    split;[cbn; ring|].
    split;[cbn; ring|].
    rewrite Nat2Z.inj_add, Z2Nat.id, divstep.stepN_app_fst by lia.
    injection (divstep.Trans.transN_step (Z.to_nat n2) (fst (divstep.stepN n1 st))); intros Hg2 Hf2.
    rewrite divstep.Trans.transDs in Hf2, Hg2;
    try solve [assumption|unfold divstep.eta in H0; unfold n2, divstep.eta; lia].
    cbn in Hf2, Hg2.
    ring_simplify in Hf2; ring_simplify in Hg2.
    assert (Hw : 0 <= w < 2^6).
    1:{
      assert (0 < 2^n2 <= 2^6) by (split;[|apply Z.pow_le_mono_r];lia).
      pose (Z.mod_pos_bound (modInv (-g1) (2 ^ n2) * (-f)) (2 ^ n2)).
      lia.
    }
    convert_C_to_math.
    assert (Hg1fw : (2^n2 | (-f) + g1 * w)).
    1: {
      apply Zmod_divide;[lia|].
      unfold w.
      rewrite <- Zplus_mod_idemp_r, Zmult_mod_idemp_r, Zplus_mod_idemp_r, Z.mul_assoc,
              <- Z.sub_opp_r, !Zopp_mult_distr_l, <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l,
              modInv_mul_r, Z.gcd_opp_l.
      rewrite Hgcd by assumption || lia.
      rewrite Zmult_mod_idemp_l, Zminus_mod_idemp_r, Z.mul_1_l, Z.sub_diag, Zmod_0_l; lia.
    }
    assert (Hw0 : w = (modInv (-divstep.g (fst (divstep.stepN n1 st))) (2 ^ n2)
       * (-divstep.f (fst (divstep.stepN n1 st)))) mod 2 ^ n2).
    1:{
      assert (Hn2 : (2^n2 | 2^((64 - Z.of_nat n1)))) by 
        (exists (2^((64 - Z.of_nat n1) - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring).
      apply Zmult_eqm;[|eapply eqm_2_pow_le;[|apply Zopp_eqm;apply Hf1];lia].
      unfold eqm; f_equal.
      apply modInv_eqm.
      apply Zopp_eqm.
      eapply eqm_2_pow_le;[|apply Hg1].
      lia.
    }
    apply Z.mul_cancel_l in Hf2;[|lia].
    repeat split.
    * rewrite Hf2.
      apply (eqm_2_pow_le _ (64 - Z.of_nat n1));[lia|assumption].
    * rewrite Z2Nat.id in Hg2 by lia.
      unfold eqm.
      rewrite <- Zaux.Zdiv_mod_mult by lia.
      symmetry.
      apply Z.div_unique_exact;[lia|].
      rewrite <- Zmult_mod_distr_l, <- Z.pow_add_r, Hg2 by lia.
      replace (n2 + (64 - (n2 + Z.of_nat n1))) with (64 - (Z.of_nat n1)) by ring.
      apply Zplus_eqm;[apply Zopp_eqm; assumption|].
      rewrite (Z.mul_comm _ (divstep.g (fst (divstep.stepN n1 st)))).
      apply Zmult_eqm; try assumption.
      unfold eqm; f_equal.
      assumption.
    * repeat f_equal.
      rewrite Z.mul_comm, <-Z_div_exact_full_2 by (try lia; apply Zdivide_mod; assumption).
      ring.
    * repeat f_equal.
      apply Z.sub_move_r.
      rewrite  <- Hw0 by lia.
      cbn; ring.
    * repeat f_equal.
      apply Z.sub_move_r.
      rewrite  <- Hw0 by lia.
      cbn; ring.
    * repeat f_equal.
      rewrite Z.land_ones by lia.
      assert (Hn264 : 2^n2 < 2^64) by (apply Z.pow_lt_mono_r; lia).
      change Int64.modulus with (2^64).
      assert (Hmod := Z.mod_pos_bound (g1 * -f * (g1 * g1 - 2)) (2^n2)).
      rewrite Z.mod_small by lia.
      unfold w.
      replace (g1 * -f * (g1 * g1 - 2)) with (g1 * (g1 * g1 - 2) * -f) by ring.
      do 2 (rewrite <- Zmult_mod_idemp_l; symmetry).
      do 2 f_equal.
      symmetry.
      rewrite <- Z.land_ones by lia.
      replace n2 with (Z.min 6 n2) at 1 by lia.
      rewrite <- Z_land_ones_min, Z.land_assoc by lia.
      rewrite HackersDelightB by (apply Zodd_equiv; assumption).
      rewrite Z.land_ones by lia.
      rewrite <- (Z.mul_1_l (modInv _ _)), <- Zmult_mod_idemp_l.
      rewrite <- (Hgcd g1 n2) at 1 by assumption || lia.
      rewrite <- Z.gcd_opp_l, <- Zmult_mod_idemp_r, <- modInv_mul_l, Zmult_mod_idemp_r, Zmult_mod_idemp_l, <- Z.mul_assoc.
      rewrite <- Z.land_ones by lia.
      replace n2 with (Z.min 6 n2) at 2 by lia.
      rewrite <- Z_land_ones_min, Z.land_assoc by lia.
      rewrite !Z.land_ones by lia.
      rewrite <- Zmult_mod_idemp_r, modInv_mul_r, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_r, Z.mul_1_r by assumption || lia.
      rewrite <- Zmod_div_mod; try lia.
      exists (2^(6 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
    * repeat f_equal.
      rewrite divstep.etaDs by assumption || lia.
      lia.
  }
  1:{
    forward_if (temp _t'5 (Vint (Int.repr (Z.min (62 - Z.of_nat n1) ((divstep.eta (fst (divstep.stepN n1 st))) + 1)))));
    try (progressC; revert H1; rewrite <- add_repr);
    try rewrite Int_repr_Int64_Z_mod_modulus;
    try entailer;
    try rewrite add_repr;
    convert_C_to_math;
    try lia;
    try (intros H1;first [rewrite Z.min_l by lia|rewrite Z.min_r by lia];reflexivity).
    progressC.
    forward_verify_check.
    1:{
      forward_if (temp _t'6 (Vint Int.one)); try lia.
      1:{
        progressC.
        destruct (zlt _ _); try lia.
        reflexivity.
      }
      forward_if; try discriminate.
      forward; entailer!.
    }
    replace ((Z.of_nat j + Z.of_nat (Z.to_nat k)
               + (64 - (Z.of_nat j + Z.of_nat (Z.to_nat k))))) with 64 by ring.
    progressC.
    change 15 with (Z.ones 4).
    rewrite <- Z.land_ones, Z.land_m1_l, Z_shiftr_ones, subsub1, Z_land_ones_min by lia.
    set (n2 := (Z.min _ 4)).
    pose (w := (modInv (-f) (2^n2) * g1) mod (2^n2)).
    do 2 progressC.
    Exists (Z.to_nat n2) (divstep.Trans.u (divstep.Trans.transN n1 st)) (divstep.Trans.v (divstep.Trans.transN n1 st)) f
           ((g1 + f * w) / 2^n2)
           (Int.repr w).
    entailer!.
    rewrite Nat.add_comm.
    rewrite <- divstep.Trans.transN_stepN.
    rewrite divstep.Trans.transSs;
    try solve [unfold divstep.eta in H0; unfold n2, divstep.eta; lia].
    split;[cbn; ring|].
    split;[cbn; ring|].
    rewrite Nat2Z.inj_add, Z2Nat.id, divstep.stepN_app_fst by lia.
    injection (divstep.Trans.transN_step (Z.to_nat n2) (fst (divstep.stepN n1 st))); intros Hg2 Hf2.
    rewrite divstep.Trans.transSs in Hf2, Hg2;
    try solve [unfold divstep.eta in H0; unfold n2, divstep.eta; lia].
    cbn in Hf2, Hg2.
    ring_simplify in Hf2; ring_simplify in Hg2.
    assert (Hw : 0 <= w < 2^4).
    1:{
      assert (0 < 2^n2 <= 2^4) by (split;[|apply Z.pow_le_mono_r];lia).
      pose (Z.mod_pos_bound (modInv (-f) (2 ^ n2) * g1) (2 ^ n2)).
      lia.
    }
    convert_C_to_math.
    assert (Hg1fw : (2^n2 | g1 + f * w)).
    1: {
      apply Zmod_divide;[lia|].
      unfold w.
      rewrite <- Zplus_mod_idemp_r, Zmult_mod_idemp_r, Zplus_mod_idemp_r, Z.mul_assoc,
              <- Z.sub_opp_r, !Zopp_mult_distr_l, <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l,
              modInv_mul_r, Z.gcd_opp_l.
      rewrite Hgcd by assumption || lia.
      rewrite Zmult_mod_idemp_l, Zminus_mod_idemp_r, Z.mul_1_l, Z.sub_diag, Zmod_0_l; lia.
    }
    assert (Hw0 : w = (modInv (-divstep.f (fst (divstep.stepN n1 st))) (2 ^ n2)
       * divstep.g (fst (divstep.stepN n1 st))) mod 2 ^ n2).
    1:{
      assert (Hn2 : (2^n2 | 2^((64 - Z.of_nat n1)))) by 
        (exists (2^((64 - Z.of_nat n1) - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring).
      apply Zmult_eqm;[|eapply eqm_2_pow_le;[|apply Hg1];lia].
      unfold eqm; f_equal.
      apply modInv_eqm.
      apply Zopp_eqm.
      eapply eqm_2_pow_le;[|apply Hf1].
      lia.
    }
    apply Z.mul_cancel_l in Hf2;[|lia].
    repeat split.
    * rewrite Hf2.
      apply (eqm_2_pow_le _ (64 - Z.of_nat n1));[lia|assumption].
    * rewrite Z2Nat.id in Hg2 by lia.
      unfold eqm.
      rewrite <- Zaux.Zdiv_mod_mult by lia.
      symmetry.
      apply Z.div_unique_exact;[lia|].
      rewrite <- Zmult_mod_distr_l, <- Z.pow_add_r, Hg2 by lia.
      replace (n2 + (64 - (n2 + Z.of_nat n1))) with (64 - (Z.of_nat n1)) by ring.
      rewrite (Z.add_comm _ (divstep.g (fst (divstep.stepN n1 st)))).
      apply Zplus_eqm; try assumption.
      rewrite (Z.mul_comm _ (divstep.f (fst (divstep.stepN n1 st)))).
      apply Zmult_eqm; try assumption.
      unfold eqm; f_equal.
      assumption.
    * repeat f_equal.
      rewrite Z.mul_comm, <-Z_div_exact_full_2 by (try lia; apply Zdivide_mod; assumption).
      ring.
    * repeat f_equal.
      apply Z.sub_move_r.
      rewrite  <- Hw0 by lia.
      cbn; ring.
    * repeat f_equal.
      apply Z.sub_move_r.
      rewrite  <- Hw0 by lia.
      cbn; ring.
    * repeat f_equal.
      rewrite Z.land_ones by lia.
      assert (Hn264 : 2^n2 < 2^64) by (apply Z.pow_lt_mono_r; lia).
      change Int64.modulus with (2^64).
      assert (Hmod := Z.mod_pos_bound (-((f + Z.land (f + 1) 4 * 2 ^ 1) mod 2 ^ 64) mod 2 ^ 32 * g1) (2^n2)).
      rewrite Z.mod_small by lia.
      unfold w.
      do 2 (rewrite <- Zmult_mod_idemp_l; symmetry).
      do 2 f_equal.
      rewrite <- Zmod_div_mod; try lia.
      2:exists (2^(32 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
      rewrite <- (Z.mul_1_l (_ mod (2^64))), <- Z.mul_opp_l, <- Zmult_mod_idemp_r.
      rewrite <- Zmod_div_mod, Zmult_mod_idemp_r; try lia.
      2:exists (2^(64 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
      rewrite (Zmod_div_mod (2^n2) (2^4)); try lia.
      2:exists (2^(4 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
      rewrite <- (Z.mul_1_r (modInv (-f) (2 ^ n2))).
      rewrite <- (Hgcd f 4) at 1 by assumption || lia.
      rewrite <- Z.gcd_opp_l, <- Zmult_mod_idemp_r, <- modInv_mul_r, Zmult_mod_idemp_r, Z.mul_assoc.
      rewrite <- Zmod_div_mod; try lia.
      2:exists (2^(4 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
      rewrite <- Zmult_mod_idemp_l, modInv_mul_l, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_l, Z.mul_1_l by assumption || lia.
      rewrite <- HackersDelightA, Z.land_ones by (try lia; apply Zodd_equiv; assumption).
      rewrite <- Zmod_div_mod; try lia.
      2:exists (2^(4 - n2)); rewrite <-Z.pow_add_r; try lia; f_equal; ring.
      rewrite Z.mul_opp_l, Z.mul_1_l.
      do 3 f_equal.
      rewrite Z.shiftl_mul_pow2; lia.
    * repeat f_equal.
      rewrite divstep.etaSs; lia.
  }
  Intros n2 u v f2 g2 w.
  rename H0 into Hn2; rename H1 into Hn232;
  rename H2 into Hu; rename H3 into Hv;
  rename H4 into Hf2; rename H5 into Hg2.
  do 3 progressC. 
  ring_simplify (g2 * 2 ^ Z.of_nat n2
                   - f2 * Int.unsigned w
                   + f2 * Int.unsigned w).
  ring_simplify ((divstep.Trans.q (divstep.Trans.transN (n1 + n2) st)
            - u * Int.unsigned w
            + u * Int.unsigned w)).
  ring_simplify ((divstep.Trans.r (divstep.Trans.transN (n1 + n2) st)
            - v * Int.unsigned w
            + v * Int.unsigned w)).
  forward_verify_check.
  match goal with
  | |- semax _ ?E _ _ => forward_if E
  end.
  2:(forward;entailer!).
  1:{
    elimtype False.
    revert H0.
    convert_C_to_math.
    rewrite Z.land_ones, Z_mod_mult, Z.eqb_refl by lia.
    discriminate.
  }
  forward.
  Exists (n1 + n2)%nat n2 u v f2 g2.
  rewrite Nat2Z.inj_add in * |- *.
  replace (62 - (Z.of_nat n1 + Z.of_nat n2) + Z.of_nat n2) 
   with (62 - Z.of_nat n1) by ring.
  entailer!.
* do 4 progressC.
  forward_verify_check.
  1:{
    forward_call (divstep.Trans.transN 62 st, t, sh, 62, false);
    [apply (divstep.Trans.bounded_transN 62)|].
    rewrite divstep.Trans.det_transN, Z.eqb_refl.
    simpl (Z.b2z true).
    forward_if;[discriminate|forward;entailer!].
  }
  forward.
Qed.

Lemma body_modinv64_update_de_62: semax_body Vprog Gprog f_secp256k1_modinv64_update_de_62 secp256k1_modinv64_update_de_62_spec.
Proof.
start_function.
assert (Hoddm : forall n, 0 <= n -> Z.gcd m (2^n) = 1).
1:{
  intros n Hn.
  apply Zgcd_1_rel_prime.
  apply Zpow_facts.rel_prime_Zpower_r;[assumption|].
  apply rel_prime_sym.
  apply prime_rel_prime;[apply prime_2|].
  intros [m0 Hm0].
  revert H; apply Z.Even_Odd_False.
  rewrite Hm0, Z.mul_comm.
  apply Zeven_equiv.
  apply Zeven_2p.
}
unfold Trans_repr, Signed62.reprn.
fastforward 16.
change (Int64.shru (Int64.repr (-1)) (Int64.repr 2)) with (Int64.repr (Z.ones 62)).
unfold Znth; simpl (Vlong _).
unfold make_modinfo.
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (d, 5%nat, m, -2, ptrd, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, shd, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Gt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (d, 5%nat, m, 1, ptrd, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, shd, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Lt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (e, 5%nat, m, -2, ptre, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, she, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Gt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (e, 5%nat, m, 1, ptre, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, she, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Lt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
destruct H3 as [[Huv _] [Hqr _]].
forward_verify_check.
1:{

  do 2 forward_call.
  forward_if;[convert_C_to_math;entailer!!| |forward;entailer!!].
  revert H3.
  convert_C_to_math.
  replace (_ <? _) with false by lia.
  discriminate.
}
forward_verify_check.
1:{
  do 2 forward_call.
  forward_if;[convert_C_to_math;entailer!!| |forward;entailer!!].
  revert H3.
  convert_C_to_math.
  replace (_ <? _) with false by lia.
  discriminate.
}
do 2 progressC.
simpl (map Vlong _).
rewrite !Z.shiftr_shiftr by lia; simpl (62 + _); simpl (_ + 62).
assert (H311 : forall x, -2 * m < x < m -> Z.shiftr x 311 = if x <? 0 then -1 else 0).
1:{
 intros x Hx.
 destruct (Z.ltb_spec0 x 0) as [Hx0|Hx0].
 * cut (-1 <= Z.shiftr x 311 < 0);[|apply shiftr_bounds];lia.
 * cut (0 <= Z.shiftr x 311 < 1);[|apply shiftr_bounds];lia.
}
rewrite !H311 by lia; clear H311.
assert (Hland : forall x (b:bool), Z.land x (if b then -1 else 0) = if b then x else 0).
1:{
 intros x b.
 rewrite !(f_if (Z.land _)), !Z.land_0_r, !Z.land_m1_r.
 reflexivity.
}
progressC;rewrite !Hland by lia.
1:{
 rewrite !(f_if (Int64.repr)), !(f_if (Int64.signed)).
 convert_C_to_math.
 destruct (_ <? _);destruct (_ <? _);lia.
}
progressC;rewrite !Hland by lia.
1:{
 rewrite !(f_if (Int64.repr)), !(f_if (Int64.signed)).
 convert_C_to_math.
 destruct (_ <? _);destruct (_ <? _);lia.
}
set (me0 := _ + _).
set (md0 := _ + _).
assert (Habsmd0 : Z.abs md0 <= 2^62) by (unfold md0; repeat destruct (_ <? 0); lia).
assert (Habsme0 : Z.abs me0 <= 2^62) by (unfold me0; repeat destruct (_ <? 0); lia).
assert (Habsmod62 : forall x, Z.abs (x mod 2 ^ 62) < 2 ^ 62).
1:{
 intros x.
 assert (Hbound : 0 <= x mod 2 ^ 62 < 2^62) by (apply Z.mod_pos_bound;lia).
 rewrite Z.abs_eq; lia.
}
assert (Habsmod62m := Habsmod62 m).
assert (Habsmod62d := Habsmod62 d).
assert (Habsmod62e := Habsmod62 e).
assert (Hudve : Z.abs (divstep.Trans.u mtx * (d mod 2 ^ 62) + divstep.Trans.v mtx * (e mod 2 ^ 62)) <= (2^62*(2^62 - 1))).
1:{
 etransitivity;[apply Z.abs_triangle|].
 rewrite !Z.abs_mul.
 transitivity (Z.abs (divstep.Trans.u mtx) * (2 ^ 62 - 1)+ Z.abs (divstep.Trans.v mtx) * (2 ^ 62 - 1));[|lia].
 apply Z.add_le_mono; apply Z.mul_le_mono_nonneg_l; lia.
}
assert (Hqrve : Z.abs (divstep.Trans.q mtx * (d mod 2 ^ 62) + divstep.Trans.r mtx * (e mod 2 ^ 62)) <= (2^62*(2^62 - 1))).
1:{
 etransitivity;[apply Z.abs_triangle|].
 rewrite !Z.abs_mul.
 transitivity (Z.abs (divstep.Trans.q mtx) * (2 ^ 62 - 1)+ Z.abs (divstep.Trans.r mtx) * (2 ^ 62 - 1));[|lia].
 apply Z.add_le_mono; apply Z.mul_le_mono_nonneg_l; lia.
}
rewrite ?Z.abs_lt, ?Z.abs_le in *. (* This speeds up lia exponentially. *)
forward_call (v_cd, Tsh, divstep.Trans.u mtx, d mod 2 ^ 62).
forward_call;[
 change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds
|].
forward_call (v_ce, Tsh, divstep.Trans.q mtx, d mod 2 ^ 62).
forward_call;[
 change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds
|].
set (cd0 := divstep.Trans.u mtx * (d mod 2 ^ 62) + divstep.Trans.v mtx * (e mod 2 ^ 62)).
set (ce0 := divstep.Trans.q mtx * (d mod 2 ^ 62) + divstep.Trans.r mtx * (e mod 2 ^ 62)).
assert (Hcd0 : -2^124 <= cd0 <= 2^124) by solve_bounds.
assert (Hce0 : -2^124 <= ce0 <= 2^124) by solve_bounds.
forward_call;forward;progressC.
forward_call;forward;progressC.
rewrite !Z.land_ones by lia.
assert (Habsmodinvd := Habsmod62 (modInv m (2 ^ 62) * cd0 + md0)).
assert (Habsmodinve := Habsmod62 (modInv m (2 ^ 62) * ce0 + me0)).
rewrite ?Z.abs_lt, ?Z.abs_le in *. (* This speeds up lia exponentially. *)
assert (Habsmd0modinv : Z.abs (m mod 2 ^ 62 * (md0 - (modInv m (2 ^ 62) * cd0 + md0) mod 2 ^ 62)) <= 2^125).
1:{
  rewrite Z.abs_mul.
  change (2^125) with (2^62 * 2^63).
  apply Zmult_le_compat; lia.
}
assert (Habsme0modinv : Z.abs (m mod 2 ^ 62 * (me0 - (modInv m (2 ^ 62) * ce0 + me0) mod 2 ^ 62)) <= 2^125).
1:{
  rewrite Z.abs_mul.
  change (2^125) with (2^62 * 2^63).
  apply Zmult_le_compat; lia.
}
rewrite ?Z.abs_lt, ?Z.abs_le in *. (* This speeds up lia exponentially. *)
simpl (Signed62.reprn 5 m).
assert (Hcd0'b : -2^126 <=
  cd0 + m mod 2 ^ 62 * (md0 - (modInv m (2 ^ 62) * cd0 + md0) mod 2 ^ 62) <=
  2^126) by solve_bounds.
assert (Hce0'b : -2^126 <=
  ce0 + m mod 2 ^ 62 * (me0 - (modInv m (2 ^ 62) * ce0 + me0) mod 2 ^ 62) <=
  2^126) by solve_bounds.
do 2 (forward;forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
drop_LOCALs [_t'44; _t'45; _t'46; _t'47; _t'10; _t'9].
assert (Hmod262 : forall c0 m0, (c0 + m mod 2^62 * (m0 - (modInv m (2^62) * c0 + m0) mod 2^62)) mod 2^62 = 0).
1:{
  intros c0 m0.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Zminus_mod_idemp_r, Zmult_mod_idemp_l.
  replace (m0 - (modInv m (2 ^ 62) * c0 + m0)) with (-(modInv m (2 ^ 62) * c0)) by ring.
  rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_r, Z.mul_opp_r, Z.mul_assoc, Z.add_opp_r.
  rewrite <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l, modInv_mul_r, Hoddm, Z.mul_1_l, Zminus_mod_idemp_r, Z.sub_diag by lia.
  reflexivity.
}
forward_verify_check.
1:{
  forward_call.
  forward_if;[|forward;entailer!!].
  revert H3; fold cd0 md0; convert_C_to_math.
  rewrite <-(Z.land_ones _ 64), <- Z.land_assoc by lia.
  change (Z.land (Z.ones 62) (Z.ones 64)) with (Z.ones 62).
  rewrite Z.land_ones, Hmod262, Z.eqb_refl by lia.
  discriminate.
}
forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|].
forward_verify_check.
1:{
  forward_call.
  forward_if;[|forward;entailer!!].
  revert H3; fold cd0 md0; convert_C_to_math.
  rewrite <-(Z.land_ones _ 64), <- Z.land_assoc by lia.
  change (Z.land (Z.ones 62) (Z.ones 64)) with (Z.ones 62).
  rewrite Z.land_ones, Hmod262, Z.eqb_refl by lia.
  discriminate.
}
forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|].
set (md := md0 - (modInv m (2 ^ 62) * cd0 + md0) mod 2 ^ 62) in *.
set (me := me0 - (modInv m (2 ^ 62) * ce0 + me0) mod 2 ^ 62) in *.
assert (Hmd : -2 ^ 63 <= md <= 2^63) by (clear -Habsmodinvd Habsmd0;nia).
assert (Hme : -2 ^ 63 <= me <= 2^63) by (clear -Habsmodinve Habsme0;nia).
set (cd0' := cd0 + m mod 2 ^ 62 * md) in *.
set (ce0' := ce0 + m mod 2 ^ 62 * me) in *.
clear Hmod262.
assert (HboundA : forall x y z, -2^127 <= x < 2^127 -> -2^62 <= y <= 2^62 -> 
  -2 ^ 126 <= Z.shiftr x 62 + y * (z mod 2 ^ 62) <= 2 ^ 126 - 1).
1:{
  intros x y z Hx Hy.
  clear -Hx Hy.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hx.
  assert (0 <= z mod 2^62 < 2^62) by (apply Z.mod_pos_bound; lia).
  nia.
}
assert (HboundB : forall x y0 z0 y1 z1, -2^127 <= x < 2^127 -> -2^62 <= y0 <= 2^62 -> -2^62 <= y1 <= 2^62 -> 
  -2 ^ 126 <= Z.shiftr x 62 + y0 * (z0 mod 2 ^ 62) + y1 * (z1 mod 2 ^ 62) <= 2 ^ 126 - 1).
1:{
  intros x y0 z0 y1 z1 Hx Hy0 Hy1.
  clear -Hx Hy0 Hy1.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hx.
  assert (0 <= z0 mod 2^62 < 2^62) by (apply Z.mod_pos_bound; lia).
  assert (0 <= z1 mod 2^62 < 2^62) by (apply Z.mod_pos_bound; lia).
  nia.
}
assert (Hcd1' : -2 ^ 126 <= Z.shiftr cd0' 62 + divstep.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hcd1'' : -2 ^ 126 <= Z.shiftr cd0' 62 + divstep.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62) + divstep.Trans.v mtx * (Z.shiftr e 62 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
assert (Hce1' : -2 ^ 126 <= Z.shiftr ce0' 62 + divstep.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hce1'' : -2 ^ 126 <= Z.shiftr ce0' 62 + divstep.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62) + divstep.Trans.r mtx * (Z.shiftr e 62 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
do 4 (forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
forward;unfold Znth;simpl (temp _ _).
set (dval := [Vlong _;Vlong _;Vlong _;Vlong _;Vlong _]).
set (eval := [Vlong _;Vlong _;Vlong _;Vlong _;Vlong _]).
set (tval := (Vlong _, (Vlong _, (Vlong _, Vlong _)))).
set (mval := [Vlong _;Vlong _;Vlong _;Vlong _;Vlong _]).
set (minvval := Vlong (Int64.repr (modInv m (2 ^ 62)))).
set (m1 := Z.shiftr m 62 mod 2 ^ 62) in *.
assert (Hm1 : 0 <= m1 < 2^62) by (apply Z.mod_pos_bound;lia).
assert (Hm1md : -2 ^ 125 <= m1 * md <= 2^125) by (clear -Hm1 Hmd;nia).
assert (Hm1me : -2 ^ 125 <= m1 * me <= 2^125) by (clear -Hm1 Hme;nia).
pose (cd1 := Z.shiftr cd0' 62 + divstep.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62)
        + divstep.Trans.v mtx * (Z.shiftr e 62 mod 2 ^ 62)
        + m1 * md).
pose (ce1 := Z.shiftr ce0' 62 + divstep.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62)
          + divstep.Trans.r mtx * (Z.shiftr e 62 mod 2 ^ 62)
          + m1 * me).
assert (Hcd1 : -2 ^ 127 <= cd1 <= 2 ^ 127 - 1) by lia.
assert (Hce1 : -2 ^ 127 <= ce1 <= 2 ^ 127 - 1) by lia.
match goal with
  | |- semax _ (PROPx nil (LOCALx ?L _)) _ _ =>
forward_if (PROPx nil (LOCALx L (SEPx [
   secp256k1_uint128_at Tsh ce1 v_ce;
   secp256k1_uint128_at Tsh cd1 v_cd;
   data_at shd t_secp256k1_modinv64_signed62 dval ptrd;
   data_at she t_secp256k1_modinv64_signed62 eval ptre;
   data_at sht t_secp256k1_modinv64_trans2x2 tval ptrt;
   data_at shm t_secp256k1_modinv64_modinfo (mval, minvval) ptrm])))
end.
2:{
  forward.
  unfold cd1, ce1; replace m1 with 0;
  [rewrite !Z.mul_0_l, !Z.add_0_r;apply ENTAIL_refl|].
  symmetry.
  revert H3.
  apply repr_inj_unsigned64;rep_lia.
}
1:{
  do 2(
    forward;change (Znth 1 mval) with (Vlong (Int64.repr m1));
    forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]
  ).
  fold cd1 ce1.
  clear -m;entailer!!.
}
do 2 (forward_call;progressC;forward_call).
rewrite !Z.land_ones by lia.
assert (Hcd2' : -2 ^ 126 <= Z.shiftr cd1 62 + divstep.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hcd2'' : -2 ^ 126 <= Z.shiftr cd1 62 + divstep.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62) + divstep.Trans.v mtx * (Z.shiftr e 124 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
assert (Hce2' : -2 ^ 126 <= Z.shiftr ce1 62 + divstep.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hce2'' : -2 ^ 126 <= Z.shiftr ce1 62 + divstep.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62) + divstep.Trans.r mtx * (Z.shiftr e 124 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
do 4 (forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
forward;unfold Znth;simpl (temp _ _).
set (dval1 := (upd_Znth 0 dval (Vlong (Int64.repr (cd1 mod 2 ^ 62))))).
set (eval1 := (upd_Znth 0 eval (Vlong (Int64.repr (ce1 mod 2 ^ 62))))).
set (m2 := Z.shiftr m 124 mod 2 ^ 62) in *.
assert (Hm2 : 0 <= m2 < 2^62) by (apply Z.mod_pos_bound;lia).
assert (Hm2md : -2 ^ 125 <= m2 * md <= 2^125) by (clear -Hm2 Hmd;nia).
assert (Hm2me : -2 ^ 125 <= m2 * me <= 2^125) by (clear -Hm2 Hme;nia).
pose (cd2 := Z.shiftr cd1 62 + divstep.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62)
        + divstep.Trans.v mtx * (Z.shiftr e 124 mod 2 ^ 62)
        + m2 * md).
pose (ce2 := Z.shiftr ce1 62 + divstep.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62)
          + divstep.Trans.r mtx * (Z.shiftr e 124 mod 2 ^ 62)
          + m2 * me).
assert (Hcd2 : -2 ^ 127 <= cd2 <= 2 ^ 127 - 1) by lia.
assert (Hce2 : -2 ^ 127 <= ce2 <= 2 ^ 127 - 1) by lia.
match goal with
  | |- semax _ (PROPx nil (LOCALx ?L _)) _ _ =>
forward_if (PROPx nil (LOCALx L (SEPx [
   secp256k1_uint128_at Tsh ce2 v_ce;
   secp256k1_uint128_at Tsh cd2 v_cd;
   data_at shd t_secp256k1_modinv64_signed62 dval1 ptrd;
   data_at she t_secp256k1_modinv64_signed62 eval1 ptre;
   data_at sht t_secp256k1_modinv64_trans2x2 tval ptrt;
   data_at shm t_secp256k1_modinv64_modinfo (mval, minvval) ptrm])))
end.
2:{
  forward.
  unfold cd2, ce2; replace m2 with 0;
  [rewrite !Z.mul_0_l, !Z.add_0_r;apply ENTAIL_refl|].
  symmetry.
  revert H3.
  apply repr_inj_unsigned64;rep_lia.
}
1:{
  do 2(
    forward;change (Znth 2 mval) with (Vlong (Int64.repr m2));
    forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]
  ).
  fold cd2 ce2.
  clear -m;entailer!!.
}
do 2 (forward_call;progressC;forward_call).
rewrite !Z.land_ones by lia.
assert (Hcd3' : -2 ^ 126 <= Z.shiftr cd2 62 + divstep.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hcd3'' : -2 ^ 126 <= Z.shiftr cd2 62 + divstep.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62) + divstep.Trans.v mtx * (Z.shiftr e 186 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
assert (Hce3' : -2 ^ 126 <= Z.shiftr ce2 62 + divstep.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundA;lia).
assert (Hce3'' : -2 ^ 126 <= Z.shiftr ce2 62 + divstep.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62) + divstep.Trans.r mtx * (Z.shiftr e 186 mod 2 ^ 62) <= 2 ^ 126 - 1) 
 by (apply HboundB;lia).
do 4 (forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
forward;unfold Znth;simpl (temp _ _).
set (dval2 := (upd_Znth 1 dval1 (Vlong (Int64.repr (cd2 mod 2 ^ 62))))).
set (eval2 := (upd_Znth 1 eval1 (Vlong (Int64.repr (ce2 mod 2 ^ 62))))).
set (m3 := Z.shiftr m 186 mod 2 ^ 62) in *.
assert (Hm3 : 0 <= m3 < 2^62) by (apply Z.mod_pos_bound;lia).
assert (Hm3md : -2 ^ 125 <= m3 * md <= 2^125) by (clear -Hm3 Hmd;nia).
assert (Hm3me : -2 ^ 125 <= m3 * me <= 2^125) by (clear -Hm3 Hme;nia).
pose (cd3 := Z.shiftr cd2 62 + divstep.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62)
        + divstep.Trans.v mtx * (Z.shiftr e 186 mod 2 ^ 62)
        + m3 * md).
pose (ce3 := Z.shiftr ce2 62 + divstep.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62)
          + divstep.Trans.r mtx * (Z.shiftr e 186 mod 2 ^ 62)
          + m3 * me).
assert (Hcd3 : -2 ^ 127 <= cd3 <= 2 ^ 127 - 1) by lia.
assert (Hce3 : -2 ^ 127 <= ce3 <= 2 ^ 127 - 1) by lia.
match goal with
  | |- semax _ (PROPx nil (LOCALx ?L _)) _ _ =>
forward_if (PROPx nil (LOCALx L (SEPx [
   secp256k1_uint128_at Tsh ce3 v_ce;
   secp256k1_uint128_at Tsh cd3 v_cd;
   data_at shd t_secp256k1_modinv64_signed62 dval2 ptrd;
   data_at she t_secp256k1_modinv64_signed62 eval2 ptre;
   data_at sht t_secp256k1_modinv64_trans2x2 tval ptrt;
   data_at shm t_secp256k1_modinv64_modinfo (mval, minvval) ptrm])))
end.
2:{
  forward.
  unfold cd3, ce3; replace m3 with 0;
  [rewrite !Z.mul_0_l, !Z.add_0_r;apply ENTAIL_refl|].
  symmetry.
  revert H3.
  apply repr_inj_unsigned64;rep_lia.
}
1:{
  do 2(
    forward;change (Znth 3 mval) with (Vlong (Int64.repr m3));
    forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]
  ).
  fold cd3 ce3.
  clear -m;entailer!!.
}
do 2 (forward_call;progressC;forward_call).
rewrite !Z.land_ones by lia.
assert (Hd248 : -2^61 <= Z.shiftr d 248 <= 2^61 - 1) by solve_bounds.
assert (He248 : -2^61 <= Z.shiftr e 248 <= 2^61 - 1) by solve_bounds.
assert (Hcd4' : -2 ^ 124 <= Z.shiftr cd3 62 + divstep.Trans.u mtx * Z.shiftr d 248 <= 2 ^ 124 - 1).
1:{
  rewrite <- strict_bounds in Hcd3.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hcd3.
  clear -Hd248 Hcd3 Huv; nia.
}
assert (Hcd4'' : -2 ^ 124 <= Z.shiftr cd3 62 + divstep.Trans.u mtx * Z.shiftr d 248 + divstep.Trans.v mtx * Z.shiftr e 248 <= 2 ^ 124 - 1).
1:{
  rewrite <- strict_bounds in Hcd3.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hcd3.
  clear -Hd248 He248 Hcd3 Huv; nia.
}
assert (Hce4' : -2 ^ 124 <= Z.shiftr ce3 62 + divstep.Trans.q mtx * Z.shiftr d 248 <= 2 ^ 124 - 1) .
1:{
  rewrite <- strict_bounds in Hce3.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hce3.
  clear -Hd248 Hce3 Hqr; nia.
}
assert (Hce4'' : -2 ^ 124 <= Z.shiftr ce3 62 + divstep.Trans.q mtx * Z.shiftr d 248 + divstep.Trans.r mtx * Z.shiftr e 248 <= 2 ^ 124 - 1) .
1:{
  rewrite <- strict_bounds in Hce3.
  apply (shiftr_bounds (-2^65) _ (2^65) 62) in Hce3.
  clear -Hd248 He248 Hce3 Hqr; nia.
}
do 4 (forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
set (dval3 := (upd_Znth 2 dval2 (Vlong (Int64.repr (cd3 mod 2 ^ 62))))).
set (eval3 := (upd_Znth 2 eval2 (Vlong (Int64.repr (ce3 mod 2 ^ 62))))).
set (m4 := Z.shiftr m 248) in *.
assert (Hm4 : 0 <= m4 <= 2^61) by (unfold m4;solve_bounds).
assert (Hm4md : -2 ^ 124 <= m4 * md <= 2^124) by (clear -Hm4 Hmd;nia).
assert (Hm4me : -2 ^ 124 <= m4 * me <= 2^124) by (clear -Hm4 Hme;nia).
pose (cd4 := Z.shiftr cd3 62 + divstep.Trans.u mtx * Z.shiftr d 248
        + divstep.Trans.v mtx * Z.shiftr e 248
        + m4 * md).
pose (ce4 := Z.shiftr ce3 62 + divstep.Trans.q mtx * Z.shiftr d 248
          + divstep.Trans.r mtx * Z.shiftr e 248
          + m4 * me).
assert (Hcd4 : -2 ^ 125 <= cd4 <= 2 ^ 125 - 1) by lia.
assert (Hce4 : -2 ^ 125 <= ce4 <= 2 ^ 125 - 1) by lia.
do 2(
  forward;change (Znth 4 mval) with (Vlong (Int64.repr m4));
  forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]
).
fold cd4 ce4.
do 2 (forward_call;progressC;forward_call;[change Int128_min_signed with (-2^127);change Int128_max_signed with (2^127-1);solve_bounds|]).
rewrite !Z.land_ones by lia.
do 2 (forward_call;[solve_bounds|forward]).
set (dval4 := (upd_Znth 4 _ _)).
set (eval4 := (upd_Znth 4 _ _)).
assert (Hcarry : forall n a x y z, 0 <= n ->
 a = Z.shiftr (x * (d mod 2^(n+62))
                     + y * (e mod 2^(n+62))
                     + (m mod 2^(n+62)) * z) n ->
 Z.shiftr a 62 + x * (Z.shiftr d (n+62) mod 2 ^ 62)
       + y * (Z.shiftr e (n+62) mod 2 ^ 62)
       + (Z.shiftr m (n+62) mod 2 ^ 62) * z 
   = Z.shiftr (x * (d mod 2^(n+124))
                     + y * (e mod 2^(n+124))
                     + (m mod 2^(n+124)) * z) (n+62)).
1:{
  intros n a x y z Hn ->.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite Z.div_div by lia.
  rewrite <-!Z.add_assoc, Z.add_comm, !Z.add_assoc, <- Z.div_add_l, <-!Z.pow_add_r by lia.
  replace ((x * ((d / 2 ^ (n + 62)) mod 2 ^ 62)
  + y * ((e / 2 ^ (n + 62)) mod 2 ^ 62)
  + (m / 2 ^ (n + 62)) mod 2 ^ 62 * z)
 * 2 ^ (n + 62)
 + (x * (d mod 2 ^ (n + 62)) + y * (e mod 2 ^ (n + 62))
      + m mod 2 ^ (n + 62) * z))
  with (x * (d mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((d / 2 ^ (n + 62)) mod 2 ^ 62))
 + y * (e mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((e / 2 ^ (n + 62)) mod 2 ^ 62))
      + (m mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((m / 2 ^ (n + 62)) mod 2 ^ 62)) * z)
  by ring.
  rewrite <-!Z.rem_mul_r, <-!Z.pow_add_r, <-!Z.add_assoc by lia.
  reflexivity.
}
assert (Hcd124 : cd1 = Z.shiftr (divstep.Trans.u mtx * (d mod 2^124)
                     + divstep.Trans.v mtx * (e mod 2^124)
                     + (m mod 2^124) * md) 62)
by (apply (Hcarry 0);[lia|reflexivity]).
assert (Hce124 : ce1 = Z.shiftr (divstep.Trans.q mtx * (d mod 2^124)
                     + divstep.Trans.r mtx * (e mod 2^124)
                     + (m mod 2^124) * me) 62)
by (apply (Hcarry 0);[lia|reflexivity]).
assert (Hcd186 : cd2 = Z.shiftr (divstep.Trans.u mtx * (d mod 2^186)
                     + divstep.Trans.v mtx * (e mod 2^186)
                     + (m mod 2^186) * md) 124) by
(apply (Hcarry 62);[lia|assumption]).
assert (Hce186 : ce2 = Z.shiftr (divstep.Trans.q mtx * (d mod 2^186)
                     + divstep.Trans.r mtx * (e mod 2^186)
                     + (m mod 2^186) * me) 124) by
(apply (Hcarry 62);[lia|assumption]).
assert (Hcd248 : cd3 = Z.shiftr (divstep.Trans.u mtx * (d mod 2^248)
                     + divstep.Trans.v mtx * (e mod 2^248)
                     + (m mod 2^248) * md) 186) by
(apply (Hcarry 124);[lia|assumption]).
assert (Hce248 : ce3 = Z.shiftr (divstep.Trans.q mtx * (d mod 2^248)
                     + divstep.Trans.r mtx * (e mod 2^248)
                     + (m mod 2^248) * me) 186) by
(apply (Hcarry 124);[lia|assumption]).
assert (Hcd310 : cd4 = Z.shiftr (divstep.Trans.u mtx * d
                     + divstep.Trans.v mtx * e
                     + m * md) 248).
1:{
  unfold cd4, m4.
  symmetry.
  rewrite (Z_div_mod_eq_full d (2^248)) at 1.
  rewrite (Z_div_mod_eq_full e (2^248)) at 1.
  rewrite (Z_div_mod_eq_full m (2^248)) at 1.
  replace (divstep.Trans.u mtx * (2 ^ 248 * (d / 2 ^ 248) + d mod 2 ^ 248)
     + divstep.Trans.v mtx * (2 ^ 248 * (e / 2 ^ 248) + e mod 2 ^ 248)
     + (2 ^ 248 * (m / 2 ^ 248) + m mod 2 ^ 248) * md)
   with
    ((divstep.Trans.u mtx * (d / 2 ^ 248) + divstep.Trans.v mtx * (e / 2 ^ 248) + (m / 2 ^ 248) * md) * 2^248
     + (divstep.Trans.u mtx * (d mod 2 ^ 248) + divstep.Trans.v mtx * (e mod 2 ^ 248) + (m mod 2 ^ 248) * md))
   by ring.
  rewrite Hcd248, Z.shiftr_shiftr, !Z.shiftr_div_pow2, Z.div_add_l by lia.
  change (186 + 62) with 248.
  ring.
}
assert (Hce310 : ce4 = Z.shiftr (divstep.Trans.q mtx * d
                     + divstep.Trans.r mtx * e
                     + m * me) 248).
1:{
  unfold ce4, m4.
  symmetry.
  rewrite (Z_div_mod_eq_full d (2^248)) at 1.
  rewrite (Z_div_mod_eq_full e (2^248)) at 1.
  rewrite (Z_div_mod_eq_full m (2^248)) at 1.
  replace (divstep.Trans.q mtx * (2 ^ 248 * (d / 2 ^ 248) + d mod 2 ^ 248)
     + divstep.Trans.r mtx * (2 ^ 248 * (e / 2 ^ 248) + e mod 2 ^ 248)
     + (2 ^ 248 * (m / 2 ^ 248) + m mod 2 ^ 248) * me)
   with
    ((divstep.Trans.q mtx * (d / 2 ^ 248) + divstep.Trans.r mtx * (e / 2 ^ 248) + (m / 2 ^ 248) * me) * 2^248
     + (divstep.Trans.q mtx * (d mod 2 ^ 248) + divstep.Trans.r mtx * (e mod 2 ^ 248) + (m mod 2 ^ 248) * me))
   by ring.
  rewrite Hce248, Z.shiftr_shiftr, !Z.shiftr_div_pow2, Z.div_add_l by lia.
  change (186 + 62) with 248.
  ring.
}
set (cd := divstep.Trans.u mtx * d + divstep.Trans.v mtx * e + m * md) in *.
set (ce := divstep.Trans.q mtx * d + divstep.Trans.r mtx * e + m * me) in *.
replace dval4 with (map Vlong (Signed62.reprn 5 (Z.shiftr cd 62))).
2:{
  cbn.
  rewrite !Z.shiftr_shiftr by lia.
  change dval4 with
  [ (Vlong (Int64.repr (cd1 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (cd2 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (cd3 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (cd4 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (Z.shiftr cd4 62)))
  ].
  cbn.
  rewrite <-!Z.land_ones by lia.
  rewrite Hcd124, Hcd186, Hcd248, Hcd310.
  rewrite <-(Z.shiftr_land _ (Z.ones 124) 62).
  rewrite <-(Z.shiftr_land _ (Z.ones 186) 124).
  rewrite <-(Z.shiftr_land _ (Z.ones 248) 186).
  rewrite <-(Z.shiftr_land _ (Z.ones 310) 248).
  symmetry.
  rewrite <-(Z.shiftr_land _ (Z.ones 124) 62).
  rewrite <-(Z.shiftr_land _ (Z.ones 186) 124).
  rewrite <-(Z.shiftr_land _ (Z.ones 248) 186).
  rewrite !Z.land_ones by lia.
  repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || f_equal).
}
replace eval4 with (map Vlong (Signed62.reprn 5 (Z.shiftr ce 62))).
2:{
  cbn.
  rewrite !Z.shiftr_shiftr by lia.
  change eval4 with
  [ (Vlong (Int64.repr (ce1 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (ce2 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (ce3 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (ce4 mod 2 ^ 62)))
  ; (Vlong (Int64.repr (Z.shiftr ce4 62)))
  ].
  cbn.
  rewrite <-!Z.land_ones by lia.
  rewrite Hce124, Hce186, Hce248, Hce310.
  rewrite <-(Z.shiftr_land _ (Z.ones 124) 62).
  rewrite <-(Z.shiftr_land _ (Z.ones 186) 124).
  rewrite <-(Z.shiftr_land _ (Z.ones 248) 186).
  rewrite <-(Z.shiftr_land _ (Z.ones 310) 248).
  symmetry.
  rewrite <-(Z.shiftr_land _ (Z.ones 124) 62).
  rewrite <-(Z.shiftr_land _ (Z.ones 186) 124).
  rewrite <-(Z.shiftr_land _ (Z.ones 248) 186).
  rewrite !Z.land_ones by lia.
  repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || f_equal).
}
assert (Hcd' : cd = (divstep.Trans.u mtx * (d + if d <? 0 then m else 0)
                  + divstep.Trans.v mtx * (e + if e <? 0 then m else 0)
                  - m * ((modInv m (2 ^ 62) * cd0 + md0) mod 2^62))).
1:{
  unfold cd, md.
  set (X := modInv _ _ * _ + _).
  unfold md0.
  destruct (d <? 0);destruct (e <? 0);ring.
}
assert (Hce' : ce = (divstep.Trans.q mtx * (d + if d <? 0 then m else 0)
                  + divstep.Trans.r mtx * (e + if e <? 0 then m else 0)
                  - m * ((modInv m (2 ^ 62) * ce0 + me0) mod 2^62))).
1:{
  unfold ce, me.
  set (X := modInv _ _ * _ + _).
  unfold me0.
  destruct (d <? 0);destruct (e <? 0);ring.
}
replace (Z.shiftr cd 62) with (fst (divstep.update_de m d e mtx)) in *.
2:{
  unfold divstep.update_de.
  rewrite <-!Z.shiftr_div_pow2 by lia.
  cbn.
  rewrite Hcd'.
  f_equal.
  f_equal.
  rewrite Z.mul_comm; f_equal.
  transitivity
   (((if d <? 0 then (divstep.Trans.u mtx * (modInv m (2 ^ 62) * d + modInv m (2 ^ 62) * m)) mod 2^62 else (modInv m (2 ^ 62) * (divstep.Trans.u mtx * d)) mod 2^62)
   + (if e <? 0 then (divstep.Trans.v mtx * (modInv m (2 ^ 62) * e + modInv m (2 ^ 62) * m)) mod 2^62 else (modInv m (2 ^ 62) * (divstep.Trans.v mtx * e)) mod 2^62))
   mod 2^62);
  [destruct (d <? 0); destruct (e <? 0);rewrite <-!Z.add_mod by lia;f_equal;ring|].
  rewrite <- (Zmult_mod_idemp_r _ (divstep.Trans.u mtx)), <- (Zmult_mod_idemp_r _ (divstep.Trans.v mtx)), <-!(Zplus_mod_idemp_r (_ * m)).
  rewrite modInv_mul_l, Hoddm by lia.
  transitivity (((if d <? 0
  then
   (divstep.Trans.u mtx * ((modInv m (2 ^ 62) * (d mod 2 ^ 62) + 1)))
  else (modInv m (2 ^ 62) * (divstep.Trans.u mtx * (d mod 2 ^ 62))))
   + (if e <? 0
      then
       (divstep.Trans.v mtx * ((modInv m (2 ^ 62) * (e mod 2 ^ 62) + 1)))
      else (modInv m (2 ^ 62) * (divstep.Trans.v mtx * (e mod 2 ^ 62))))) mod 
    2 ^ 62);
  [destruct (d <? 0); destruct (e <? 0);
    repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || (unfold eqm; rewrite Zmod_mod))
  |].
  unfold cd0, md0.
  f_equal.
  destruct (d <? 0); destruct (e <? 0); ring.
}
replace (Z.shiftr ce 62) with (snd (divstep.update_de m d e mtx)) in *.
2:{
  unfold divstep.update_de.
  rewrite <-!Z.shiftr_div_pow2 by lia.
  cbn.
  rewrite Hce'.
  f_equal.
  f_equal.
  rewrite Z.mul_comm; f_equal.
  transitivity
   (((if d <? 0 then (divstep.Trans.q mtx * (modInv m (2 ^ 62) * d + modInv m (2 ^ 62) * m)) mod 2^62 else (modInv m (2 ^ 62) * (divstep.Trans.q mtx * d)) mod 2^62)
   + (if e <? 0 then (divstep.Trans.r mtx * (modInv m (2 ^ 62) * e + modInv m (2 ^ 62) * m)) mod 2^62 else (modInv m (2 ^ 62) * (divstep.Trans.r mtx * e)) mod 2^62))
   mod 2^62);
  [destruct (d <? 0); destruct (e <? 0);rewrite <-!Z.add_mod by lia;f_equal;ring|].
  rewrite <- (Zmult_mod_idemp_r _ (divstep.Trans.q mtx)), <- (Zmult_mod_idemp_r _ (divstep.Trans.r mtx)), <-!(Zplus_mod_idemp_r (_ * m)).
  rewrite modInv_mul_l, Hoddm by lia.
  transitivity (((if d <? 0
  then
   (divstep.Trans.q mtx * ((modInv m (2 ^ 62) * (d mod 2 ^ 62) + 1)))
  else (modInv m (2 ^ 62) * (divstep.Trans.q mtx * (d mod 2 ^ 62))))
   + (if e <? 0
      then
       (divstep.Trans.r mtx * ((modInv m (2 ^ 62) * (e mod 2 ^ 62) + 1)))
      else (modInv m (2 ^ 62) * (divstep.Trans.r mtx * (e mod 2 ^ 62))))) mod 
    2 ^ 62);
  [destruct (d <? 0); destruct (e <? 0);
    repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || (unfold eqm; rewrite Zmod_mod))
  |].
  unfold ce0, me0.
  f_equal.
  destruct (d <? 0); destruct (e <? 0); ring.
}
rewrite <- Zodd_equiv in H.
destruct (divstep.update_de_bound m d e mtx) as [Hcdm Hcem]; try assumption.
assert (Hcd62 : -2 ^ (62 * Z.of_nat 5 + 1) <= fst (divstep.update_de m d e mtx) <= 2 ^ (62 * Z.of_nat 5 + 1) - 1) by lia.
assert (Hce62 : -2 ^ (62 * Z.of_nat 5 + 1) <= snd (divstep.update_de m d e mtx) <= 2 ^ (62 * Z.of_nat 5 + 1) - 1) by lia.
change mval with (map Vlong (Signed62.reprn 5 m)).
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  change mval with (map Vlong (Signed62.reprn 5 m)).
  forward_call (fst (divstep.update_de m d e mtx), 5%nat, m, -2, ptrd, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, shd, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Gt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (fst (divstep.update_de m d e mtx), 5%nat, m, 1, ptrd, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, shd, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Lt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
1:{
  unfold_data_at (data_at _ _ _ ptrm).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
  forward_call (snd (divstep.update_de m d e mtx), 5%nat, m, -2, ptre, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, she, shm);
  [rewrite field_address_offset by assumption;entailer!|].
  rewrite Zaux.Zcompare_Gt by lia.
  forward_if;[discriminate|forward].
  unfold_data_at (data_at _ _ _ ptrm).
  entailer!!.
}
forward_verify_check.
unfold_data_at (data_at _ _ _ ptrm).
assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm);[entailer!|].
forward_call (snd (divstep.update_de m d e mtx), 5%nat, m, 1, ptre, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) ptrm, she, shm);
[rewrite field_address_offset by assumption;entailer!|].
rewrite Zaux.Zcompare_Lt by lia.
match goal with
| |- semax _ ?E _ _ => forward_if E;[discriminate|forward;entailer!!|]
end.
forward.
unfold_data_at (data_at _ _ _ ptrm).
entailer!!.
unfold secp256k1_uint128_at, t_secp256k1_uint128.
set (X := (_,_)).
set (Y := (_,_)).
clearbody X Y.
clear -X Y.
apply sepcon_derives;apply data_at_data_at_.
Qed.

Lemma body_modinv64_update_fg_62_var: semax_body Vprog Gprog f_secp256k1_modinv64_update_fg_62_var secp256k1_modinv64_update_fg_62_var_spec.
Proof.
start_function.
set (f := divstep.f st).
set (g := divstep.g st).
unfold Trans_repr.
do 5 forward.
forward_verify_check.
1:{
  revert H2.
  convert_C_to_math.
  elim Z.ltb_spec; try discriminate.
  lia.
}
assert (HZnth : forall a i, 0 <= i < Z.of_nat len ->
        Znth i (Signed62.reprn len a) =
        Int64.repr (Z.shiftr (if Z.of_nat len =? i + 1 then a else a mod 2^(62 * (i + 1))) (62 * i))).
1:{
  intros a i Hi.
  rewrite f_if, (f_if (fun f => f (62 * i))).
  rewrite Z.mul_add_distr_l, (Z.add_comm (62 * i)), <- Z_shiftr_mod_2 by lia.
  assert (Ha := Signed62.reprn_Zlength len a).
  elim (Z.eqb_spec); intros Hlen.
  * replace i with (Z.of_nat len - 1)%Z by lia.
    rewrite <- Ha at 1.
    rewrite Znth_last, Signed62.reprn_last by lia.
    reflexivity.
  * rewrite Signed62.reprn_Znth by lia.
    reflexivity.
}
assert (HZnth0 : forall a, @Znth _ Vundef 0 (Signed62.pad (Signed62.reprn len a)) =
        Vlong (Int64.repr (if Z.of_nat len =? 1 then a else a mod 2^62))).
1:{
  intros a.
  specialize (HZnth a 0).
  rewrite Z.shiftr_0_r in HZnth.
  assert (Ha := Signed62.reprn_Zlength len a).
  rewrite Signed62.pad_nth by lia.
  destruct len;[lia|]. 
  destruct len.
  * rewrite HZnth by lia.
    reflexivity.
  * replace (Z.of_nat (S (S len)) =? 0 + 1) with false in HZnth by
    (symmetry;apply Z.eqb_neq; lia).
    rewrite HZnth by lia.
    rewrite <- zeq_eqb.
    destruct zeq;try reflexivity.
    lia.
}
forward;[rewrite HZnth0;entailer!!|].
forward;[rewrite (HZnth0 g);entailer!!|].
fold t_secp256k1_uint128.
rewrite (HZnth0 f), (HZnth0 g).
clear HZnth0.
pose (fi := fun i => if Z.of_nat len =? i then f else f mod 2^(62*i)).
pose (gi := fun i => if Z.of_nat len =? i then g else g mod 2^(62*i)).
change (if Z.of_nat len =? 1 then f else _) with (fi 1).
change (if Z.of_nat len =? 1 then g else _) with (gi 1).
assert (Hfij : forall i j, j <= Z.of_nat len -> 0 <= i < j -> (fi j) mod 2^(62 * i) = fi i).
1:{
 intros i j Hj Hij.
 unfold fi.
 replace (Z.of_nat len =? i) with false by lia.
 destruct (Z.of_nat len =? j); try reflexivity.
 rewrite <- !Z.land_ones, <- Z.land_assoc, Z_land_ones_min, Z.min_r by lia.
 reflexivity.
}
assert (Hgij : forall i j, j <= Z.of_nat len -> 0 <= i < j -> (gi j) mod 2^(62 * i) = gi i).
1:{
 intros i j Hj Hij.
 unfold gi.
 replace (Z.of_nat len =? i) with false by lia.
 destruct (Z.of_nat len =? j); try reflexivity.
 rewrite <- !Z.land_ones, <- Z.land_assoc, Z_land_ones_min, Z.min_r by lia.
 reflexivity.
}
assert (Hfi : forall i, 0 <= i -> -2 ^ (62*i + 1) <= fi i <= 2 ^ (62*i + 1) - 1).
1:{
 intros i Hi.
 unfold fi.
 elim Z.eqb_spec;[intros <-; lia|intros _].
 cut (0 <= f mod 2 ^ (62 * i) <= 2 ^ (62 * i) - 1);
 [rewrite Z.pow_add_r;lia|solve_bounds].
}
assert (Hgi : forall i, 0 <= i -> -2 ^ (62*i + 1) <= gi i <= 2 ^ (62*i + 1) - 1).
1:{
 intros i Hi.
 unfold gi.
 elim Z.eqb_spec;[intros <-; lia|intros _].
 cut (0 <= g mod 2 ^ (62 * i) <= 2 ^ (62 * i) - 1);
 [rewrite Z.pow_add_r;lia|solve_bounds].
}
assert (Hf1 := Hfi 1).
assert (Hg1 := Hgi 1).
destruct (divstep.Trans.bounded_transN 62 st) as [[Huv Huv'] [Hqr Hqr']].
set (u := divstep.Trans.u (divstep.Trans.transN 62 st)) in *.
set (v := divstep.Trans.v (divstep.Trans.transN 62 st)) in *.
set (q := divstep.Trans.q (divstep.Trans.transN 62 st)) in *.
set (r := divstep.Trans.r (divstep.Trans.transN 62 st)) in *.
set (T := (Vlong (Int64.repr u),(Vlong (Int64.repr v),
       (Vlong (Int64.repr q), Vlong (Int64.repr r))))).
assert (H6262i : forall a b x y, -2 ^ a <= x <= 2 ^ a -> -2 ^ b <= y <= 2 ^ b ->
  -(2 ^ a * 2 ^ b) <= x * y <= 2 ^ a * 2 ^ b).
1:{
 intros a b x y Hx Hy.
 rewrite <- Z.abs_le in *.
 rewrite Z.abs_mul.
 etransitivity;[apply Z.mul_le_mono_nonneg_l;[|apply Hy]|apply Z.mul_le_mono_nonneg_r];lia.
}
assert (Hufi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= u * fi i <= 2 ^ 62 * 2^(62 * i + 1))
 by (intros;specialize (Hfi i);apply H6262i;lia).
assert (Hvgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= v * gi i <= 2 ^ 62 * 2^(62 * i + 1))
 by (intros;specialize (Hgi i);apply H6262i;lia).
assert (Huf1 := Hufi 1).
assert (Hvg1 := Hvgi 1).
forward_call (v_cf, Tsh, u, fi 1).
forward_call.
1: unfold Int128_min_signed, Int128_max_signed;lia.
assert (Hqfi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= q * fi i <= 2 ^ 62 * 2^(62 * i + 1))
 by (intros;specialize (Hfi i);apply H6262i;lia).
assert (Hrgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= r * gi i <= 2 ^ 62 * 2^(62 * i + 1))
 by (intros;specialize (Hgi i);apply H6262i;lia).
assert (Hqf1 := Hqfi 1).
assert (Hrg1 := Hrgi 1).
forward_call (v_cg, Tsh, q, fi 1).
forward_call.
1: unfold Int128_min_signed, Int128_max_signed;lia.
change (Int64.shru _ _) with (Int64.repr (Z.ones 62)).
set (f1 := divstep.f (fst (divstep.stepN 62 st))).
set (g1 := divstep.g (fst (divstep.stepN 62 st))).
assert (Hfg := divstep.Trans.transN_step 62 st).
injection Hfg as Htransf Htransg.
change (2^62 * f1 = u*f + v*g) in Htransf.
change (2^62 * g1 = q*f + r*g) in Htransg.
assert (Hfi62 : forall i, 0 <= i -> fi i mod 2^(62*i) = f mod 2^(62*i)) by
 (intros; unfold fi; destruct Z.eqb; rewrite ?Zmod_mod; reflexivity).
assert (Hgi62 : forall i, 0 <= i -> gi i mod 2^(62*i) = g mod 2^(62*i)) by
 (intros; unfold gi; destruct Z.eqb; rewrite ?Zmod_mod; reflexivity).
forward_verify_check.
1:{
  forward_call.
  forward_if;[|forward;entailer!!].
  exfalso.
  revert H2.
  convert_C_to_math.
  change (_ + _) with (u*(fi 1) + v*(gi 1)).
  rewrite <-(Z.land_ones _ 64), <-Z.land_assoc by lia.
  change (Z.land (Z.ones _) _) with (Z.ones 62).
  rewrite Z.land_ones by lia.
  rewrite <- Zplus_mod_idemp_l, <- Zmult_mod_idemp_r, Hfi62,
          Zmult_mod_idemp_r, Zplus_mod_idemp_l by lia.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hgi62,
          Zmult_mod_idemp_r, Zplus_mod_idemp_r by lia.
  rewrite <- Htransf, Z.mul_comm, Z_mod_mult, Z.eqb_refl.
  discriminate.
}
forward_call.
1: unfold Int128_min_signed, Int128_max_signed;lia.
forward_verify_check.
1:{
  forward_call.
  forward_if;[|forward;entailer!!].
  exfalso.
  revert H2.
  convert_C_to_math.
  change (_ + _) with (q*(fi 1) + r*(gi 1)).
  rewrite <-(Z.land_ones _ 64), <-Z.land_assoc by lia.
  change (Z.land (Z.ones _) _) with (Z.ones 62).
  rewrite Z.land_ones by lia.
  rewrite <- Zplus_mod_idemp_l, <- Zmult_mod_idemp_r, Hfi62,
          Zmult_mod_idemp_r, Zplus_mod_idemp_l by lia.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hgi62,
          Zmult_mod_idemp_r, Zplus_mod_idemp_r by lia.
  rewrite <- Htransg, Z.mul_comm, Z_mod_mult, Z.eqb_refl.
  discriminate.
}
forward_call.
1: unfold Int128_min_signed, Int128_max_signed;lia.
assert (Hlength_firstn_skipn : forall n m x y,
    Zlength (firstn (Z.to_nat n) (Signed62.reprn m x) ++ skipn (Z.to_nat n) (Signed62.reprn m y)) = Z.of_nat m)
  by (intros; rewrite Zlength_app, Zlength_firstn, Zlength_skipn, !Signed62.reprn_Zlength; lia).
forward_for_simple_bound (Z.of_nat len)
(EX i:Z, PROP ( )
   LOCAL (temp _r (Vlong (Int64.repr r));
   temp _q (Vlong (Int64.repr q)); temp _v (Vlong (Int64.repr v));
   temp _u (Vlong (Int64.repr u));
   temp _M62 (Vlong (Int64.repr (Z.ones 62)));
   lvar _cg t_secp256k1_uint128 v_cg; lvar _cf t_secp256k1_uint128 v_cf;
   temp _len (Vint (Int.repr (Z.of_nat len))); 
   temp _f ptrf; temp _g ptrg; temp _t ptrt)
   SEP (secp256k1_uint128_at Tsh (Z.shiftr (q * (fi i) + r * (gi i)) (62*i)) v_cg;
   secp256k1_uint128_at Tsh (Z.shiftr (u * (fi i) + v * (gi i)) (62*i)) v_cf;
   data_at shf t_secp256k1_modinv64_signed62
     (Signed62.pad (firstn (Z.to_nat (i - 1)) (Signed62.reprn len ((u * f + v * g) / 2^62)) ++ skipn (Z.to_nat (i - 1)) (Signed62.reprn len f))) ptrf;
   data_at shg t_secp256k1_modinv64_signed62
     (Signed62.pad (firstn (Z.to_nat (i - 1)) (Signed62.reprn len ((q * f + r * g) / 2^62)) ++ skipn (Z.to_nat (i - 1)) (Signed62.reprn len g))) ptrg;
   data_at sht t_secp256k1_modinv64_trans2x2 T ptrt))%assert.  
* entailer!!.
* do 2 (forward;rewrite !Signed62.pad_nth by (rewrite Hlength_firstn_skipn;lia);try entailer).
  rewrite !Znth_app2;rewrite !Zlength_firstn; try lia.
  rewrite !Signed62.reprn_Zlength, !Znth_skipn by lia.
  replace (i - Z.min (Z.max 0 (i - 1)) (Z.of_nat len) + (i - 1)) with i by lia.
  rewrite !HZnth by lia.
  fold (fi (i + 1)) (gi (i + 1)).
  assert (Hi01 : 0 <= i + 1) by lia.
  assert (Hi0 : 0 <= i) by lia.
  specialize (Hfi _ Hi01);
  specialize (Hgi _ Hi01).
  rewrite !Z.mul_add_distr_l, !Z.pow_add_r in Hfi, Hgi by lia.
  assert (Hfi_boundA : -2^63 <= Z.shiftr (fi (i + 1)) (62 * i) <= 2^63) by solve_bounds.
  assert (Hfi_boundB : -(2^62 * 2^63) <= u * Z.shiftr (fi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
  assert (Hgi_boundA : -2^63 <= Z.shiftr (gi (i + 1)) (62 * i) <= 2^63) by solve_bounds.
  assert (Hgi_boundB : -(2^62 * 2^63) <= v * Z.shiftr (gi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
  specialize (Hufi _ Hi0);
  specialize (Hvgi _ Hi0);
  specialize (Hqfi _ Hi0);
  specialize (Hrgi _ Hi0).
  rewrite !Z.pow_add_r in Hufi, Hvgi, Hqfi, Hrgi by lia.
  assert (Hfgi_boundA : -2^64 <= Z.shiftr (u * fi i + v * gi i) (62 * i) <= 2^64) by solve_bounds.
  forward_call;[unfold Int128_min_signed, Int128_max_signed;split;solve_bounds|].
  forward_call;[unfold Int128_min_signed, Int128_max_signed;split;solve_bounds|].
  assert (Hfi_boundC : -(2^62 * 2^63) <= q * Z.shiftr (fi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
  assert (Hgi_boundC : -(2^62 * 2^63) <= r * Z.shiftr (gi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
  assert (Hfgi_boundB : -2^64 <= Z.shiftr (q * fi i + r * gi i) (62 * i) <= 2^64) by solve_bounds.
  forward_call;[unfold Int128_min_signed, Int128_max_signed;split;solve_bounds|].
  forward_call;[unfold Int128_min_signed, Int128_max_signed;split;solve_bounds|].
  forward_call;forward;forward_call;[unfold Int128_min_signed, Int128_max_signed;solve_bounds|].
  forward_call;forward;forward_call;[unfold Int128_min_signed, Int128_max_signed;solve_bounds|].
  replace (Z.shiftr (u * fi i + v * gi i) (62 * i) + u * Z.shiftr (fi (i + 1)) (62 * i) + v * Z.shiftr (gi (i + 1)) (62 * i))
   with (Z.shiftr (u * fi (i + 1) + v * gi (i + 1)) (62 * i)).
  2:{
    rewrite (Z_div_mod_eq_full (fi (i + 1)) (2^(62 * i))) at 1.
    rewrite (Z_div_mod_eq_full (gi (i + 1)) (2^(62 * i))) at 1.
    rewrite Hfij, Hgij by lia.
    replace (u * ((2^(62 * i)) * (fi (i + 1) / (2^(62 * i))) + fi i) + v * ((2^(62 * i)) * (gi (i + 1) / (2^(62 * i))) + gi i))
     with ((u * fi i + v * gi i) + ((u * (fi (i + 1) / (2^(62 * i))) + v * (gi (i + 1) / (2^(62 * i)))) *  2^(62 * i))) by ring.
    rewrite !Z.shiftr_div_pow2, Z.div_add by lia.
    ring.
  }
  replace (Z.shiftr (q * fi i + r * gi i) (62 * i) + q * Z.shiftr (fi (i + 1)) (62 * i) + r * Z.shiftr (gi (i + 1)) (62 * i))
   with (Z.shiftr (q * fi (i + 1) + r * gi (i + 1)) (62 * i)).
  2:{
    rewrite (Z_div_mod_eq_full (fi (i + 1)) (2^(62 * i))) at 1.
    rewrite (Z_div_mod_eq_full (gi (i + 1)) (2^(62 * i))) at 1.
    rewrite Hfij, Hgij by lia.
    replace (q * ((2^(62 * i)) * (fi (i + 1) / (2^(62 * i))) + fi i) + r * ((2^(62 * i)) * (gi (i + 1) / (2^(62 * i))) + gi i))
     with ((q * fi i + r * gi i) + ((q * (fi (i + 1) / (2^(62 * i))) + r * (gi (i + 1) / (2^(62 * i)))) *  2^(62 * i))) by ring.
    rewrite !Z.shiftr_div_pow2, Z.div_add by lia.
    ring.
  }
  rewrite !Z.shiftr_shiftr by lia.
  convert_C_to_math.
  rewrite !Signed62.pad_upd_Znth by (rewrite Hlength_firstn_skipn; lia).
  rewrite !upd_Znth_app2 by (rewrite Zlength_firstn, Zlength_skipn, Signed62.reprn_Zlength; lia).
  rewrite !Zlength_firstn, !Signed62.reprn_Zlength.
  replace (i - 1 - Z.min (Z.max 0 (i - 1)) (Z.of_nat len)) with 0 by lia.
  rewrite !(skipn_cons (Z.to_nat (i - 1))) by (rewrite Signed62.reprn_length; lia).
  rewrite !upd_Znth0.
  replace (S (Z.to_nat (i - 1))) with (Z.to_nat (i + 1 - 1)) by lia.
  replace (Z.ones 62) with (Z.ones (62 * (i + 1) - 62 * i)) by (f_equal;ring).
  rewrite <- !Z_shiftr_ones, <- !Z.shiftr_land, !Z.land_ones by lia.
  rewrite !(Z.add_mod (_*_) (_*_)), <-!(Z.mul_mod_idemp_r _ (fi (i + 1))), <-!(Z.mul_mod_idemp_r _ (gi (i+1))) by lia.
  rewrite !Hfi62, !Hgi62 by lia.
  rewrite !Z.mul_mod_idemp_r, <-!Z.add_mod by lia.
  replace (62 * (i + 1)) with (62 + 62 * i) by ring.
  rewrite <- !Z_shiftr_mod_2 by lia.
  replace (62 * i) with (62 + (62 * (i - 1))) by ring.
  rewrite <- !(Z.shiftr_shiftr _ 62 (62 * (i - 1))), !(Z.shiftr_div_pow2 _ 62) by lia.
  rewrite <- !(Signed62.reprn_Znth _ len) by lia.
  rewrite !Znth_cons by (rewrite Signed62.reprn_Zlength; lia).
  rewrite !app_assoc, !firstn_app, <- Z2Nat.inj_add by lia.
  replace (i - 1 + 1) with (i + 1 - 1) by lia.
  rewrite !(Z.add_comm _ 62).
  entailer!!.
* unfold fi, gi.
  rewrite !Z.eqb_refl.
  assert (Hcfdg : forall c d, Z.abs c + Z.abs d <= 2^62 -> -2^62 < c + d ->
     -(2^63 * 2^(62 * Z.of_nat len)) <= c * f + d * g < 2^63 * 2^(62 * Z.of_nat len)).
  1:{
    intros c d Hcd0 Hcd1.
    rewrite <- Z.pow_add_r by lia.
    replace (63 + 62 * Z.of_nat len) with (62 + (62 * Z.of_nat len + 1)) by ring.
    rewrite Z.pow_add_r by lia.
    split;[|destruct (Z_le_lt_dec c 0); destruct (Z_le_lt_dec d 0)].
    * cut (Z.abs (c * f) + Z.abs (d * g) <= 2 ^ 62 * 2 ^ (62 * Z.of_nat len + 1));[lia|].
      transitivity (Z.abs (c * f) + Z.abs (d * g));[lia|].
      rewrite !Z.abs_mul.
      transitivity (Z.abs c * Z.max (Z.abs f) (Z.abs g) + Z.abs d * Z.max (Z.abs f) (Z.abs g));
      [apply Z.add_le_mono; apply Zmult_le_compat_l; lia|].
      rewrite <- Z.mul_add_distr_r.
      apply Zmult_le_compat; lia.
    * apply Z.le_lt_trans with (c * (-2 ^ (62 * Z.of_nat len + 1)) + d * (-2 ^ (62 * Z.of_nat len + 1)));
      [apply Z.add_le_mono;apply Z.mul_le_mono_nonpos_l;lia|].
      replace (c * -2 ^ (62 * Z.of_nat len + 1) + d * -2 ^ (62 * Z.of_nat len + 1))
       with (-(c + d) * 2 ^ (62 * Z.of_nat len + 1)) by ring.
      apply Zmult_lt_compat_r;lia.
    * apply Z.le_lt_trans with (c * (-2 ^ (62 * Z.of_nat len + 1)) + d * (2 ^ (62 * Z.of_nat len + 1) - 1));
      [apply Z.add_le_mono;[apply Z.mul_le_mono_nonpos_l|apply Z.mul_le_mono_nonneg_l];lia|].
      replace (c * -2 ^ (62 * Z.of_nat len + 1) + d * (2 ^ (62 * Z.of_nat len + 1) - 1))
       with ((d - c) * (2 ^ (62 * Z.of_nat len + 1)) - d) by ring.
      apply Z.le_lt_trans with (2^62 * (2 ^ (62 * Z.of_nat len + 1)) - d);
      [apply Z.add_le_mono_r;apply Zmult_le_compat_r;lia|lia].
    * apply Z.le_lt_trans with (c * (2 ^ (62 * Z.of_nat len + 1) - 1) + d * (-2 ^ (62 * Z.of_nat len + 1)));
      [apply Z.add_le_mono;[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonpos_l];lia|].
      replace (c * (2 ^ (62 * Z.of_nat len + 1) - 1) + d * (-2 ^ (62 * Z.of_nat len + 1)))
       with ((c - d) * (2 ^ (62 * Z.of_nat len + 1)) - c) by ring.
      apply Z.le_lt_trans with (2^62 * (2 ^ (62 * Z.of_nat len + 1)) - c);
      [apply Z.add_le_mono_r;apply Zmult_le_compat_r;lia|lia].
    * apply Z.le_lt_trans with (c * (2 ^ (62 * Z.of_nat len + 1) - 1) + d * (2 ^ (62 * Z.of_nat len + 1) - 1));
      [apply Z.add_le_mono; apply Z.mul_le_mono_nonneg_l;lia|].
      replace (c * (2 ^ (62 * Z.of_nat len + 1) - 1) + d * (2 ^ (62 * Z.of_nat len + 1) - 1))
       with ((c + d) * (2 ^ (62 * Z.of_nat len + 1) - 1)) by ring.
      apply Z.le_lt_trans with (2^62 * (2 ^ (62 * Z.of_nat len + 1) - 1));
      [apply Zmult_le_compat_r;lia|lia].
  }
  assert (Hufvg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= u * f + v * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len)) by
    (apply Hcfdg; lia).
  assert (Hqfrg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= q * f + r * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len)) by
    (apply Hcfdg; lia).
  forward_call;[solve_bounds|].
  forward.
  forward_call;[solve_bounds|].
  forward.
  rewrite !Signed62.pad_upd_Znth by (rewrite Hlength_firstn_skipn; lia).
  rewrite !upd_Znth_app2 by (rewrite Zlength_firstn, Zlength_skipn, Signed62.reprn_Zlength; lia).
  rewrite !Zlength_firstn, !Signed62.reprn_Zlength.
  replace (Z.of_nat len - 1 - Z.min (Z.max 0 (Z.of_nat len - 1)) (Z.of_nat len)) with 0 by lia.
  rewrite !(skipn_cons (Z.to_nat (Z.of_nat len - 1))) by (rewrite Signed62.reprn_length; lia).
  rewrite !upd_Znth0.
  replace (S (Z.to_nat (Z.of_nat len - 1))) with (len) by lia.
  rewrite !skipn_short by (rewrite Signed62.reprn_length;lia).
  replace (62 * Z.of_nat len) with (62 + (62 * (Z.of_nat len - 1))) by ring.
  rewrite <- !(Z.shiftr_shiftr _ 62 (62 * (Z.of_nat len - 1))), !(Z.shiftr_div_pow2 _ 62) by lia.
  replace (Z.to_nat (Z.of_nat len - 1)) with (Init.Nat.pred (Datatypes.length (Signed62.reprn len ((u * f + v * g) / 2 ^ 62)))) at 1
   by (rewrite Signed62.reprn_length; lia).
  replace (Z.to_nat (Z.of_nat len - 1)) with (Init.Nat.pred (Datatypes.length (Signed62.reprn len ((q * f + r * g) / 2 ^ 62))))
   by (rewrite Signed62.reprn_length; lia).
  rewrite <- !removelast_firstn_len, <- !(Signed62.reprn_last _ len default) by lia.
  rewrite <- !app_removelast_last by (rewrite <- length_zero_iff_nil, Signed62.reprn_length; lia).
  rewrite <- Htransf, <- Htransg, !(Z.mul_comm (2 ^ 62)), !Z.div_mul by lia.
  unfold secp256k1_uint128_at.
  sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128
  (Vlong (Int64.repr (Z.shiftr f1 (62 * (Z.of_nat len - 1)))),
   Vlong
     (Int64.repr (Z.shiftr (Z.shiftr f1 (62 * (Z.of_nat len - 1))) 64)))
  v_cf).
  sep_apply (data_at_data_at_ Tsh t_secp256k1_uint128
  (Vlong (Int64.repr (Z.shiftr g1 (62 * (Z.of_nat len - 1)))),
   Vlong
     (Int64.repr (Z.shiftr (Z.shiftr g1 (62 * (Z.of_nat len - 1))) 64)))
  v_cg).
  entailer!!.
Qed.

Lemma body_secp256k1_modinv64_var: semax_body Vprog Gprog f_secp256k1_modinv64_var secp256k1_modinv64_var_spec.
Proof.
start_function.
fastforward 5.
change (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 0)).
fastforward 5.
change (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 1)).
unfold make_modinfo.
unfold_data_at (data_at _ _ _ modinfo).
assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo) by entailer.
forward_call (m, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
[rewrite field_address_offset by assumption;entailer!!|].
change (data_at sh_modinfo t_secp256k1_modinv64_signed62) with
 (data_at sh_modinfo (nested_field_type t_secp256k1_modinv64_modinfo (DOT _modulus))).
rewrite <- field_at_data_at.
assert (Hmodinfo :
 ((field_at sh_modinfo t_secp256k1_modinv64_modinfo (DOT _modulus) (map Vlong (Signed62.reprn 5 m)) modinfo) *
  (field_at sh_modinfo t_secp256k1_modinv64_modinfo (DOT _modulus_inv62) (Vlong (Int64.repr (modInv m (2 ^ 62)))) modinfo) |--
  data_at sh_modinfo t_secp256k1_modinv64_modinfo (map Vlong (Signed62.reprn 5 m), Vlong (Int64.repr (modInv m (2 ^ 62)))) modinfo))
 by (unfold_data_at (data_at _ _ _ modinfo);entailer!!).
sep_apply Hmodinfo.
fold (make_modinfo m).
clear Hmodinfo.
forward_call.
fastforward 3.
change (Int.neg (Int.repr 1)) with (Int.repr (-1)).
rewrite <- Zodd_equiv in H.
set (init := divstep.init m x H).
assert (HfBound : forall i, -m < divstep.f (fst (divstep.stepN i init)) <= m).
1:{
  clear -H0 H1; intro i.
  injection (divstep.Trans.transN_step i init).
  intros _.
  destruct (divstep.Trans.bounded_transN i init) as [[Huv Huv'] _].
  nia.
}
assert (HgBound : forall i, -m < divstep.g (fst (divstep.stepN i init)) < m).
1:{
  clear -H0 H1; intro i.
  case (divstep.fgBoundsStrict init i);[cbn; lia|].
  intros _.
  change (divstep.f init) with m.
  change (divstep.g init) with x.
  lia.
}
set (invariant := fun P f => (EX i:nat, EX len:nat, EX d:Z, EX e:Z,
 PROP ( 0 <= Z.of_nat i < 12
      ; (1 <= len <= 5)%nat
      ; -2^(62 * Z.of_nat len + 1) <= divstep.f (fst (divstep.stepN (f i) init)) <= 2^(62 * Z.of_nat len + 1) - 1
      ; -2^(62 * Z.of_nat len + 1) <= divstep.g (fst (divstep.stepN (f i) init)) <= 2^(62 * Z.of_nat len + 1) - 1
      ; -2 * m < d < m
      ; -2 * m < e < m
      ; eqm m (x * d) (divstep.f (fst (divstep.stepN (f i) init)))
      ; eqm m (x * e) (divstep.g (fst (divstep.stepN (f i) init)))
      ; x = 0 -> d = 0
      ; P (divstep.g (fst (divstep.stepN (f i) init)))
      )
  LOCAL (temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.stepN (f i) init)))));
   temp _len (Vint (Int.repr (Z.of_nat len)));
   temp _i (Vint (Int.repr (Z.of_nat i)));
   lvar _t (Tstruct _secp256k1_modinv64_trans2x2 noattr) v_t;
   lvar _g (Tstruct _secp256k1_modinv64_signed62 noattr) v_g;
   lvar _f (Tstruct _secp256k1_modinv64_signed62 noattr) v_f;
   lvar _e (Tstruct _secp256k1_modinv64_signed62 noattr) v_e;
   lvar _d (Tstruct _secp256k1_modinv64_signed62 noattr) v_d;
   gvars gv; temp _x ptrx; temp _modinfo modinfo)
   SEP (
   data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.g (fst (divstep.stepN (f i) init))))) v_g;
   data_at (cs := CompSpecs) shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx;
   data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.f (fst (divstep.stepN (f i) init))))) v_f;
   data_at_ (cs := CompSpecs) Tsh (Tstruct _secp256k1_modinv64_trans2x2 noattr) v_t;
   data_at (cs := CompSpecs) Tsh (Tstruct _secp256k1_modinv64_signed62 noattr) (map Vlong (Signed62.reprn 5 e)) v_e;
   data_at (cs := CompSpecs) Tsh (Tstruct _secp256k1_modinv64_signed62 noattr) (map Vlong (Signed62.reprn 5 d)) v_d;
   data_at (cs := CompSpecs) sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
   debruijn64_array sh_debruijn gv;
   data_at (cs := CompSpecs) sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE))
)%assert).
forward_loop (invariant (fun g => True) (fun i => 62*i)%nat) break: (invariant (fun g => g = 0) (fun i => 62*(i + 1))%nat);
  unfold invariant in *; clear invariant.
* Exists 0%nat; Exists 5%nat; Exists 0; Exists 1.
  rewrite !Signed62.pad5 by (rewrite Signed62.reprn_length; reflexivity).
  simpl (divstep.stepN (62 * 0) init).
  simpl (divstep.g _).
  simpl (divstep.f _).
  entailer!!.
  split.
  - unfold eqm; rewrite Z.mod_same, Z.mul_0_r, Z.mod_0_l; lia.
  - apply eqm_refl.
* Intros i len d e.
  set (sti := (fst (divstep.stepN (62 * i) init))) in *.
  set (fi := divstep.f sti) in *.
  set (gi := divstep.g sti) in *.
  forward;rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia);[entailer!!|].
  forward;rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia);[entailer!!|].
  assert (Hi0 : forall z, Znth 0 (Signed62.reprn len z) = Int64.repr (if (len =? 1)%nat then z else z mod 2^62)).
  1:{
    intros z.
    destruct len;[lia|].
    destruct len.
    - rewrite Nat.eqb_refl.
      change (Znth 0 (Signed62.reprn 1 z)) with (last (Signed62.reprn 1 z) default).
      rewrite Signed62.reprn_last by lia.
      reflexivity.
    - replace (_ =? _)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      rewrite Signed62.reprn_Znth by lia.
      reflexivity.
  }
  rewrite !Hi0.
  set (fi0 := if (len =? 1)%nat then fi else fi mod 2^62).
  set (gi0 := if (len =? 1)%nat then gi else gi mod 2^62).
  assert (Hfi0Odd : Zodd fi0).
  1:{
   unfold fi0.
   destruct (len =? 1)%nat; try apply divstep.oddF.
   apply Zodd_bool_iff.
   rewrite <- Zbits.Ztestbit_base, <-Z.land_ones, Z.land_spec, Zbits.Ztestbit_base, andb_true_r by lia.
   apply Zodd_bool_iff.
   apply divstep.oddF.
  }
  set (stCall := {| divstep.delta := divstep.delta sti; divstep.f := _; divstep.g := gi0; divstep.oddF := Hfi0Odd |}).
  assert (etaStCall : -683 <= divstep.eta stCall < 683).
  1:{
    assert (etaInit : -(1) <= divstep.eta init < 1) by (cbn;lia).
    assert (etaBounds := divstep.etaBounds 1 (62*i) init etaInit).
    fold sti in etaBounds.
    change (divstep.eta stCall) with (divstep.eta sti).
    lia.
  }
  forward_call (stCall, v_t, Tsh, sh_debruijn, gv).
  assert (Hi0mod : forall z, eqm (2^62) (if (len =? 1)%nat then z else z mod 2^62) z).
  1:{
    intros z.
    destruct (_ =? _)%nat;[reflexivity|].
    unfold eqm.
    rewrite Z.mod_mod by lia.
    reflexivity.
  }
  unfold divstep.eta, divstep.Trans.transN.
  destruct (divstep.stepN_mod 62 stCall sti (Hi0mod fi) (Hi0mod gi) (eq_refl _)) as [-> ->].
  fold (divstep.Trans.transN 62 sti).
  fold (divstep.eta (fst (divstep.stepN 62 sti))).
  clear Hi0mod etaStCall stCall.
  forward.
  assert (HmOdd : Z.Odd m) by (apply Zodd_equiv; assumption).
  assert (HstiBounded := divstep.Trans.bounded_transN 62 sti).
  forward_call (d, e, divstep.Trans.transN 62 sti, m, v_d, v_e, v_t, modinfo, Tsh, Tsh, Tsh, sh_modinfo).
  destruct HstiBounded as [[Huv Huv'] [Hqr Hqr']].
  destruct (divstep.update_de_bound m d e (divstep.Trans.transN 62 sti)) as [Hdm Hem]; try assumption.
  set (d' := fst (divstep.update_de m d e (divstep.Trans.transN 62 sti))).
  set (e' := snd (divstep.update_de m d e (divstep.Trans.transN 62 sti))).
  assert (Hx0d'0 : x = 0 -> d' = 0).
  1:{
    intros Hx0.
    specialize (H13 Hx0).
    unfold d', sti, init.
    rewrite divstep.Trans.transHs.
    - rewrite H13.
      simpl.
      replace (_ + _) with (0) by ring.
      unfold divstep.pre_div62Modulo.
      rewrite Z.mul_0_r.
      reflexivity.
    - rewrite divstep.fixed_g;[|assumption].
      apply Z.divide_0_r.
  }
  clear H13.
  assert (HfiBound : -m < fi <= m) by apply HfBound.
  assert (HgiBound : -m < gi < m) by apply HgBound.
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (fi, len, m, -1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Gt in H13; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (fi, len, m, 1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      revert H13.
      elim Z.compare_spec; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (gi, len, m, -1, v_g, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Gt in H13; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (gi, len, m, 1, v_g, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Lt in H13; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_call (len, sti, v_f, v_g, v_t, Tsh, Tsh, Tsh).
  sep_apply (data_at_data_at_ Tsh t_secp256k1_modinv64_trans2x2).
  set (fi' := divstep.f (fst (divstep.stepN 62 sti))).
  set (gi' := divstep.g (fst (divstep.stepN 62 sti))).
  assert (Hfgi'Bound : 
    -2 ^ (62 * Z.of_nat len + 1) <= fi' <= 2 ^ (62 * Z.of_nat len + 1) - 1 /\
    -2 ^ (62 * Z.of_nat len + 1) <= gi' <= 2 ^ (62 * Z.of_nat len + 1) - 1).
  1:{
    unfold fi'.
    remember 62%nat as n62.
    injection (divstep.Trans.transN_step n62 sti).
    subst n62.
    destruct (divstep.Trans.bounded_transN 62 sti) as [[Hb1 Hb2] [Hb3 Hb4]].
    clear -Hb1 Hb2 Hb3 Hb4 H7 H8.
    nia.
  }
  destruct Hfgi'Bound as [Hfi'Bound Hgi'Bound].
  destruct (divstep.update_de_eqm m x d e sti) as [Hxd' Hxe']; try assumption.
  fold d' in Hxd'.
  fold e' in Hxe'.
  pose (sti' := fst (divstep.stepN (62 * (i + 1)) init)).
  unfold fi', gi' in *; clear fi' gi'.
  replace (fst (divstep.stepN 62 sti)) with sti' in * by
  (unfold sti';
   replace (62 * (i + 1))%nat with (62 + 62 * i)%nat by lia;
   apply divstep.stepN_app_fst).
  set (fi' := divstep.f sti') in *.
  set (gi' := divstep.g sti') in *.
  forward;
  rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
  [entailer!!|].
  drop_LOCALs [_t'1; _t'38; _t'37].
  forward_if (gi' <> 0).
  2:{
    forward.
    entailer!!.
    apply H13.
    rewrite H14.
    clear -len.
    destruct len as [|[|len]];reflexivity.
  }
  1:{
    forward.
    forward_for_simple_bound (Z.of_nat len)  (EX j:Z,
   PROP ( )
   LOCAL (temp _cond (Vlong (fold_left (fun x y => Int64.or x y) (firstn (Z.to_nat j) (Signed62.reprn len gi')) Int64.zero));
   temp _t'31 (Vlong (Znth 0 (Signed62.reprn len gi')));
   temp _eta (Vlong (Int64.repr (divstep.eta sti')));
   temp _len (Vint (Int.repr (Z.of_nat len)));
   temp _i (Vint (Int.repr (Z.of_nat i)));
   lvar _t (Tstruct _secp256k1_modinv64_trans2x2 noattr) v_t;
   lvar _g (Tstruct _secp256k1_modinv64_signed62 noattr) v_g;
   lvar _f (Tstruct _secp256k1_modinv64_signed62 noattr) v_f;
   lvar _e (Tstruct _secp256k1_modinv64_signed62 noattr) v_e;
   lvar _d (Tstruct _secp256k1_modinv64_signed62 noattr) v_d; 
   gvars gv; temp _x ptrx; temp _modinfo modinfo)
   SEP (data_at_ Tsh t_secp256k1_modinv64_trans2x2 v_t;
   data_at Tsh t_secp256k1_modinv64_signed62
     (Signed62.pad (Signed62.reprn len fi')) v_f;
   data_at Tsh t_secp256k1_modinv64_signed62
     (Signed62.pad (Signed62.reprn len gi')) v_g;
   data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d'))
     v_d;
   data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e'))
     v_e;
   data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
   debruijn64_array sh_debruijn gv;
   data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE);
   data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x))
     ptrx))%assert.
   + entailer!!.
     rewrite <-sublist_firstn, sublist_one, H13;[reflexivity|lia| |lia].
     rewrite Signed62.reprn_Zlength;lia.
   + forward;
     rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
     [entailer!!|].
     forward.
     entailer!!.
     rewrite <-Zfirstn_app by lia.
     rewrite (app_nil_end (firstn (Z.to_nat 1) _)), <-(Znth_cons Int64.zero) by (rewrite Signed62.reprn_Zlength;lia).
     rewrite fold_left_app.
     cbn.
     reflexivity.
   + rewrite Nat2Z.id, firstn_all2 by (rewrite Signed62.reprn_length;lia).
     rewrite fold_symmetric;intros;[|rewrite Int64.or_assoc|rewrite Int64.or_commut];try reflexivity.
     forward_if (gi' <> 0);[| |entailer!!].
     2:{
       forward;entailer!!.
       apply H14.
       rewrite H15.
       clear -len.
       induction len;[reflexivity|].
       destruct len;[reflexivity|].
       cbn in *.
       rewrite !Z.shiftr_0_l, !Zmod_0_l in *.
       rewrite IHlen.
       reflexivity.
     }
     forward.
     Exists i len d' e'.
     entailer!!.
     change (gi' = 0).
     assert (Hgi'0 : Forall (fun x => x = Int64.zero) (Signed62.reprn len gi')).
     1:{
       revert H14.
       clear H13.
       induction (Signed62.reprn len gi');[constructor|].
       cbn.
       intros H14.
       assert (Horzero : forall a b, Int64.or a b = Int64.zero -> a = Int64.zero).
       1:{
         clear -l.
         intros a b Hab.
         destruct (Int64.bits_size_1 a);[assumption|].
         assert (Hsize : 0 < Int64.size a).
         1:{
           destruct (Z_le_lt_dec 0 (Z.pred (Int64.size a))) as [Hle|Hlt];[lia|].
           assert (Hcontra := Int64.bits_below a _ Hlt).
           congruence.
         }
         apply (f_equal (fun x => Int64.testbit x (Z.pred (Int64.size a)))) in Hab.
         rewrite Int64.bits_zero, Int64.bits_or in Hab by (assert (Hrange := Int64.size_range a); lia). 
         apply orb_false_elim in Hab.
         destruct Hab;congruence.
       }
       constructor;[eapply Horzero; apply H14|].
       apply IHl.
       eapply Horzero; rewrite Int64.or_commut; apply H14.
     }
     rewrite <-(Signed62.signed_reprn gi' len);[|lia|assumption].
     clear -Hgi'0.
     induction (Signed62.reprn len gi');[reflexivity|].
     cbn.
     inversion_clear Hgi'0 as [|Ha Hl].
     rewrite H0, IHl;[reflexivity|assumption].
  }
  drop_LOCALs [_t'31].
  forward;
  rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
  [entailer!!|].
  replace (Z.of_nat len - 1) with (Zlength (Signed62.reprn len fi') - 1)
  by (rewrite Signed62.reprn_Zlength; reflexivity).
  rewrite Znth_last, Signed62.reprn_last by lia.
  forward;
  rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
  [entailer!!|].
  replace (Z.of_nat len - 1) with (Zlength (Signed62.reprn len gi') - 1) at 1
  by (rewrite Signed62.reprn_Zlength; reflexivity).
  rewrite Znth_last, Signed62.reprn_last by lia.
  progressC.
  replace (Z.shiftr (Z.of_nat len - 2) 63) with (if 2 <=? Z.of_nat len then 0 else -1).
  2:{
    rewrite Z.shiftr_div_pow2 by lia.
    elim Z.leb_spec; intros Hlen.
    + cut (0 <= (Z.of_nat len - 2) / 2 ^ 63 < 1);[lia|].
      apply div_bounds; lia.
    + cut (-1 <= (Z.of_nat len - 2) / 2 ^ 63 < 0);[lia|].
      apply div_bounds; lia.
  }
  do 2 forward.
  forward_if (EX len:nat,
   PROP (
     (1 <= len <= 5)%nat
   ; -2^(62 * Z.of_nat len + 1) <= divstep.f (fst (divstep.stepN (62 * (i + 1)) init)) <= 2^(62 * Z.of_nat len + 1) - 1
   ; -2^(62 * Z.of_nat len + 1) <= divstep.g (fst (divstep.stepN (62 * (i + 1)) init)) <= 2^(62 * Z.of_nat len + 1) - 1
   )
   LOCAL (
   temp _eta (Vlong (Int64.repr (divstep.eta sti')));
   temp _len (Vint (Int.repr (Z.of_nat len)));
   temp _i (Vint (Int.repr (Z.of_nat i)));
   lvar _t (Tstruct _secp256k1_modinv64_trans2x2 noattr) v_t;
   lvar _g (Tstruct _secp256k1_modinv64_signed62 noattr) v_g;
   lvar _f (Tstruct _secp256k1_modinv64_signed62 noattr) v_f;
   lvar _e (Tstruct _secp256k1_modinv64_signed62 noattr) v_e;
   lvar _d (Tstruct _secp256k1_modinv64_signed62 noattr) v_d; 
   gvars gv; temp _x ptrx; temp _modinfo modinfo)
   SEP (data_at_ Tsh t_secp256k1_modinv64_trans2x2 v_t;
   data_at Tsh t_secp256k1_modinv64_signed62
     (Signed62.pad (Signed62.reprn len fi')) v_f;
   data_at Tsh t_secp256k1_modinv64_signed62
     (Signed62.pad (Signed62.reprn len gi')) v_g;
   data_at Tsh t_secp256k1_modinv64_signed62
     (map Vlong (Signed62.reprn 5 d')) v_d;
   data_at Tsh t_secp256k1_modinv64_signed62
     (map Vlong (Signed62.reprn 5 e')) v_e;
   data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
   debruijn64_array sh_debruijn gv;
   data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE);
   data_at shx t_secp256k1_modinv64_signed62
     (map Vlong (Signed62.reprn 5 x)) ptrx))%assert;
   [|forward;Exists len;entailer!!|Intros len0].
   1:{
    assert (Hor0_l : forall x y, Int64.or x y = Int64.zero -> x = Int64.zero).
    1:{
      clear.
      intros x y Hxy.
      apply Int64.same_bits_eq.
      intros i Hi.
      apply (f_equal (fun x => Int64.testbit x i)) in Hxy.
      rewrite Int64.bits_or, Int64.bits_zero, orb_false_iff in Hxy by assumption.
      rewrite Int64.bits_zero.
      tauto.
    }
    assert (H14ab := Hor0_l _ _ H14).
    rewrite Int64.or_commut in H14.
    generalize (Hor0_l _ _ H14).
    clear H14.
    assert (H14a := Hor0_l _ _ H14ab).
    rewrite Int64.or_commut in H14ab.
    generalize (Hor0_l _ _ H14ab).
    clear H14ab.
    convert_C_to_math.
    assert (Hxor : forall x, -2^63 <= x < 2^63 -> Int64.repr (Z.lxor x (Z.shiftr (Int64.signed (Int64.repr x)) 63)) = Int64.zero -> -1 <= x <= 0).
    1:{
      clear.
      intros x Hx Hlxor.
      rewrite <- xor64_repr in Hlxor.
      apply Int64.xor_zero_equal in Hlxor.
      rewrite Int64.signed_repr in Hlxor by rep_lia.
      assert (Heq : x = Z.shiftr x 63).
      1:{
        rewrite <- (Int64.signed_repr (Z.shiftr x 63)) by solve_bounds.
        rewrite <- (Int64.signed_repr x) at 1 by solve_bounds.
        congruence.
      }
      rewrite Heq.
      solve_bounds.
    }
    intros Hfi'last Hgi'last.
    apply Hxor in Hfi'last, Hgi'last.
    2:{
      rewrite Z.mul_sub_distr_l, Z.shiftr_div_pow2 by lia.
      apply div_bounds;[lia|]. 
      clear -Hgi'Bound H5 H6.
      rewrite Z.mul_opp_r, <- Z.pow_add_r by lia.
      replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1) by ring.
      lia.
    }
    2:{
      rewrite Z.mul_sub_distr_l, Z.shiftr_div_pow2 by lia.
      apply div_bounds;[lia|]. 
      clear -Hfi'Bound H5 H6.
      rewrite Z.mul_opp_r, <- Z.pow_add_r by lia.
      replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1) by ring.
      lia.
    }
    revert H14a.
    elim Z.leb_spec;[|discriminate].
    intros Hlen2 _.
    set (fisign := Z.shiftr fi' (62 * (Z.of_nat len - 1))) in *.
    set (gisign := Z.shiftr gi' (62 * (Z.of_nat len - 1))) in *.
    forward;
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
    [entailer!!|forward].
    forward;
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
    [entailer!!|forward].
    rewrite !Int64_shl_shiftl, !Signed62.pad_upd_Znth by (rewrite Signed62.reprn_Zlength;lia).
    change (Int64.unsigned(Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
    rewrite !Int64.signed_repr by rep_lia.
    forward.
    rewrite sub_repr.
    Exists (len - 1)%nat.
    rewrite Nat2Z.inj_sub by lia.
    change (Z.of_nat 1) with 1.
    assert (Hfi'Bound' : -2 ^ (Z.of_nat (len - 1) * 62) <= fi' <
            2 ^ (Z.of_nat (len - 1) * 62)).
    1:{
      replace (Z.of_nat (len - 1) * 62) with (62 * (Z.of_nat len - 1)) by lia.
      destruct (Z.eq_dec fisign 0) as [Hfisign0|Hfisign0];
      [apply shiftr_small_iff in Hfisign0; lia|].
      destruct (Z.eq_dec fisign (-1)) as [Hfisign1|Hfisign1];[|lia].
      apply shiftr_small_neg_iff in Hfisign1; lia.
    }
    assert (Hgi'Bound' : -2 ^ (Z.of_nat (len - 1) * 62) <= gi' <
            2 ^ (Z.of_nat (len - 1) * 62)).
    1:{
      replace (Z.of_nat (len - 1) * 62) with (62 * (Z.of_nat len - 1)) by lia.
      destruct (Z.eq_dec gisign 0) as [Hgisign0|Hgisign0];
      [apply shiftr_small_iff in Hgisign0; lia|].
      destruct (Z.eq_dec gisign (-1)) as [Hgisign1|Hgisign1];[|lia].
      apply shiftr_small_neg_iff in Hgisign1; lia.
    }
    entailer!!.
    1:{
      replace (62 * (Z.of_nat len - 1) + 1) with (Z.of_nat (len - 1) * 62 + 1) by lia.
      rewrite Z.pow_add_r by lia.
      fold sti' fi' gi'.
      lia.
    }
    assert (Hsign : forall x n, -1 <= Z.shiftr x n <= 0 -> Z.shiftr x n = if 0 <=? x then 0 else -1).
    1:{
      clear.
      intros x n Hx.
      elim Z.leb_spec; intros Hx0.
      + apply (Z.shiftr_nonneg _ n) in Hx0; lia.
      + apply (Z.shiftr_neg _ n) in Hx0; lia.
    }
    unfold fisign, gisign.
    rewrite !Hsign by assumption.
    cut (forall v x, -2 ^ (Z.of_nat (len - 1) * 62) <= x <= 2 ^ (Z.of_nat (len - 1) * 62) - 1 -> data_at Tsh t_secp256k1_modinv64_signed62
  (Signed62.pad
     (upd_Znth (Z.of_nat len - 2) (Signed62.reprn len x)
        (Int64.or (Znth (Z.of_nat len - 2) (Signed62.reprn len x))
           (Int64.repr (Z.shiftl (if 0 <=? x then 0 else -1) 62))))) v
|-- data_at Tsh t_secp256k1_modinv64_signed62
      (Signed62.pad (Signed62.reprn (len - 1) x)) v).
    intro K.
    apply sepcon_derives;apply K;lia.
    intros v h Hh.
    unfold Signed62.pad at 2.
    do 2 unfold_data_at (data_at _ _ _ v).
    rewrite !field_at_data_at.
    simpl (nested_field_type t_secp256k1_modinv64_signed62 (DOT _v)).
    rewrite (split2_data_at_Tarray_app (Z.of_nat len - 1));rewrite ?Signed62.reprn_length;[
    |rewrite Zlength_map, Signed62.reprn_Zlength; lia
    |rewrite Zlength_repeat'; lia
    ].
    rewrite <-(data_at__tarray' _ tlong _ (repeat Vundef (5 - (len - 1)))) by
     (replace (5 - (len - 1))%nat with (Z.to_nat (5 - (Z.of_nat len - 1))) by lia;apply repeat_Zrepeat).
    sep_apply (split2_data_at_Tarray_unfold Tsh tlong 5 (Z.of_nat len - 1));[lia|].
    entailer!!.
    unfold Signed62.pad.
    rewrite sublist0_app1, sublist_map, sublist_firstn by (rewrite Zlength_map, Zlength_upd_Znth, Signed62.reprn_Zlength;lia).
    replace (Z.to_nat (Z.of_nat len - 1)) with (len - 1)%nat by lia.
    replace (Z.of_nat len - 2) with ((Z.of_nat (len - 1)) - 1) by lia.
    rewrite Signed62.reprn_shrink;[entailer!!| |lia].
    unfold Signed62.min_signed, Signed62.max_signed.
    lia.
  }
  clear Hgi'Bound Hfi'Bound Hfi0Odd gi0 fi0 Hi0 H8 H7 H6 H5 len.
  rename len0 into len.
  assert(Hi0 : (i <> 11)%nat).
  1:{
    intros ->.
    apply H13.
    unfold gi', sti', init.
    rewrite (divstep.stepN_app_fst 20 724).
    apply divstep.fixed_g.
    rewrite divstep.Translate_divsteps_g.
    apply (processDivstep_correct _ 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2); try lia;[assumption|].
    apply example724.
  }
  match goal with
  | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
    let Q' := remove_LOCAL2 [temp _i (Vint (Int.repr (Z.of_nat i)))] Q in
    forward_loop (PROPx (P) (LOCALx Q R))
    break:(PROPx (P) (LOCALx (temp _i (Vint (Int.repr (Z.of_nat i + 1)))::Q') R))
  end;[entailer!!| |].
  1:{
    forward.
    rewrite add_repr.
    forward.
    forward_if True;[exfalso|forward;entailer!!|forward;entailer!!].
    revert H5.
    convert_C_to_math.
    case Z.ltb_spec;[discriminate|lia].
  }
  assert (Hfi'Bound : -m < fi' <= m) by apply HfBound.
  assert (Hgi'Bound : -m < gi' < m) by apply HgBound.
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (fi', len, m, -1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Gt in H5; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (fi', len, m, 1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      revert H5.
      elim Z.compare_spec; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (gi', len, m, -1, v_g, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Gt in H5; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  forward_verify_check.
  1:{
    unfold make_modinfo.
    forward_call (gi', len, m, 1, v_g, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
    [rewrite field_address_offset by assumption;entailer!
    |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
    forward_if.
    1:{
      rewrite Zaux.Zcompare_Lt in H5; try discriminate.
      lia.
    }
    forward;unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!.
  }
  Exists (i+1)%nat; Exists len; Exists d'; Exists e'.
  entailer!!.
  do 2 f_equal.
  lia.
* Intros i len d e.
  rename H13 into Hx0d0.
  rename H14 into H13.
  set (sti := (fst (divstep.stepN (62 * (i + 1)) init))) in *.
  set (fi := divstep.f sti) in *.
  set (gi := divstep.g sti) in *.
  forward_verify_check.
  1:{
    forward_call (gi, len, 1, 0, v_g, gv _SECP256K1_SIGNED62_ONE, Tsh, sh_SECP256K1_SIGNED62_ONE).
    rewrite H13 at 1.
   forward_if;[discriminate|].
   forward.
   entailer!!.
  }
  assert (Hverify : (Z.abs fi = 1) \/ (x = 0 /\ fi = m)).
  1:{
    destruct (Z.eq_dec x 0) as [Hx0|Hx0];[right|left].
    - split;[assumption|].
      specialize (HfBound (62 * (i + 1))%nat).
      fold sti fi in HfBound.
      cut (m = Z.abs fi);[lia|].
      etransitivity;[|apply Z.gcd_0_r].
      symmetry.
      apply Zis_gcd_gcd;[lia|].
      rewrite <- H13.
      apply divstep.gcd.
      subst x.
      apply Zis_gcd_0.
    - rewrite <- Z.gcd_0_r.
      apply Zis_gcd_gcd;[lia|].
      rewrite <- H13.
      apply divstep.gcd.
      apply Zis_gcd_sym.
      destruct H2 as [H2|H2];[lia|].
      apply H2.
  }
  forward_verify_check.
  1:{
    forward_call (fi, len, 1, -1, v_f, gv _SECP256K1_SIGNED62_ONE, Tsh, sh_SECP256K1_SIGNED62_ONE).
    forward_if (temp _t'13 (Vint (Int.repr (Z.b2z (Z.abs fi =? 1))))).
    1:{
      forward.
      destruct (Z.eq_dec fi (-1)) as [->|Hne];[entailer!!|].
      revert H14.
      elim Zaux.Zcompare_spec;try discriminate.
      lia.
    }
    1:{
      forward_call (fi, len, 1, 1, v_f, gv _SECP256K1_SIGNED62_ONE, Tsh, sh_SECP256K1_SIGNED62_ONE).
      forward.
      entailer!!.
      assert (Hfi1 : fi <> -1) by (revert H14;elim Zaux.Zcompare_spec;try contradiction;lia).
      elim Z.eqb_spec;intros Habsfi.
      - replace fi with 1 by lia.
        reflexivity.
      - elim Zaux.Zcompare_spec;try reflexivity.
        lia.
    }
    forward_if (temp _t'15 (Vint (Int.repr (Z.b2z ((Z.abs fi =? 1) || (x =? 0) && (d =? 0) && (Z.abs fi =? m)))))).
    1:{
      forward.
      entailer!!.
      rewrite H14.
      reflexivity.
    }
    1:{
      forward_call (x, 5%nat, 1, 0, ptrx, gv _SECP256K1_SIGNED62_ONE, shx, sh_SECP256K1_SIGNED62_ONE).
      forward_if (temp _t'17 (Vint (Int.repr (Z.b2z ((x =? 0) && (d =? 0)))))).
      2:{
        forward.
        entailer!!.
        elim Z.eqb_spec; try reflexivity.
        intros ->.
        contradiction.
      }
      1:{
        forward_call (d, 5%nat, 1, 0, v_d, gv _SECP256K1_SIGNED62_ONE, Tsh, sh_SECP256K1_SIGNED62_ONE).
        forward.
        entailer!!.
        elim (Z.eqb_spec d).
        2:{
          rewrite andb_false_r; simpl.
          elim Zaux.Zcompare_spec;try reflexivity; lia.
        }
        revert H15.
        elim Zaux.Zcompare_spec;try discriminate.
        intros -> _ ->.
        reflexivity.
      }
      forward_if.
      2:{
        forward.
        entailer!!.
      }
      unfold make_modinfo.
      forward_call (fi, len, m, 1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
      [rewrite field_address_offset by assumption;entailer!
      |unfold_data_at (data_at _ _ _ modinfo);entailer!|].
      forward_if.
      1:{
        fastforward.
        entailer!!;[|
          unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!].
        revert H16.
        elim Zaux.Zcompare_spec;try discriminate.
        rewrite H14, H15.
        intros -> _.
        replace (Z.abs (m * 1)) with m by lia.
        rewrite Z.eqb_refl.
        reflexivity.
      }
      forward_call (fi, len, m, -1, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo, Tsh, sh_modinfo);
      [rewrite field_address_offset by assumption;entailer!|].
      fastforward.
      entailer!!;[|
        unfold_data_at (data_at _ t_secp256k1_modinv64_modinfo _ modinfo);entailer!].
      assert (Hfim : fi <> m).
      1:{
        revert H16.
        elim Zaux.Zcompare_spec;try contradiction;lia.
      }
      rewrite H14, H15.
      simpl.
      elim Z.eqb_spec;elim Zaux.Zcompare_spec;try lia; reflexivity.
   }
   forward_if;[|forward;entailer!!].
   exfalso.
   destruct Hverify as [Hverify|[Hx0 Hverify]].
   - rewrite Hverify, Z.eqb_refl in H14 by reflexivity;discriminate.
   - subst x.
     rewrite orb_comm, Hverify in H14.
     replace (Z.abs m) with m in H14 by lia.
     rewrite Hx0d0, !Z.eqb_refl in H14 by reflexivity.
     discriminate.
  }
  forward;
  rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength;lia);
  [entailer!!|].
  rewrite <- (Signed62.reprn_Zlength len fi), Znth_last, Signed62.reprn_last at 1 by lia.
  forward_call.
  assert (Hfibound : 2 ^ (62 * (Z.of_nat len - 1)) * -2 ^ 63 <= fi <=
    2 ^ (62 * (Z.of_nat len - 1)) * (2 ^ 63 - 1 + 1) - 1).
  1:{
    rewrite Z.sub_add, Z.mul_opp_r, <-Z.pow_add_r, Z.mul_sub_distr_l by lia.
    replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1);lia.
  }
  rewrite Int64.signed_repr by solve_bounds.
  replace (_<?0) with (fi<?0).
  2:{
   do 2 elim Z.ltb_spec0; try reflexivity.
   - intros Hcontra Hfi0; elim Hcontra.
     rewrite Z.shiftr_neg; assumption.
   - intros Hshift Hcontra; elim Hcontra.
     rewrite Z.shiftr_neg in Hshift; assumption.
  }
  replace ((if fi <? 0 then -d else d) mod m) with (modInv x m).
  2:{
    symmetry.
    destruct Hverify as [Habsfi|[Hx0 _]].
    2:{
      rewrite Hx0d0, Hx0, modInv_zero by assumption.
      destruct (fi <? 0); reflexivity.
    }
    apply modInv_mul_unique_r.
    replace ((if fi <? 0 then -d else d)) with (d*Z.sgn fi) by (elim (Z.ltb_spec);lia).
    rewrite Z.mul_assoc, <-Zmult_mod_idemp_l, H11, Zmult_mod_idemp_l, Z.sgn_abs, Habsfi, Z.mod_1_l; lia.
  }
  sep_apply (data_at_data_at_ shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx).
  forward_call.
  entailer!!.
Qed.
