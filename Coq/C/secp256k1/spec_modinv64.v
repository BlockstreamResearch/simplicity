Require Import VST.floyd.proofauto.
Require Import jets_secp256k1.
Require Import Coq.Logic.Eqdep_dec.

Require Import progressC.
Require Import extraMath.
Require Import modinv.
Require divstep.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Opaque Z.shiftr Z.pow.

Definition t_secp256k1_modinv64_signed62 := Tstruct _secp256k1_modinv64_signed62 noattr.
Definition t_secp256k1_modinv64_modinfo := Tstruct _secp256k1_modinv64_modinfo noattr.

Module Signed62.

Definition max_signed n : Z := 2^(n*62)-1.
Definition min_signed n : Z := -2^(n*62).

Fixpoint signed (l : list int64) : Z :=
match l with
| [] => 0
| (a :: l') => Int64.signed a + 2^62 * signed l'
end.

Lemma app_signed l1 l2 : signed (l1 ++ l2) = signed l1 + 2^(Zlength l1 * 62) * signed l2.
Proof.
revert l2.
induction l1; intros l2.
* rewrite Z.pow_0_r. cbn. ring.
* rewrite Zlength_cons.
  cbn.
  assert (Hlen := Zlength_nonneg l1).
  rewrite IHl1, Z.mul_succ_l, Z.pow_add_r; lia.
Qed.

Fixpoint reprn (n : nat) (a : Z) : list int64 :=
match n with
| 0%nat => []
| 1%nat => [Int64.repr a]
| (S n0) => Int64.repr (a mod (2 ^ 62)) :: (reprn n0 (Z.shiftr a 62))
end.

Lemma reprn_length n : forall a, length (reprn n a) = n.
Proof.
induction n;try reflexivity.
destruct n;try reflexivity.
intro a; simpl in *; rewrite IHn; reflexivity.
Qed.

Lemma reprn_Zlength n : forall a, Zlength (reprn n a) = Z.of_nat n.
Proof.
intros a.
rewrite Zlength_correct, Signed62.reprn_length; reflexivity.
Qed.

Lemma reprn_succ n a : reprn (S n) a = 
  reprn n (a mod 2 ^ (62 * Z.of_nat n)) ++ [Int64.repr (Z.shiftr a (62 * Z.of_nat n))].
Proof.
revert a; induction n; intros a;[reflexivity|].
pattern (S n).
simpl (reprn (S _) a).
cbn beta.
rewrite IHn, Z.shiftr_shiftr, Nat2Z.inj_succ, Z.mul_succ_r, Z.add_comm by lia.
simpl.
destruct n;[reflexivity|].
rewrite Z.pow_add_r by lia.
rewrite <- Zmod_div_mod, !(Z.shiftr_div_pow2 _ 62) by (try lia; auto with *).
rewrite (Z.mul_comm _ (2^62)), Zaux.Zdiv_mod_mult by lia.
reflexivity.
Qed.

Lemma reprn_last : forall a n d, (1 <= n)%nat ->
  last (reprn n a) d = Int64.repr (Z.shiftr a (62 * (Z.of_nat n - 1))).
Proof.
intros a n.
revert a.
induction n;[lia|].
intros a d Hn.
rewrite Nat2Z.inj_succ.
unfold Z.succ.
replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) by ring.
rewrite reprn_succ.
apply last_last.
Qed.

Lemma reprn_nth : forall a n i d, (0 <= i < n - 1)%nat ->
  nth i (reprn n a) d = Int64.repr ((Z.shiftr a (62 * (Z.of_nat i))) mod (2^62)).
Proof.
intros a n.
revert a.
induction n;[intros; lia|].
intros a i d Hi.
rewrite reprn_succ.
rewrite app_nth1 by (rewrite reprn_length; lia).
destruct (Nat.lt_ge_cases i (n - 1)).
+ rewrite IHn, !Z.shiftr_div_pow2, <- (Nat.sub_add i n), Nat2Z.inj_add,
          Z.mul_add_distr_l, Z.pow_add_r, Z.mul_comm, Zaux.Zdiv_mod_mult by lia.
  rewrite !Z.pow_mul_r, <- Zmod_div_mod; try reflexivity; try lia.
  apply Zpow_facts.Zpower_divide.
  lia.
+ set (l := (reprn n _)).
  replace i with (n - 1)%nat by lia.
  replace n with (length l) at 1 by apply reprn_length.
  unfold l.
  rewrite nth_last, reprn_last by lia.
  replace (62 * Z.of_nat n) with (62 * (Z.of_nat n - 1) + 62) by ring.
  rewrite Z.pow_add_r, !Z.shiftr_div_pow2, Zaux.Zdiv_mod_mult by lia.
  repeat f_equal.
  lia.
Qed.

Lemma reprn_Znth : forall a n i, 0 <= i < Z.of_nat n - 1 ->
  Znth i (reprn n a) = Int64.repr ((Z.shiftr a (62 * i)) mod (2^62)).
Proof.
intros a n i Hi.
rewrite <- nth_Znth by (rewrite reprn_Zlength; lia).
rewrite reprn_nth, Z2Nat.id by lia.
reflexivity.
Qed.

Lemma signed_firstn_reprn a i n : (i < n)%nat -> signed (firstn i (reprn n a)) = a mod (2^(62*Z.of_nat i)).
Proof.
revert a i.
induction n;[lia|].
intros a [|i];[simpl; rewrite Z.pow_0_r, Zmod_1_r; reflexivity|].
intros Hi.
apply Nat.succ_lt_mono in Hi.
destruct n;[lia|].
rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
simpl.
change (signed _) with (signed (firstn i (reprn (S n) (Z.shiftr a 62)))).
rewrite IHn by assumption.
rewrite Int64.signed_repr by solve_bounds.
rewrite Z.shiftr_div_pow2 by lia.
symmetry.
rewrite Zmod_recombine by lia.
ring.
Qed.

Lemma signed_reprn a n : (1 <= n)%nat -> -2 ^ (62 * Z.of_nat n + 1) <= a <= 2 ^ (62 * Z.of_nat n + 1) - 1 ->
 signed (reprn n a) = a.
Proof.
revert a.
induction n;[lia|].
intros a _.
rewrite Nat2Z.inj_succ, Z.mul_succ_r.
destruct n.
* simpl. intros Ha. rewrite Int64.signed_repr;[lia|assumption].
* change (reprn _ a) with (Int64.repr (a mod (2 ^ 62)) :: (reprn (S n) (Z.shiftr a 62))).
  cbn [signed].
  rewrite !Z.pow_add_r in * by lia.
  intros Ha.
  rewrite IHn by solve_bounds.
  rewrite Int64.signed_repr by solve_bounds.
  rewrite Z.shiftr_div_pow2, Z.add_comm by lia.
  symmetry.
  apply Z_div_mod_eq_full.
Qed.

Lemma reprn_shrink a n1 n2 : (min_signed (Z.of_nat n1) <= a <= max_signed (Z.of_nat n1)) -> (1 <= n1 < n2)%nat -> 
     (firstn n1
        (upd_Znth (Z.of_nat n1 - 1) (reprn n2 a)
           (Int64.or (Znth (Z.of_nat n1 - 1) (reprn n2 a))
              (Int64.repr (Z.shiftl (if 0 <=? a then 0 else -1) 62))))) =
     (reprn n1 a).
Proof.
intros Ha Hn.
apply (nth_eq_ext _ default);
  rewrite firstn_length, <-ZtoNat_Zlength, Zlength_upd_Znth, ZtoNat_Zlength, !reprn_length;
[lia|].
replace (Init.Nat.min n1 n2) with n1 by lia.
intros i Hi.
rewrite nth_firstn by lia.
destruct (Nat.eq_dec i (n1 - 1)) as [->|Hneq];rewrite nth_Znth';
[|rewrite reprn_nth, Znth_upd_Znth_diff, reprn_Znth by lia; reflexivity].
replace (Z.of_nat (n1 - 1)) with (Z.of_nat n1 - 1) by lia.
rewrite upd_Znth_same by (rewrite reprn_Zlength; lia).
rewrite reprn_Znth by lia.
symmetry.
replace n1 with (length (reprn n1 a)) at 1 by (rewrite reprn_length;reflexivity).
rewrite nth_last.
rewrite reprn_last by lia.
unfold min_signed, max_signed in Ha.
elim Z.leb_spec;intros Ha0.
+ rewrite Int64.or_zero.
  symmetry.
  f_equal.
  apply Z.mod_small.
  apply shiftr_bounds.
  rewrite <-Z.pow_add_r by lia.
  replace (62 * (Z.of_nat n1 - 1) + 62) with (Z.of_nat n1 * 62) by lia.
  lia.
+ rewrite <- Int64.add_is_or.
  2:{
    apply Int64.same_bits_eq.
    intros j Hj.
    rewrite Int64.bits_zero, and64_repr, Int64.testbit_repr by assumption.
    rewrite <- Z.land_ones, !Z.land_spec, Z.testbit_ones_nonneg, Z.shiftl_spec by lia.
    elim Z.ltb_spec;[|rewrite andb_false_r;reflexivity].
    intro; rewrite (Z.testbit_neg_r _ (j - 62)), !andb_false_r by lia; reflexivity.
  }
  rewrite add64_repr.
  f_equal.
  change (Z.shiftl (-1) 62) with (-2^62).
  rewrite <- (Z_mod_plus_full _ 1), Z.mod_small;[ring|].
  rewrite strict_bounds.
  apply unadd_bounds_small.
  setoid_rewrite <- strict_bounds'.
  apply shiftr_bounds.
  rewrite Z.mul_0_r.
  cut (-(2^62 * 2 ^ (62 * (Z.of_nat n1 - 1))) <= a < 0);[lia|].
  rewrite <-Z.pow_add_r by lia.
  replace (62 + 62 * (Z.of_nat n1 - 1)) with (Z.of_nat n1 * 62); lia.
Qed.

Definition pad (l : list int64) : list val := map Vlong l ++ repeat Vundef (5 - length l).

Lemma pad_nth i (l : list int64) : 0 <= i < Zlength l -> Znth i (pad l) = Vlong (Znth i l).
Proof.
intros Hi.
rewrite <- !nth_Znth; try auto.
* assert (Z.to_nat i < length l)%nat by (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia).
  unfold pad.
  rewrite app_nth1 by (rewrite map_length; assumption).
  erewrite nth_indep by (rewrite map_length; assumption).
  apply map_nth.
* unfold pad.
  rewrite Zlength_app, Zlength_map.
  assert (Hlen := Zlength_nonneg (repeat Vundef (5 - Datatypes.length l))).
  lia.
Qed.

Lemma pad_nth_undef i (l : list int64) : Zlength l <= i -> Znth i (pad l) = Vundef.
Proof.
intros Hi.
pose (Hl := Zlength_nonneg l).
rewrite <- (Z2Nat.id i), <- nth_Znth' by lia.
rewrite Z2Nat.inj_le, ZtoNat_Zlength in Hi by lia.
unfold pad.
rewrite app_nth2 by (rewrite map_length; lia).
apply nth_repeat.
Qed.

Lemma pad_length l : (length l <= 5)%nat -> length (pad l) = 5%nat.
Proof.
intros Hl.
unfold pad.
rewrite app_length, map_length, repeat_length.
lia.
Qed.

Lemma pad_Zlength l : Zlength l <= 5 -> Zlength (pad l) = 5.
Proof.
intros Hl.
rewrite Zlength_correct, pad_length in *; try lia.
Qed.

Lemma pad0 : pad nil = repeat Vundef 5.
Proof.
reflexivity.
Qed.

Lemma pad5 l : length l = 5%nat -> pad l = map Vlong l.
Proof.
unfold pad.
intros ->.
cbn.
rewrite app_nil_end.
reflexivity.
Qed.


Lemma pad_upd_Znth a i l : 0 <= i < Zlength l -> upd_Znth i (pad l) (Vlong a) = pad (upd_Znth i l a).
Proof.
intros Hi.
unfold pad.
rewrite upd_Znth_app1 by (rewrite Zlength_map; assumption).
f_equal.
* apply upd_Znth_map.
* rewrite <- (ZtoNat_Zlength (upd_Znth _ _ _)), Zlength_upd_Znth, ZtoNat_Zlength.
  reflexivity.
Qed.

Lemma pad_upd_Znth_end a l : (length l <= 4)%nat -> upd_Znth (Zlength l) (pad l) (Vlong a) = pad (l++[a]).
Proof.
intros Hl.
rewrite <- ZtoNat_Zlength in Hl.
(* assert (Hl' : Zlength l <= 4) by lia. *)
apply (nth_ext _ _ default default).
* apply Nat2Z.inj.
  rewrite <- !Zlength_correct, Zlength_upd_Znth, !pad_Zlength; simpl; try lia.
  rewrite Zlength_app, Zlength_cons; simpl; lia.  
* intros n Hn.
  rewrite !nth_Znth'.
  pose (Hpad := pad_Zlength l).
  destruct (Z.lt_total (Z.of_nat n) (Zlength l)) as [Hnl|[Hnl|Hnl]].
  + rewrite Znth_upd_Znth_diff, pad_nth by lia.
    rewrite pad_nth by (rewrite Zlength_app, Zlength_cons; simpl; lia).
    rewrite Znth_app1 by lia.
    reflexivity.
  + rewrite Znth_upd_Znth_same by lia.
    unfold pad.
    rewrite map_app, Znth_app1, Znth_app2, Zlength_map, Hnl, Z.sub_diag by
      (rewrite ?Zlength_app, !Zlength_map, ?Zlength_cons; simpl; lia).
    reflexivity.
  + rewrite Znth_upd_Znth_diff, pad_nth_undef by lia.
    rewrite pad_nth_undef by (rewrite Zlength_app, Zlength_cons; simpl; lia).
    reflexivity.
Qed.

End Signed62.

Definition make_modinfo (m : Z) : (list val * val)%type :=
  (map Vlong (Signed62.reprn 5 m), Vlong (Int64.repr (modInv m (2^62)))).

Definition debruijn64_array (sh: share) (gv: globals) : mpred :=
  Eval cbn in
  let
    is_all_init_int8 := fix is_all_init_int8 (l : list init_data) :=
      match l with
      | [] => True
      | Init_int8 _ :: l' => is_all_init_int8 l'
      | _ => False
      end
  in let
    uninit_int8s := fix uninit_int8s (l: list init_data) :
        is_all_init_int8 l -> list int :=
      match l with
      | [] => fun _ => []
      | x :: l' =>
        match x with
        | Init_int8 i => fun pf => i :: uninit_int8s l' pf
        | _ => False_rec (list int)
        end
      end
  in data_at sh (gvar_info v_debruijn)
    (map Vint (uninit_int8s (gvar_init v_debruijn) I)) (gv _debruijn).

Lemma data_at_tulong_tlong {cs: compspecs}: forall sh v p, data_at sh tulong v p = data_at sh tlong v p.
Proof.
  intros.
  unfold data_at, field_at.
  f_equal.
  unfold field_compatible.
  apply ND_prop_ext.
  assert (align_compatible tulong p <-> align_compatible tlong p); [| tauto].
  destruct p; simpl; try tauto.
  split; intros.
  + eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
    eapply align_compatible_rec_by_value; [reflexivity |].
    auto.
  + eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
    eapply align_compatible_rec_by_value; [reflexivity |].
    auto.
Qed.

Lemma SECP256K1_SIGNED62_ONE_global gv : headptr (gv _SECP256K1_SIGNED62_ONE) ->
   globvar2pred gv (_SECP256K1_SIGNED62_ONE, v_SECP256K1_SIGNED62_ONE) |--
   data_at Ers t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE).
Proof.
intros Hheadptr.
unfold globvar2pred.
simpl.
rewrite sepcon_emp.
change (Z.shiftr 1 _) with 0.
repeat change (Z.shiftr 0 _) with 0.
change (1 mod _) with 1.
change (0 mod _) with 0.
unfold t_secp256k1_modinv64_signed62.
assert (Hptr : isptr (gv _SECP256K1_SIGNED62_ONE)) by (apply headptr_isptr; assumption).

unfold data_at.
erewrite field_at_Tstruct;
[|reflexivity|apply JMeq_refl].
simpl (co_members (get_co _secp256k1_modinv64_signed62)).
cbn -[mapsto].
change (0 + _) with 40.
unfold withspacer.
destruct (Z.eq_dec _ _);[clear e|lia].
rewrite field_at_data_at.
assert (Hcompat : field_compatible
          (Tstruct _secp256k1_modinv64_signed62 noattr)
          (DOT _v) (gv _SECP256K1_SIGNED62_ONE)).
1:{
  apply headptr_field_compatible.
  - assumption.
  - reflexivity.
  - repeat constructor.
  - reflexivity.
  - eapply align_compatible_rec_Tstruct.
    + reflexivity.
    + reflexivity.
    + simpl; intros i0 t0 z0 H0 H1.
      destruct (ident_eq _ _) in H0;[|discriminate].
      injection H0; clear H0.
      intros <-.
      subst i0.
      injection H1; clear H1.
      intros <-.
      eapply align_compatible_rec_Tarray.
      * intros i Hi.
        cut (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4);[|lia].
        clear Hi.
        intros [->|[->|[->|[->| ->]]]];econstructor;try reflexivity;apply Zmod_divide;try reflexivity;cbn;lia.
}
rewrite field_address_offset by assumption.
rewrite isptr_offset_val_zero by (apply headptr_isptr; assumption).
simpl (nested_field_type _ _).

unfold tarray.
  rewrite (split2_data_at_Tarray _ tlong _ 1 _
   [Vlong (Int64.repr 1); Vlong (Int64.repr 0);
       Vlong (Int64.repr 0); Vlong (Int64.repr 0);
       Vlong (Int64.repr 0)]
   [Vlong (Int64.repr 1)] [Vlong (Int64.repr 0);
       Vlong (Int64.repr 0); Vlong (Int64.repr 0);
       Vlong (Int64.repr 0)]); try solve[cbn;lia]; try reflexivity.
  apply sepcon_derives.
  -  eapply derives_trans;[|apply data_at_singleton_array];[|reflexivity].
     rewrite <-data_at_tulong_tlong.
     erewrite mapsto_data_at'; try reflexivity; try apply JMeq_refl;try entailer.
  apply headptr_field_compatible.
  + assumption.
  + reflexivity.
  + repeat constructor.
  + reflexivity.
  + econstructor;[reflexivity|apply Z.divide_0_r].
  - clear Hcompat.
      assert (Hcompat : field_compatible (tarray tlong 5) [] (gv _SECP256K1_SIGNED62_ONE)).
      1:{
        apply headptr_field_compatible.
  - assumption.
  - reflexivity.
  - repeat constructor.
  - reflexivity.
  - eapply align_compatible_rec_Tarray.
      * intros i Hi.
        cut (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4);[|lia].
        clear Hi.
        intros [->|[->|[->|[->| ->]]]];econstructor;try reflexivity;apply Zmod_divide;try reflexivity;cbn;lia.
       }
    eapply derives_trans;[apply (mapsto_zero_data_at_zero (Tarray tlong (5 - 1) noattr))|].
    + apply readable_Ers.
    + reflexivity.
    + reflexivity.
    + apply (field_compatible0_nested_field_array (Tarray tlong 5 noattr) []); try lia; apply arr_field_compatible0; try lia; assumption.
    + rewrite field_address0_offset by
       (eapply field_compatible0_cons_Tarray;[reflexivity|assumption|lia]).
      change (nested_field_offset (Tarray tlong 5 noattr) (SUB 1)) with 8.
      fold (tarray tlong (5 - 1)).
      rewrite zero_val_tarray, zero_val_tlong.
      apply derives_refl.
Qed.

Definition secp256k1_modinv64_signed62_assign_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_signed62_assign
  WITH x : Z, ptr_dst : val, ptr_src : val, sh_dst : share, sh_src : share
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_signed62
      ]
    PROP( writable_share sh_dst
        ; readable_share sh_src
        )
    PARAMS(ptr_dst; ptr_src)
    SEP( data_at_ sh_dst t_secp256k1_modinv64_signed62 ptr_dst
       ; data_at sh_src t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptr_src
       )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP( data_at sh_dst t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptr_dst
       ; data_at sh_src t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptr_src
       ).

Definition secp256k1_modinv64_var_spec : ident * funspec :=
DECLARE _secp256k1_modinv64_var
  WITH x : Z, m : Z, ptrx : val, modinfo : val, shx : share, sh_modinfo : share,
       sh_debruijn : share, sh_SECP256K1_SIGNED62_ONE : share, gv : globals
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_modinfo
      ]
    PROP( Z.Odd m
        ; 0 <= x < m
        ; 1 < m < 2^256
        ; x = 0 \/ rel_prime x m
        ; writable_share shx
        ; readable_share sh_modinfo
        ; readable_share sh_debruijn
        ; readable_share sh_SECP256K1_SIGNED62_ONE
        )
    PARAMS(ptrx; modinfo)
    GLOBALS(gv)
    SEP(data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx;
        data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
        debruijn64_array sh_debruijn gv;
        data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE))
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (modInv x m))) ptrx;
        data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
        debruijn64_array sh_debruijn gv;
        data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE)).

Definition secp256k1_modinv64_var_spec_prime : ident * funspec :=
DECLARE _secp256k1_modinv64_var
  WITH x : Z, m : Z, ptrx : val, modinfo : val, shx : share, sh_modinfo : share,
       sh_debruijn : share, sh_SECP256K1_SIGNED62_ONE : share, gv : globals
  PRE [ tptr t_secp256k1_modinv64_signed62
      , tptr t_secp256k1_modinv64_modinfo
      ]
    PROP( Z.Odd m
        ; 0 <= x < m
        ; m < 2^256
        ; prime m
        ; writable_share shx
        ; readable_share sh_modinfo
        ; readable_share sh_debruijn
        ; readable_share sh_SECP256K1_SIGNED62_ONE
        )
    PARAMS(ptrx; modinfo)
    GLOBALS(gv)
    SEP(data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx;
        data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
        debruijn64_array sh_debruijn gv;
        data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE))
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (modInv x m))) ptrx;
        data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
        debruijn64_array sh_debruijn gv;
        data_at sh_SECP256K1_SIGNED62_ONE t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 1)) (gv _SECP256K1_SIGNED62_ONE)).

(* Use with
   forward_call secp256k1_modinv64_var_spec_prime_sub (x, m, ptrx, modinfo, shx, sh_modinfo, sh_debruijn, sh_SECP256K1_SIGNED62_ONE, gv)
*)
Lemma secp256k1_modinv64_var_spec_prime_sub :
  funspec_sub (snd secp256k1_modinv64_var_spec) (snd secp256k1_modinv64_var_spec_prime).
Proof.
do_funspec_sub.
Exists w emp.
destruct w as [[[[[[[[x m] ptrx] modinfo] shx] sh_modinfo] sh_debruinj] sh_SECP256K1_SIGNED62_ONE] gv].
entailer!!.
split.
* cut (m <> 1);[lia|].
  intros Hm; apply not_prime_1.
  congruence.
* destruct (Z.eq_dec x 0) as [Hx0|Hx0];[tauto|].
  right.
  apply rel_prime_le_prime;[assumption|lia].
Qed.
