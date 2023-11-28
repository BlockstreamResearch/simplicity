Require Import ZArith.
Require Import Bool.
Require Import Lia.

Local Open Scope Z.

Lemma f_if {A B} (f: A -> B) (b:bool) x y:
  f (if b then x else y) = if b then f x else f y.
Proof.
destruct b; reflexivity.
Qed.

Lemma div_bounds a b c d : 0 < d -> d * a <= b < d * c <-> a <= b / d < c.
Proof.
intros Hd.
split; intros Hb.
* split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];tauto.
* split.
  - etransitivity;[apply Zmult_le_compat_l|apply Z.mul_div_le];lia.
  - eapply Z.lt_le_trans;[apply Z.mul_succ_div_gt|apply Zmult_le_compat_l];try lia.
Qed.

Lemma Z_shiftr_neg1_l: forall n : Z, 0 <= n -> Z.shiftr (-1) n = -1.
Proof.
apply natlike_rec.
 reflexivity.
intros x Hx Hrec.
rewrite <- Z.add_1_r, <- Z.shiftr_shiftr, Hrec by auto with zarith.
reflexivity.
Qed.

Lemma mod_add_carry m a b : 0 < m -> (a mod m + b mod m) / m = Z.b2z ((a + b) mod m <? b mod m).
Proof.
intros Hm.
assert (a_pos_bound := Z.mod_pos_bound a m Hm).
assert (b_pos_bound := Z.mod_pos_bound b m Hm).
case Z.ltb_spec;simpl (Z.b2z _);[intros Hlt|intros Hge].
 cut (1 <= (a mod m + b mod m)/m < 2);[lia|].
 apply div_bounds; auto.
 replace (m * 1) with m by ring.
 replace (m * 2) with (m + m) by ring.
 split;[|lia].
 apply Z.nlt_ge; intro Hltm; revert Hlt; apply Z.le_ngt.
 rewrite <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l.
 rewrite (Zmod_small (_ + _)); lia.
cut (0 <= (a mod m + b mod m)/m < 1);[lia|].
apply div_bounds; auto.
replace (m * 1) with m by ring.
replace (m * 0) with 0 by ring.
split;[lia|].
apply Z.nle_gt; intro Hltm; revert Hge; apply Z.lt_nge.
rewrite <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l.
replace (a mod m + b mod m) with (a mod m + b mod m - 0) by ring.
rewrite <- (Z_mod_same_full m), Zminus_mod_idemp_r.
rewrite Z.mod_small;lia.
Qed.

Lemma div_add_carry m a b : 0 < m -> (a + b) / m = a / m + b / m + Z.b2z ((a + b) mod m <? b mod m).
Proof.
intros Hm.
rewrite <- mod_add_carry by auto.
rewrite <- Z_div_plus_full_l by lia.
rewrite Z.mul_add_distr_r.
replace
  (a / m * m + b / m * m + (a mod m + b mod m))
 with
  (m * (a / m) + a mod m + (m * (b / m) + b mod m))
 by ring.
rewrite <- !Z_div_mod_eq_full.
reflexivity.
Qed.

Lemma shiftr_mod_add_carry n a b : 0 <= n -> Z.shiftr (a mod (2^n) + b mod (2^n)) n = Z.b2z ((a + b) mod (2^n) <? b mod (2^n)).
Proof.
intros Hn.
rewrite Z.shiftr_div_pow2 by assumption.
apply mod_add_carry.
auto with *.
Qed.

Lemma shiftr_add_carry n a b : 0 <= n -> Z.shiftr (a + b) n = Z.shiftr a n + Z.shiftr b n + Z.b2z ((a + b) mod (2^n) <? b mod (2^n)).
Proof.
intros Hn.
rewrite !Z.shiftr_div_pow2 by assumption.
apply div_add_carry.
auto with *.
Qed.

Lemma mod_sub_borrow m a b : 0 < m -> (a mod m - b mod m) / m = - Z.b2z (a mod m <? b mod m).
Proof.
intros Hm.
assert (a_pos_bound := Z.mod_pos_bound a m Hm).
assert (b_pos_bound := Z.mod_pos_bound b m Hm).
case Z.ltb_spec;simpl (Z.b2z _);[intros Hlt|intros Hge].
 cut (-1 <= (a mod m - b mod m)/m < 0);[lia|].
 apply div_bounds; auto.
 lia.
cut (0 <= (a mod m - b mod m)/m < 1);[lia|].
apply div_bounds; auto.
lia.
Qed.

Lemma div_sub_borrow m a b : 0 < m -> (a - b) / m = a / m - b / m - Z.b2z (a mod m <? b mod m).
Proof.
intros Hm.
unfold Z.sub.
rewrite <- mod_sub_borrow by auto.
rewrite <- Z_div_plus_full_l by lia.
rewrite Z.mul_add_distr_r.
replace
  (a / m * m + - (b / m) * m + (a mod m - b mod m))
 with
  (m * (a / m) + a mod m - (m * (b / m) + b mod m))
 by ring.
rewrite <- !Z_div_mod_eq_full.
reflexivity.
Qed.

Lemma shiftr_bounds a b c n : 2^n * a <= b < 2^n * c -> a <= Z.shiftr b n < c.
Proof.
intros Hb.
assert (Hn : 0 <= n).
 destruct (Z.neg_nonneg_cases n); auto.
 rewrite (Z.pow_neg_r 2 n) in Hb; lia. 
rewrite Z.shiftr_div_pow2 by assumption.
apply div_bounds; auto with *.
Qed.

Lemma shiftr_mod_sub_borrow n a b : 0 <= n -> Z.shiftr (a mod (2^n) - b mod (2^n)) n = - Z.b2z (a mod (2^n) <? b mod (2^n)).
Proof.
intros Hn.
rewrite Z.shiftr_div_pow2 by assumption.
apply mod_sub_borrow.
auto with *.
Qed.

Lemma shiftr_sub_borrow n a b : 0 <= n -> Z.shiftr (a - b) n = Z.shiftr a n - Z.shiftr b n - Z.b2z (a mod (2^n) <? b mod (2^n)).
Proof.
intros Hn.
rewrite !Z.shiftr_div_pow2 by assumption.
apply div_sub_borrow.
auto with *.
Qed.

Lemma shiftr_small a n : 0 <= a < 2^n -> Z.shiftr a n = 0.
Proof.
intros [Ha0 Ha1].
apply Zle_lt_or_eq in Ha0.
destruct Ha0 as [Ha0| <-].
 apply Z.shiftr_eq_0.
  lia.
 apply Z.log2_lt_pow2; assumption.
apply Z.shiftr_0_l.
Qed.

Lemma shiftr_small_iff a n : 0 <= n -> Z.shiftr a n = 0 <-> 0 <= a < 2^n.
Proof.
intros Hn.
split;[|apply shiftr_small].
rewrite Z.shiftr_eq_0_iff.
intros [->|[Ha Hlog]];[lia|].
rewrite <- Z.log2_lt_pow2 in Hlog; lia.
Qed.

Lemma shiftr_small_neg a n : -2^n <= a < 0 -> Z.shiftr a n = -1.
Proof.
intros Ha.
cut (-1 <= Z.shiftr a n < 0);[lia|].
apply shiftr_bounds.
lia.
Qed.

Lemma shiftr_small_neg_iff a n : 0 <= n -> Z.shiftr a n = -1 <-> -2^n <= a < 0.
Proof.
intros Hn.
split;[|apply shiftr_small_neg].
intros Ha.
split;[|apply (Z.shiftr_neg _ n);lia].
rewrite Z.shiftr_div_pow2 in Ha by assumption.
rewrite (Z_div_mod_eq_full a (2^n)), Ha.
assert (X := Z.mod_pos_bound a (2^n)).
lia.
Qed.

Lemma shiftr_small_signed a n m : -2^n <= a < 2^n -> 0 < m ->
  Z.shiftr a (n + m) = Z.shiftr a n.
Proof.
intros [Ha0 Ha1] Hm.
rewrite <- Z.shiftr_shiftr by lia.
destruct (Z.neg_nonneg_cases a);
[|rewrite (shiftr_small _ n), Z.shiftr_0_l by lia; reflexivity].
replace (Z.shiftr a n) with (-1);
[rewrite Z_shiftr_neg1_l by lia; reflexivity|].
cut (-1 <= Z.shiftr a n < 0);[lia|].
apply shiftr_bounds.
lia.
Qed.

Lemma shiftl_mod_eqb_unique n a b c d :
 0 <= n ->
 Z.shiftl a n + b mod 2^n =? Z.shiftl c n + d mod 2^n =
 ((a =? c) && (b mod 2^n =? d mod 2^n))%bool.
Proof.
intros Hn.
rewrite !Z.shiftl_mul_pow2 by auto.
symmetry; rewrite andb_comm.
case Z.eqb_spec;[case Z.eqb_spec|].
- intros -> ->.
  symmetry.
  apply Z.eqb_eq.
  reflexivity.
- intros Hac ->.
  symmetry.
  apply Z.eqb_neq.
  rewrite Z.add_cancel_r.
  intros Hneq.
  apply Z.mul_reg_r in Hneq; auto with *.
- intros Hbd.
  symmetry.
  apply Z.eqb_neq.
  intros Hneq.
  apply Hbd.
  rewrite <- Z.mod_mod by auto with *.
  rewrite <- (Z_mod_plus_full _ a), Z.add_comm, Hneq, Z.add_comm, Z_mod_plus_full.
  rewrite Z.mod_mod by auto with *.
  reflexivity.
Qed.

Lemma Z_mod_eq_bounded a b m x y :
 0 < m ->
 b - a <= m ->
 a <= x <= b - 1 ->
 a <= y <= b - 1 ->
 x mod m = y mod m ->
 x = y.
Proof.
intros Hm Hab Hx Hy Hxym.
cut (x - a = y - a);[lia|].
rewrite (Z_div_mod_eq_full (x - a) m), (Z_div_mod_eq_full (y - a) m),
        <- Zminus_mod_idemp_l, Hxym, Zminus_mod_idemp_l.
do 2 f_equal.
assert (Hx' : 0 <= (x - a)/m < 1) by (apply div_bounds; lia).
assert (Hy' : 0 <= (y - a)/m < 1) by (apply div_bounds; lia).
lia.
Qed.

Lemma Z_lor_pos (a b : Z) : 0 <= a -> 0 < b -> 0 < Z.lor a b.
Proof.
intros Ha Hb.
cut (0 <= Z.lor a b).
* intros Hab.
  apply Z.le_lteq in Hab.
  destruct Hab; try assumption.
  cut (false = true);[discriminate|].
  rewrite <- (Z.bits_0 (Z.log2 b)), H, Z.lor_spec, Z.bit_log2, orb_true_r; auto.
* apply Z.lt_le_incl in Hb.
  rewrite Z.bits_iff_nonneg_ex in *.
  destruct Ha as [ka Ha].
  destruct Hb as [kb Hb].
  exists (Z.max ka kb).
  intros m Hm.
  rewrite Z.lor_spec, Ha, Hb; lia.
Qed.

Lemma Z_log2_lt_pow2 (a b : Z) : 0 < b -> a < 2 ^ b <-> Z.log2 a < b.
Proof.
intros Hb.
destruct a as [|a|a];[|apply Z.log2_lt_pow2;lia|];auto with *.
Qed.

Lemma Z_shiftr_ones a n : 0 <= n <= a -> (Z.shiftr (Z.ones a) n) = Z.ones (a - n).
Proof.
intros Hn.
apply Z.bits_inj.
intros i.
destruct (Z.neg_nonneg_cases i) as [Hi|Hi];
[rewrite !Z.testbit_neg_r by lia; reflexivity|].
rewrite Z.shiftr_spec, !Z.testbit_ones_nonneg; lia.
Qed.

Lemma Z_land_ones_min a b : 0 <= a -> 0 <= b ->
  (Z.land (Z.ones a) (Z.ones b)) = Z.ones (Z.min a b).
intros Ha fhb.
apply Z.bits_inj.
intros i.
destruct (Z.neg_nonneg_cases i) as [Hi|Hi];
[rewrite !Z.testbit_neg_r by lia; reflexivity|].
rewrite Z.land_spec; rewrite !Z.testbit_ones_nonneg; lia.
Qed.

Lemma eqm_2_pow_le m n a b : 0 <= m <= n -> eqm (2^n) a b -> eqm (2^m) a b.
Proof.
intros Hmn.
unfold eqm.
rewrite <- !Z.land_ones by lia.
replace m with (Z.min n m) by lia.
rewrite <- !Z_land_ones_min, !Z.land_assoc by lia.
intros ->.
reflexivity.
Qed.

Lemma Z_shiftr_mod_2 a i j : 0 <= i -> 0 <= j -> Z.shiftr a i mod 2^j = Z.shiftr (a mod 2^(j + i)) i.
Proof.
intros Hi Hj.
rewrite <-!Z.land_ones by lia.
rewrite Z.shiftr_land, Z_shiftr_ones by lia.
repeat f_equal.
lia.
Qed.

Definition Z_of_comparison (c : Datatypes.comparison) : Z :=
match c with
| Gt => 1
| Eq => 0
| Lt => -1
end.

Lemma comp_Z_of_comparison c : Z_of_comparison c ?= 0 = c.
Proof.
destruct c; reflexivity.
Qed.

Lemma Z_of_comparison_bounds c : -1 <= Z_of_comparison c <= 1.
Proof.
destruct c; cbn; lia.
Qed.

Fixpoint Pos_ctz (p : positive) : nat :=
match p with
| xO p0 => Nat.succ (Pos_ctz p0)
| _ => 0
end.

(* ctz 0 is normally undefined.  We simply return 0 in this case. *)
Definition Z_ctz (a : Z) : Z :=
match a with
| Z0 => 0
| Zpos p => Z.of_nat (Pos_ctz p)
| Zneg p => Z.of_nat (Pos_ctz p)
end.

Lemma Z_ctz_non_neg a : 0 <= Z_ctz a.
Proof.
destruct a; cbn; lia.
Qed.

Lemma Z_ctz_bound_aux a n : Z.pos a < 2^(Z.of_nat n) -> (Pos_ctz a < n)%nat.
Proof.
destruct n; try lia.
revert n.
induction a; auto with *.
intros n Hn.
rewrite Nat2Z.inj_succ, Z.pow_succ_r, Pos2Z.inj_xO, <- Z.mul_lt_mono_pos_l in Hn by lia.
simpl.
rewrite <- Nat.succ_lt_mono.
destruct n; try lia.
auto.
Qed.

Lemma Z_ctz_bound a n : a <> 0 -> -2^n < a < 2^n -> Z_ctz a < n.
Proof.
intros Ha0 Ha.
destruct (Z.neg_nonneg_cases n);[rewrite Z.pow_neg_r in Ha;lia|].
destruct a; try lia; simpl;
rewrite <- (Z2Nat.id _ H);
apply Nat2Z.inj_lt;
apply Z_ctz_bound_aux;
rewrite (Z2Nat.id _ H);
lia.
Qed.

Lemma Z_ctz_testbit_false a i : i < Z_ctz a -> Z.testbit a i = false.
Proof.
revert i.
destruct a; try induction p; simpl in *; try lia;
try solve [auto using Z.testbit_neg_r];
intros i Hi;
[rewrite Pos2Z.pos_xO|rewrite Pos2Z.neg_xO];
rewrite Z.double_bits;
apply IHp;
rewrite Z.lt_pred_lt_succ, <- Zpos_P_of_succ_nat;
assumption.
Qed.

Lemma Z_ctz_testbit_true a : a <> 0 -> Z.testbit a (Z_ctz a) = true.
Proof.
destruct a; try lia; intros _;
induction p; try reflexivity;
simpl (Z_ctz _);
rewrite Zpos_P_of_succ_nat;
[rewrite Pos2Z.pos_xO|rewrite Pos2Z.neg_xO];
rewrite Z.double_bits_succ;
apply IHp.
Qed.

Lemma Z_neg_lnot a : -a = Z.lnot a + 1.
Proof.
cut (a + Z.lnot a = -1);[lia|].
apply Z.add_lnot_diag.
Qed.

Lemma Z_testbit_neg_low_aux a i : i <= Z_ctz (Z.pos a) ->
  Z.testbit (-(Z.pos a)) i = Z.testbit (Z.pos a) i.
Proof.
destruct (Z.neg_nonneg_cases i);
[rewrite !Z.testbit_neg_r; auto|].
revert i H a.
apply (natlike_ind (fun i =>
forall a, i <= Z_ctz (Z.pos a) ->
Z.testbit (-(Z.pos a)) i =
Z.testbit (Z.pos a) i)).
* intros a _.
  rewrite Z_neg_lnot, Z.add_bit0, Z.lnot_spec, xorb_true_r by lia.
  apply negb_involutive.
* intros i H Hrec a Hi.
  destruct a; try solve [simpl in Hi; lia].
  rewrite Pos2Z.inj_xO, <- Z.mul_opp_r, !Z.double_bits_succ.
  apply Hrec.
  simpl in *.
  lia.
Qed.

Lemma Z_testbit_neg_low a i : i <= Z_ctz a ->
  Z.testbit (-a) i = Z.testbit a i.
Proof.
intros Hi.
destruct a.
* reflexivity.
* auto using Z_testbit_neg_low_aux.
* symmetry; apply Z_testbit_neg_low_aux.
  assumption.
Qed.

Lemma Z_testbit_neg_high_aux a i : Z_ctz (Z.pos a) < i ->
  Z.testbit (-(Z.pos a)) i = negb (Z.testbit (Z.pos a) i).
Proof.
revert i.
induction a.
* intros i Hi.
  simpl in Hi.
  rewrite Z_neg_lnot, Z.add_nocarry_lxor, Z.lxor_spec, Z.lnot_spec; try lia.
  1:{
    change (Z.testbit 1) with (Z.testbit (Z.ones 1)).
    rewrite (Z.ones_spec_high 1 i), xorb_false_r by lia.
    reflexivity.
  }
  apply Z.bits_inj_iff'.
  intros n Hn.
  rewrite Z.bits_0, Z.land_comm, Z.land_spec, Z.lnot_spec by lia.
  apply Zle_lt_or_eq in Hn.
  destruct Hn as [Hn|<-];[|reflexivity].
  change (Z.testbit 1) with (Z.testbit (Z.ones 1)).
  rewrite (Z.ones_spec_high 1 n) by lia.
  reflexivity.
* intros i Hi.
  rewrite Pos2Z.inj_xO, <- Z.mul_opp_r, !Z.double_bits.
  apply IHa.
  cbn in Hi.
  rewrite Zpos_P_of_succ_nat, Z.lt_succ_lt_pred in Hi.
  assumption.
* cbn.
  intros i Hi.
  change (Z.testbit 1) with (Z.testbit (Z.ones 1)).
  rewrite Z.bits_m1, (Z.ones_spec_high 1 i) by lia. 
  reflexivity.
Qed.

Lemma Z_testbit_neg_high a i : a <> 0 -> Z_ctz a < i ->
  Z.testbit (-a) i = negb (Z.testbit a i).
Proof.
intros Ha Hi.
destruct a.
* lia.
* auto using Z_testbit_neg_high_aux.
* rewrite <- (negb_involutive (Z.testbit (-Z.neg p) i)).
  f_equal; symmetry.
  apply (Z_testbit_neg_high_aux p).
  assumption.
Qed.

Lemma Z_x_and_opp_x a : a <> 0 -> Z.land a (-a) = 2^(Z_ctz a).
Proof.
intros Ha.
apply Z.bits_inj'.
intros n Hn.
rewrite Z.land_spec, Z.pow2_bits_eqb by apply Z_ctz_non_neg.
destruct (Z.le_gt_cases n (Z_ctz a));
[|rewrite Z_testbit_neg_high, andb_negb_r by auto;lia].
rewrite Z_testbit_neg_low, andb_diag by auto.
apply Z.le_lteq in H.
destruct H as [H| ->];
[rewrite Z_ctz_testbit_false|rewrite Z_ctz_testbit_true]; lia.
Qed.

Lemma Z_testbit_false_ctz a i : a <> 0 -> (forall j, 0 <= j <= i -> Z.testbit a j = false) -> i < Z_ctz a.
Proof.
intros Ha0 Ha.
apply Z.nle_gt.
intros Hi.
assert (Htest : Z.testbit a (Z_ctz a) = false).
* apply Ha.
  auto using Z_ctz_non_neg.
* rewrite Z_ctz_testbit_true in Htest by assumption.
  discriminate.
Qed.

Lemma Z_ctz_lor_l a b : a <> 0 -> Z_ctz (Z.lor a b) <= Z_ctz a.
Proof.
intros Ha.
cut (forall i, i < Z_ctz (Z.lor a b) -> i < Z_ctz a).
* intros H.
  apply Z.lt_pred_le.
  apply H.
  lia.
* intros i Hi.
  apply Z_testbit_false_ctz;[assumption|].
  intros j Hj.
  eapply proj1.
  apply orb_false_iff.
  rewrite <- Z.lor_spec.
  apply Z_ctz_testbit_false.
  eapply Z.le_lt_trans;[|apply Hi].
  tauto.
Qed.

