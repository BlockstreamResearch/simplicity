Require Import ZArith.
Require Import Bool.
Require Import Lia.

Local Open Scope Z.

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