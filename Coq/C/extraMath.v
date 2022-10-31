Require Import ZArith.
Require Import Bool.
Require Import Lia.

Local Open Scope Z.

Lemma div_bounds a b c d : d * a <= b < d * c -> 0 < d -> a <= b / d < c.
Proof.
intros Hb Hd.
split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];tauto.
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
auto using div_bounds with *.
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