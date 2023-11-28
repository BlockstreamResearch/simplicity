Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import Coq.Logic.Eqdep_dec.

Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

Record Bezout (a b d : Z) :=
{ uBezout : Z
; vBezout : Z
; HBezout : uBezout * a + vBezout * b = d
}.
Arguments uBezout [a b d].
Arguments vBezout [a b d].

Definition Bezout_normalize [a b d] (H: Bezout a b d) : Bezout a b d.
exists (uBezout H) (vBezout H).
match goal with
 |- ?x = ?y => destruct (Z.eq_dec x y);[assumption|]
end.
abstract (destruct H;contradiction).
Defined.

Lemma Bezout_normalize_eq a b d (H: Bezout a b d) : Bezout_normalize H = H.
Proof.
destruct H as [u v H].
unfold Bezout_normalize.
destruct (Z.eq_dec _ _);try contradiction.
replace e with H; try reflexivity.
apply UIP_dec.
apply Z.eq_dec.
Qed.

Definition Bezout_0b b : Bezout 0 b (Z.abs b).
exists 0 (Z.sgn b).
abstract (rewrite <- Z.sgn_abs;ring).
Defined.

Definition Bezout_a0 a : Bezout a 0 (Z.abs a).
exists (Z.sgn a) 0.
abstract (rewrite <- Z.sgn_abs;ring).
Defined.

Definition Bezout_aba a b : Bezout a b a.
exists 1 0.
abstract ring.
Defined.

Definition Bezout_abb a b : Bezout a b b.
exists 0 1.
abstract ring.
Defined.

Definition Bezout_b_minus_a a b d : Bezout (b - a) a d -> Bezout a b d.
intros bezout.
exists (vBezout bezout - uBezout bezout) (uBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_a_minus_b a b d : Bezout (a - b) b d -> Bezout a b d.
intros bezout.
exists (uBezout bezout) (vBezout bezout - uBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_even a b d : Bezout a b d -> Bezout (2*a) (2*b) (2*d).
intros bezout.
exists (uBezout bezout) (vBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_flip a b d : Bezout a b d -> Bezout b a d.
intros bezout.
exists (vBezout bezout) (uBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_2a a b d : Z.Odd b -> Bezout a b d -> Bezout (2*a) b d.
intros Hodd [u v Huv].
destruct (Z.odd u) eqn:H.
  exists (Z.div2 (u + b)) (v - a).
  abstract (
    rewrite <- Z.odd_spec in Hodd;
    rewrite (Zdiv2_odd_eqn u), (Zdiv2_odd_eqn b) in Huv|-*;
    rewrite <- Huv, H, Hodd;
    rewrite Z.div2_div;
    replace (2 * Z.div2 u + 1 + (2 * Z.div2 b + 1)) with
      ((Z.div2 u + Z.div2 b + 1) * 2) by ring;
    rewrite Z.div_mul by lia;
    ring
  ).
exists (Z.div2 u) v.
abstract (
  rewrite (Zdiv2_odd_eqn u) in Huv;
  rewrite <- Huv, H;
  ring
).
Defined.

Definition Bezout_2b a b d : Z.Odd a -> Bezout a b d -> Bezout a (2*b) d.
intros Hodd bezout.
apply Bezout_flip.
apply Bezout_2a; try assumption.
apply Bezout_flip.
assumption.
Defined.

Lemma Pos_size_nat_sub a b : (Pos.size_nat (a - b) <= Pos.size_nat a)%nat.
Proof.
destruct (Pos.lt_total a b) as [H|[->|H]].
* rewrite (Pos.sub_lt _ _ H); destruct a; simpl; lia.
* rewrite Pos.sub_diag; destruct b; simpl; lia.
* apply Pos.size_nat_monotone; apply Pos.sub_decr; assumption.
Qed.

Definition Pos_Bezoutn : forall n a b,
  (Pos.size_nat a + Pos.size_nat b <= n)%nat -> Bezout (Z.pos a) (Z.pos b) (Z.pos (Pos.gcdn n a b)).
fix Pos_Bezoutn 1.
intros [|n].
* abstract (intros a b Hn; destruct a; destruct b; simpl in Hn; lia).
* intros [a'|a0|].
  + intros [b'|b0|] Hsize;simpl.
    - destruct (a' ?= b')%positive eqn:Hcmp; simpl.
      apply Bezout_aba.
      apply Bezout_b_minus_a;simpl;apply Bezout_2a;
      [abstract (rewrite <- Z.odd_spec; reflexivity)|].
      destruct (Z.eq_dec (Z.pos_sub b' a') (Z.pos (b' - a'))) as [->|Hneq];
      [apply (Pos_Bezoutn n);abstract(assert (H:=Pos_size_nat_sub b' a'); simpl in *;lia)|].
      abstract (rewrite Pos.compare_lt_iff in Hcmp;apply Z.pos_sub_gt in Hcmp;contradiction).
      apply Bezout_a_minus_b;simpl;apply Bezout_2a;
      [abstract (rewrite <- Z.odd_spec; reflexivity)|].
      destruct (Z.eq_dec (Z.pos_sub a' b') (Z.pos (a' - b'))) as [->|Hneq];
      [apply (Pos_Bezoutn n);abstract(assert (H:=Pos_size_nat_sub a' b'); simpl in *;lia)|].
      abstract (rewrite Pos.compare_gt_iff in Hcmp;apply Z.pos_sub_gt in Hcmp;contradiction).
    - change (Z.pos b0~0) with (2*Z.pos b0);apply Bezout_2b;
      [abstract (rewrite <- Z.odd_spec; reflexivity)|].
      apply (Pos_Bezoutn n).
      abstract(simpl in *;lia).
    - apply Bezout_abb.
  + intros [b'|b0|] Hsize;simpl.
    - change (Z.pos a0~0) with (2*Z.pos a0);apply Bezout_2a;
      [abstract (rewrite <- Z.odd_spec; reflexivity)|].
      apply (Pos_Bezoutn n).
      abstract(simpl in *;lia).
    - apply (Bezout_even (Z.pos a0) (Z.pos b0) (Z.pos (Pos.gcdn n a0 b0))).
      apply (Pos_Bezoutn n).
      abstract(simpl in *;lia).
    - apply Bezout_abb.
  + intros b _.
    apply Bezout_aba.
Defined.

Definition Pos_Bezout a b : Bezout (Z.pos a) (Z.pos b) (Z.pos (Pos.gcd a b)).
apply Bezout_normalize.
apply Pos_Bezoutn.
abstract lia.
Defined.

Definition Bezout_neg_a a b d : Bezout (-a) b d -> Bezout a b d.
intros bezout.
exists (- uBezout bezout) (vBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_neg_b a b d : Bezout a (-b) d -> Bezout a b d.
intros bezout.
exists (uBezout bezout) (- vBezout bezout).
abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

Definition Bezout_gcd a b : Bezout a b (Z.gcd a b).
apply Bezout_normalize.
destruct a; try apply Bezout_0b; destruct b; try apply Bezout_a0.
* apply Pos_Bezout.
* apply Bezout_neg_b; apply Pos_Bezout.
* apply Bezout_neg_a; apply Pos_Bezout.
* apply Bezout_neg_a; apply Bezout_neg_b; apply Pos_Bezout.
Defined.

Definition modInv a b := Zmod (uBezout (Bezout_gcd (Zmod a b) b)) b.

Lemma modInv_zero b : modInv 0 b = 0.
Proof.
reflexivity.
Qed.

Lemma modInv_divide a b : (b | a) -> modInv a b = 0.
Proof.
intros Hba.
unfold modInv.
rewrite (Zdivide_mod _ _ Hba).
apply (modInv_zero b).
Qed.

Lemma modInv_mul_l a b : modInv a b * a mod b = Z.gcd a b mod b.
Proof.
unfold modInv.
destruct (Bezout_gcd (a mod b) b) as [u v Huv]; simpl.
rewrite Zmult_mod_idemp_l, <- Zmult_mod_idemp_r.
replace (u * (a mod b)) with (Z.gcd (a mod b) b + (- v) * b) by lia.
destruct (Z.eq_dec b 0) as [->|Hb].
* rewrite !Zmod_0_r; ring.
* rewrite Z.gcd_mod, Z.gcd_comm by assumption.
  apply Z_mod_plus_full.
Qed.

Lemma modInv_mul_r a b : a * modInv a b mod b = Z.gcd a b mod b.
Proof.
rewrite Z.mul_comm.
apply modInv_mul_l.
Qed.

Lemma modInv_mul_unique_l a b x : x * a mod b = 1 -> x mod b = modInv a b.
Proof.
intros Hx.
destruct (Z_dec' b 0) as [[Hb0|Hb0]| ->].
* apply (Z.mod_neg_bound (x*a)) in Hb0.
  lia.
* apply Zmod_divide_minus in Hx;[|assumption].
  destruct (Hx) as [c Hc].
  unfold modInv.
  symmetry.
  apply Zdivide_mod_minus;[apply Z.mod_pos_bound;assumption|].
  replace (uBezout (Bezout_gcd (a mod b) b) - x mod b)
   with ((uBezout (Bezout_gcd (a mod b) b) - x) + (x - x mod b)) by ring.
  apply Z.divide_add_r;[|apply Zmod_divide_minus;lia].
  destruct (Bezout_gcd (a mod b) b) as [u v Huv]; simpl.
  rewrite Z.gcd_mod, Zmod_eq in Huv by lia.
  assert (Hgcd : Z.gcd b a = 1).
  1:{
    apply Z.bezout_1_gcd.
    exists (-c); exists x.
    lia.
  }
  rewrite Hgcd in Huv.
  apply Z.gauss with a;[|lia].
  exists (-c - v + u*(a/b)).
  lia.
* assert (Hmodinv := modInv_mul_r a 0).
  rewrite !Zmod_0_r, Z.gcd_0_r in *.
  rewrite Z.mul_comm in Hx.
  destruct (Z.mul_eq_1 _ _ Hx) as [->| ->];lia.
Qed.

Lemma modInv_mul_unique_r a b x : a * x mod b = 1 -> x mod b = modInv a b.
Proof.
rewrite Z.mul_comm.
apply modInv_mul_unique_l.
Qed.

Lemma modInv_eqm N a b : eqm N a b -> modInv a N = modInv b N.
Proof.
intros Hab.
unfold modInv.
rewrite Hab.
reflexivity.
Qed.

Transparent Z.shiftr Z.pow.
Lemma HackersDelightA a : Z.Odd a ->
  Z.land (-(a + (Z.shiftl (Z.land (a + 1) 4)) 1)) (Z.ones 4) =  modInv (-a) (2^4).
Proof.
rewrite <- Z.odd_spec.
intros Hodd.
rewrite Z.land_ones by lia.
rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
rewrite <- Zplus_mod_idemp_l.
change (Z.land (a + 1) 4) with (Z.land (a + 1) (Z.land (Z.ones 4) 4)).
rewrite Z.land_assoc, Z.land_ones by lia.
rewrite <- (Zplus_mod_idemp_l a).
unfold modInv.
symmetry.
rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
assert (Ha : 0 <= a mod 2^4 < 2^4) by (apply Z.mod_pos_bound;lia).
assert (Hodd0 : Z.odd (a mod 2 ^ 4) = true).
1:{
  rewrite <- Z.bit0_odd in *|-*.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec, Hodd.
  reflexivity.
}
destruct (a mod 2^4) as [|b|b]; try discriminate; try lia.
do 4 (destruct b; try reflexivity; try discriminate; try lia).
Qed.

Lemma HackersDelightB a : Z.Odd a ->
  Z.land (a * (a * a - 2)) (Z.ones 6) =  modInv (-a) (2^6).
Proof.
rewrite <- Z.odd_spec.
intros Hodd.
rewrite Z.land_ones by lia.
rewrite <- Zmult_mod_idemp_l, <- Zmult_mod_idemp_r, <- Zminus_mod_idemp_l.
rewrite <- (Zmult_mod_idemp_l a), <- (Zmult_mod_idemp_r a).
rewrite Zminus_mod_idemp_l, Zmult_mod_idemp_r.
unfold modInv.
symmetry.
rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
assert (Ha : 0 <= a mod 2^6 < 2^6) by (apply Z.mod_pos_bound;lia).
assert (Hodd0 : Z.odd (a mod 2 ^ 6) = true).
1:{
  rewrite <- Z.bit0_odd in *|-*.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec, Hodd.
  reflexivity.
}
destruct (a mod 2^6) as [|b|b]; try discriminate; try lia.
do 6 (destruct b; try reflexivity; try discriminate; try lia).
Qed.