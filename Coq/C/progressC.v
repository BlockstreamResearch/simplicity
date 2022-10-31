Require Import VST.floyd.proofauto.
Require Import extraMath.

Lemma Int64_low_is_nonneg (x : Z) :
 Int64.min_signed <= x <= Int64.max_signed ->
 x mod 2 ^ 64 <= Int64.max_signed -> 0 <= x <= Int64.max_signed.
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
 Int64.max_signed < x mod 2 ^ 64 -> Int64.min_signed <= x < 0.
Proof.
intros [Hx0 Hx1] Hxmod.
destruct (Z.neg_nonneg_cases x) as [Hneg|Hpos].
* change x with (2^64 mod 2^64 + x) in Hxmod.
  rewrite Zplus_mod_idemp_l in Hxmod.
  rewrite Z.mod_small in Hxmod; rep_lia.
* apply Zle_not_lt in Hxmod;[contradiction|].
  rewrite Z.mod_small; rep_lia.
Qed.

Lemma umul64_bounds_tight x y : 0 <= x <= 2^32 - 1 -> 0 <= y <= 2^32-1 ->
  0 <= x * y <= 2^64 - 2^33 + 1.
Proof.
intros Hx Hy.
split;[lia|].
change (2 ^ 64 - 2 ^ 33 + 1) with ((2 ^ 32 - 1)*(2 ^ 32 - 1)).
transitivity (x * (2^32-1));[apply Zmult_le_compat_l|apply Zmult_le_compat_r]; try tauto.
lia.
Qed.

Lemma smul_bounds_tight a b x y : 0 <= a <= b ->
  -b <= x <= a -> -b <= y <= a ->
  -(a * b) <= x * y <= b * b.
Proof.
intros Hab.
destruct (Z.neg_nonneg_cases y).
 split.
  rewrite <- Z.mul_opp_r.
  etransitivity;[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonpos_r];lia.
 etransitivity;[apply (Z.mul_le_mono_nonpos_r (-b))
               |rewrite Z.mul_opp_comm;apply Z.mul_le_mono_nonneg_l];lia.
split.
 rewrite Z.mul_comm, <- Z.mul_opp_l.
 etransitivity;[apply Z.mul_le_mono_nonpos_l|apply Z.mul_le_mono_nonneg_r];lia.
etransitivity;[apply (Z.mul_le_mono_nonneg_r _ b)|apply Z.mul_le_mono_nonneg_l];lia.
Qed.

Lemma smul64_bounds_tight x y : -2^31 <= x <= 2^31 - 1 -> -2^31 <= y <= 2^31 - 1 ->
  -2^62+2^31 <= x * y <= 2^62.
Proof.
assert (H := smul_bounds_tight (2^31 - 1) (2^31) x y).
lia.
Qed.

Lemma smul128_bounds_tight x y : -2^63 <= x <= 2^63 - 1 -> -2^63 <= y <= 2^63 - 1 ->
  -2^126+2^63 <= x * y <= 2^126.
Proof.
assert (H := smul_bounds_tight (2^63 - 1) (2^63) x y).
lia.
Qed.

Lemma sumul64_bounds x y : -2^31 <= x <= 2^31 - 1 -> 0 <= y <= 2^32-1 ->
  -2^63 <= x * y <= 2^63 - 1.
Proof.
intros Hx Hy.
change (2^63) with (2^31 * 2^32).
split.
 rewrite <- Z.mul_opp_l.
 transitivity (-2^31 * y);[|apply Z.mul_le_mono_nonneg_r];lia.
transitivity ((2^31 - 1)*(2^32));[|lia].
transitivity ((2^31 - 1) * y);[apply Z.mul_le_mono_nonneg_r|];lia.
Qed.

Lemma usmul64_bounds x y : -2^31 <= y <= 2^31 - 1 -> 0 <= x <= 2^32-1 ->
  -2^63 <= x * y <= 2^63 - 1.
Proof.
rewrite Z.mul_comm.
auto using sumul64_bounds.
Qed.
(*
Lemma add_bounds ax ay az cx cy cz : ax <= ay <= az -> cx <= cy <= cz ->
 ax + cx <= ay + cy <= az + cz.
Proof.
lia.
Qed.
*)
Lemma unadd_bounds_unsigned_32 ax ay az b : ax <= ay <= az - 2^32 + 1 ->
  0 <= b <= 2^32-1 -> ax <= ay + b <= az.
Proof.
lia.
Qed.

Lemma unadd_bounds_signed_32 ax ay az b : ax + 2^31 <= ay <= az - 2^31 + 1 ->
  -2^31 <= b <= 2^31-1 -> ax <= ay + b <= az.
Proof.
lia.
Qed.

Lemma unadd_bounds_b2z ax ay az b : ax <= ay <= az - 1 ->
  ax <= ay + Z.b2z b <= az.
Proof.
destruct b;simpl;lia.
Qed.

Lemma unadd_bounds_small b ax ay az : ax - b <= ay <= az - b ->
   ax <= ay + b <= az.
Proof.
lia.
Qed.
(*
Lemma umul64_bounds x y a b : 0 <= x <= 2^32 - 1 -> 0 <= y <= 2^32-1 ->
  0 <= a <= 2^32-1 -> 0 <= b <= 2^32-1 -> 0 <= x * y + a + b <= 2^64 - 1.
Proof.
intros Hx Hy Ha Hb.
change (2 ^ 64- 1) with (2^64 - 2^33 + 1 + (2^32 - 1) + (2^32 - 1)).
change 0 with (0 + 0 + 0).
repeat (apply add_bounds;[|tauto]).
apply umul64_bounds_tight; tauto.
Qed.
*)

Lemma strict_bounds a b : a < b <-> a <= b-1.
Proof.
rep_lia.
Qed.

Lemma strict_bounds' a b c : a <= b < c+1 <-> a <= b <= c.
Proof.
rep_lia.
Qed.

Lemma weaken_bounds a b c d e : b <= c <= d -> a <= b -> d <= e -> a <= c <= e.
Proof.
rep_lia.
Qed.

Lemma of_bool_if b : Val.of_bool b = Vint (Int.repr (Z.b2z b)).
Proof.
destruct b; reflexivity.
Qed.
(*
Lemma Int_unsigned_b2z b : Int.unsigned (Int.repr (Z.b2z b)) = Z.b2z b.
Proof.
destruct b; reflexivity.
Qed.
*)
Lemma Int_signed_b2z b : Int.signed (Int.repr (Z.b2z b)) = Z.b2z b.
Proof.
destruct b; reflexivity.
Qed.

Lemma ltu_eq a b : Int.ltu (Int.repr a) (Int.repr b) = (a mod 2^32 <? b mod 2^32).
Proof.
destruct (Int.ltu _ _) eqn:Hlt; [apply ltu_inv in Hlt|apply ltu_false_inv in Hlt];
revert Hlt;
rewrite !Int.unsigned_repr_eq;
change (Int.modulus) with (2^32);
lia.
Qed.

Lemma ltu_eq64 a b : Int64.ltu (Int64.repr a) (Int64.repr b) = (a mod 2^64 <? b mod 2^64).
Proof.
destruct (Int64.ltu _ _) eqn:Hlt; [apply ltu_inv64 in Hlt|apply ltu_false_inv64 in Hlt];
revert Hlt;
rewrite !Int64.unsigned_repr_eq;
change (Int64.modulus) with (2^64);
lia.
Qed.

Lemma eq_eq64 a b : Int64.eq (Int64.repr a) (Int64.repr b) = (a mod 2^64 =? b mod 2^64).
Proof.
symmetry.
rewrite <- !Int64.unsigned_repr_eq.
destruct (Int64.eq _ _) eqn:Heq.
* apply Int64.same_if_eq in Heq.
  rewrite Z.eqb_eq.
  congruence.
* apply int64_eq_false_e in Heq.
  rewrite Z.eqb_neq.
  intros Hab; apply Heq.
  rewrite <- Int64.repr_unsigned, <- Hab, Int64.repr_unsigned.
  reflexivity.
Qed.

Lemma Int_le_bool a b : negb (Int.lt (Int.repr (Z.b2z b)) (Int.repr (Z.b2z a))) = orb (negb a) b.
Proof.
destruct a; destruct b; reflexivity.
Qed.

Lemma Int64_shru_shiftr x y : Int64.shru x y = Int64.repr (Z.shiftr (Int64.unsigned x) (Int64.unsigned y)).
Proof.
rewrite Int64.shru_div_two_p.
rewrite Zbits.Zshiftr_div_two_p by rep_lia.
reflexivity.
Qed.

Lemma Int64_shr_shiftr x y : Int64.shr x y = Int64.repr (Z.shiftr (Int64.signed x) (Int64.unsigned y)).
Proof.
rewrite Int64.shr_div_two_p.
rewrite Zbits.Zshiftr_div_two_p by rep_lia.
reflexivity.
Qed.

Lemma mul128_tight x y (Hx : -2^63 <= x <= 2^63-1)
                       (Hy : -2^63 <= y <= 2^63-1) :
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

Ltac unfold_C :=
change (Int.unsigned Int64.iwordsize') with 64 in *;
change Int.modulus with (2^32) in *;
change Int64.modulus with (2^64) in *;
change Int64.min_signed with (-2^63) in *;
change Int64.max_signed with (2^63-1) in *.

(* Tries to solve bounds of the form x <= expr <= y *)
Ltac solve_bounds :=
unfold_C;
repeat match goal with
 |- (?a1 /\ ?a2 /\ ?b) => split
end;
  solve[repeat (rep_lia
      + (setoid_rewrite <- strict_bounds';apply shiftr_bounds;rewrite strict_bounds)
      + apply unadd_bounds_unsigned_32
      + apply unadd_bounds_signed_32
      + apply unadd_bounds_b2z
      + apply (unadd_bounds_small 1)
      + (eapply weaken_bounds;[(setoid_rewrite <- strict_bounds;apply Z.mod_pos_bound;lia)
                              +apply umul64_bounds_tight
                              +apply smul64_bounds_tight
                              +apply sumul64_bounds
                              +apply usmul64_bounds
                              +apply smul128_bounds_tight
                              |rep_lia|rep_lia])
     )].

Ltac clear_mod :=
repeat match goal with
 | |- context [ (?a mod ?b)%Z ] =>
  first
  [change (?a mod ?b)%Z with ?a
  |rewrite <- Zmod_div_mod by
    (try lia; change (2^64) with (2^32 * 2^32);auto with *)
  |rewrite (Z.mod_small a b);[|solve[rewrite strict_bounds;solve_bounds]]
  ]
end.

Ltac convert_C_to_math :=
repeat (first [rewrite of_bool_if;simpl (force_val _)
              |rewrite Int64.unsigned_zero
              |rewrite Int_signed_b2z
              |rewrite Int.signed_zero
              |rewrite Int.signed_one by rep_lia
              |rewrite Int_le_bool
              |rewrite ltu_eq
              |rewrite ltu_eq64
              |rewrite eq_eq64
              |rewrite add64_repr
              |rewrite Int64.neg_repr
              |rewrite sub64_repr
              |rewrite mul64_repr
              |rewrite Int64_shru_shiftr
              |rewrite Int64_shr_shiftr
              |rewrite Int64.shl_mul_two_p; try rewrite !two_p_equiv
              ]);
repeat match goal with
 | |- context [ Int.unsigned (Int.repr ?a) ] => rewrite (Int.unsigned_repr a) by rep_lia
 | |- context [ Int64.unsigned (Int64.repr ?a) ] => rewrite (Int64.unsigned_repr a) by rep_lia
 | |- context [ Int64.signed (Int64.repr ?a) ] => rewrite (Int64.signed_repr a) by solve_bounds
end;
repeat (first [rewrite (Int.unsigned_repr_eq _)
              |rewrite (Int64.unsigned_repr_eq _)
              ]);
unfold_C;
clear_mod.

Ltac progressC :=
first [forward|forward_if]; try entailer!;convert_C_to_math;try entailer!;try solve_bounds.

Ltac forward_verify_check :=
  match goal with |- semax _ ?E _ _ =>
    forward_loop E continue:E break:E
  end;[entailer!|try (forward_if;[elimtype False|forward;entailer!])|forward;entailer|].