Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Require Import List.

Require Import divsteps.divsteps_def.
Require Import extraMath.
Require Import modinv.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

Definition Zodd_irr z (Hz1 Hz2 : Zodd z) : Hz1 = Hz2.
Proof.
revert Hz1 Hz2.
destruct z as [|p|p]; try destruct p; try contradiction; intros [] []; reflexivity.
Defined.

Module Step.

Inductive Step : Set :=
| D : Step
| S : Step
| H : Step.

End Step.
Definition Step := Step.Step.

Definition INC : Z := 1.

Record State : Set :=
 { delta : Z
 ; f : Z
 ; g : Z
 ; oddF : Zodd f
 }.

Definition eta (st : State) := Z.opp (delta st).

Definition init f g oddF :=
{| delta := 1
 ; f := f
 ; g := g
 ; oddF := oddF
 |}.

Definition step (st : State) : State * Step :=
match Zeven_odd_dec (g st) with
| left _ => ({| delta := INC + delta st
              ; f := f st
              ; g := g st / 2
              ; oddF := oddF st
              |}
            , Step.H)
| right oddG =>
    if (0 <? delta st)%Z
    then ({| delta := INC - delta st
           ; f := g st
           ; g := (g st - f st) / 2
           ; oddF := oddG
           |}
         , Step.D)
    else ({| delta := INC + delta st
           ; f := f st
           ; g := (g st + f st) / 2
           ; oddF := oddF st
           |}
         , Step.S)
end.

(* Last step is first in the list to facilitate matrix multiplication. *)
Fixpoint stepN (n : nat) : State -> State * list Step  :=
match n with
| O => fun st => (st, nil)
| (S n) => fun st =>
    let (st0, xs) := stepN n st in
    let (st1, x) := step st0 in
    (st1, x :: xs)
end.

Inductive Spec : State -> (State * Step) -> Set :=
| specH : forall d f' g', Spec {| delta := d; f := 2*f'+1; g := 2*g'; oddF := Zodd_2p_plus_1 f' |}
                               ({| delta := INC + d; f := 2*f'+1; g := g'; oddF := Zodd_2p_plus_1 f' |}, Step.H)
| specD : forall d f' g', Spec {| delta := Z.pos d; f := 2*f'+1; g := 2*g'+1; oddF := Zodd_2p_plus_1 f' |}
                               ({| delta := INC - Z.pos d; f := 2*g'+1; g := g' - f'; oddF := Zodd_2p_plus_1 g' |}, Step.D)
| specS : forall d f' g', (d <= 0) ->
                          Spec {| delta := d; f := 2*f'+1; g := 2*g'+1; oddF := Zodd_2p_plus_1 f' |}
                               ({| delta := INC + d; f := 2*f'+1; g := g' + f' + 1; oddF := Zodd_2p_plus_1 f' |}, Step.S).

Lemma spec st : Spec st (step st).
Proof.
destruct st as [d0 f0 g0 Hf0].
unfold step; cbn -[Z.div].
destruct (Zeven_odd_dec g0) as [Hg0|Hg0].
generalize Hf0.
apply Zodd_bool_iff in Hf0.
rewrite (Zdiv2_odd_eqn f0), Hf0.
rewrite (Zeven_div2 g0) by auto.
replace (2 * Z.div2 g0 / 2) with (Z.div2 g0) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
intros Hf0'.
replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
apply specH.
generalize Hf0 Hg0.
apply Zodd_bool_iff in Hf0.
apply Zodd_bool_iff in Hg0.
rewrite (Zdiv2_odd_eqn f0), Hf0.
rewrite (Zdiv2_odd_eqn g0), Hg0.
destruct (0 <? d0) eqn:Hd.
destruct d0; try solve [cbn in Hd; congruence].
replace (2 * Z.div2 g0 + 1 - (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 - Z.div2 f0) * 2) by ring.
rewrite Z.div_mul by lia.
intros Hf0' Hg0'.
replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
replace Hg0' with (Zodd_2p_plus_1 (Z.div2 g0)) by apply Zodd_irr.
apply specD.
replace (2 * Z.div2 g0 + 1 + (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 + Z.div2 f0 + 1) * 2) by ring.
rewrite Z.div_mul by lia.
intros Hf0' _.
replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
apply specS.
lia.
Qed.

Lemma etaBounds b n st : -b <= eta st < b ->
  -b - Z.of_nat n <= eta (fst (stepN n st)) < b + Z.of_nat n.
Proof.
induction n; simpl; [lia|].
destruct (stepN n st).
rewrite Zpos_P_of_succ_nat.
revert IHn.
elim (spec s); intros d f' g'; try generalize (Z.pos d); unfold eta; cbn; try lia.
Qed.

Lemma gHs n st : (2^(Z.of_nat n) | g st) ->
  g (fst (stepN n st)) = g st / 2^(Z.of_nat n).
Proof.
induction n;[intros;rewrite Z.div_1_r; reflexivity|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
simpl (fst _).
destruct (stepN n st).
intros Hg.
assert (Hdivide : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
apply Zdivide_mod in Hg.
apply (f_equal (fun x => x / 2 ^ (Z.of_nat n))) in Hg.
rewrite Z.mul_comm, Z.rem_mul_r, Z.mul_comm, Z_div_plus_full, Z.mod_div, Z.add_0_l in Hg by lia.
rewrite <- IHn in Hg by assumption.
destruct (spec s);
simpl in Hg;
try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
           discriminate].
simpl (g _).
simpl (g _) in IHn.
apply Z.mul_cancel_l with 2; try lia.
rewrite !(Z.mul_comm 2), <- Zdiv_Zdiv by lia.
rewrite <- IHn by assumption.
rewrite !(Z.mul_comm 2), Z.div_mul; lia.
Qed.

Lemma fHs n st : (2^(Z.of_nat n) | g st) ->
  f (fst (stepN n st)) = f st.
Proof.
induction n;[intros; reflexivity|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
intros Hg.
simpl (fst _).
assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
apply Zdivide_mod in Hg.
apply (f_equal (fun x => x / 2 ^ (Z.of_nat n))) in Hg.
rewrite Z.mul_comm, Z.rem_mul_r, Z.mul_comm, Z_div_plus_full, Z.mod_div, Z.add_0_l in Hg by lia.
rewrite <- gHs in Hg by assumption.
destruct (stepN n st).
rewrite <- IHn by assumption.
destruct (spec s);
simpl in Hg;
try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
           discriminate].
reflexivity.
Qed.

Lemma etaHs n st : (2^(Z.of_nat n) | g st) ->
  eta (fst (stepN n st)) = eta st - (Z.of_nat n).
Proof.
induction n;[intros;cbn;ring|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
intros Hg.
simpl (fst _).
assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
apply Zdivide_mod in Hg.
apply (f_equal (fun x => x / 2 ^ (Z.of_nat n))) in Hg.
rewrite Z.mul_comm, Z.rem_mul_r, Z.mul_comm, Z_div_plus_full, Z.mod_div, Z.add_0_l in Hg by lia.
rewrite <- gHs in Hg by assumption.
destruct (stepN n st).
replace (eta st - _) with (eta st - (Z.of_nat n) - 1) by lia.
rewrite <- IHn by assumption.
destruct (spec s);
simpl in Hg;
try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
           discriminate].
unfold eta, INC.
simpl.
ring.
Qed.

Lemma etaSs n st : 0 <= eta st ->
       Z.of_nat n <= 1 + eta st ->
       eta (fst (stepN n st)) = eta st - Z.of_nat n.
Proof.
induction n;[intros;cbn;ring|].
rewrite Nat2Z.inj_succ, <- Z.add_1_l.
intros Heta Hn.
simpl (fst _).
destruct (stepN n st) as [s l].
transitivity (eta st - Z.of_nat n - 1);[|ring].
assert (Hs : eta (fst (s, l)) = eta st - Z.of_nat n) by (apply IHn; lia).
rewrite <- Hs.
unfold eta in *.
destruct (spec s); cbn; try ring.
cbn in Hs.
lia.
Qed.

Lemma stepN_app (n m : nat) st : stepN (n + m) st = let st1 := stepN m st in
  (fst (stepN n (fst st1)), snd (stepN n (fst st1)) ++ snd st1).
Proof.
induction n;[destruct (stepN _ _);reflexivity|].
cbn.
rewrite IHn.
cbn.
destruct (stepN n _).
cbn.
destruct (step s).
reflexivity.
Qed.

Lemma stepN_app_fst (n m : nat) st : fst (stepN (n + m) st) = fst (stepN n (fst (stepN m st))).
Proof.
rewrite stepN_app.
reflexivity.
Qed.

Lemma stepN_app_snd (n m : nat) st : snd (stepN (n + m) st) = 
  snd (stepN n (fst (stepN m st))) ++ snd (stepN m st).
Proof.
rewrite stepN_app.
reflexivity.
Qed.

Lemma etaDs n st : Zodd (g st) -> eta st < 0 ->
       0 < Z.of_nat n <= 1 - eta st ->
       eta (fst (stepN n st)) = -eta st - Z.of_nat n.
Proof.
intros Hodd Heta Hn.
destruct n;[lia|].
rewrite <- Nat.add_1_r.
rewrite stepN_app_fst.
simpl (stepN 1 st).
destruct (spec st);[elim (Zodd_not_Zeven _ Hodd); apply Zeven_2p| |unfold eta in *;cbn in *;lia].
rewrite etaSs; unfold eta in *; cbn in *; change (Z.pos_sub 1 d) with (1 - Z.pos d); try lia.
change (0 < Z.of_nat (S n) <= 1 - -(Z.pos d)) in Hn.
lia.
Qed.

Lemma stepN_mod n st1 st2 :
  eqm (2^Z.of_nat n) (f st1) (f st2) ->
  eqm (2^Z.of_nat n) (g st1) (g st2) ->
  delta st1 = delta st2 ->
  delta (fst (stepN n st1)) = delta (fst (stepN n st2)) /\
  snd (stepN n st1) = snd (stepN n st2).
Proof.
revert st1 st2.
induction n;[simpl;repeat split;congruence|].
intros st1 st2 Hf Hg Hdelta.
replace (S n) with (n + 1)%nat by lia.
rewrite !stepN_app_fst, !stepN_app_snd.
simpl (stepN 1 st1); simpl (stepN 1 st2).
unfold step; rewrite Hdelta.
assert (Hdiv2 : forall x y, eqm (2 ^ Z.of_nat (S n)) x y -> eqm (2 ^ Z.of_nat n) (x / 2) (y / 2)).
1:{
 intros x y.
 unfold eqm.
 rewrite <-!Z.land_ones, <-!(Z.shiftr_div_pow2 _ 1) by lia.
 replace (Z.of_nat n) with (Z.of_nat (S n) - 1) by lia.
 rewrite <-!extraMath.Z_shiftr_ones, <-!Z.shiftr_land by lia.
 congruence.
}
destruct (Zeven_odd_dec (g st1)); destruct (Zeven_odd_dec (g st2)); 
try solve
[exfalso;
rewrite <-?Zeven_bool_iff, <-?Zodd_bool_iff, ?Zeven_mod, ?Zodd_mod in *;
apply Zeq_bool_eq in z, z0;
apply (extraMath.eqm_2_pow_le 1) in Hg; try lia;
change (2^1) with 2 in *;
rewrite Hg in z;
congruence
];[|destruct (0 <? delta st2)];cbn;
  set (st1' := Build_State _ _ _ _);
  set (st2' := Build_State _ _ _ _);
  destruct (IHn st1' st2');
  try solve [cbn; lia|split; congruence].
* eapply extraMath.eqm_2_pow_le;[|apply Hf]; lia.
* apply Hdiv2; apply Hg.
* eapply extraMath.eqm_2_pow_le;[|apply Hg]; lia.
* apply Hdiv2; apply Zminus_eqm; assumption.
* eapply extraMath.eqm_2_pow_le;[|apply Hf]; lia.
* apply Hdiv2; apply Zplus_eqm; assumption.
Qed.

Lemma fStepBounds st : Z.abs (f (fst (step st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
destruct (spec st); cbn;lia.
Qed.

Lemma gStepBounds st : 2 * Z.abs (g (fst (step st))) <= Z.abs (f st) + Z.abs (g st).
Proof.
destruct (spec st); cbn;lia.
Qed.

Lemma fgBounds st n :
 Z.abs (f (fst (stepN n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)) /\
 Z.abs (g (fst (stepN n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
induction n;[cbn; lia|].
cbn.
assert (Hf := fStepBounds (fst (stepN n st))).
assert (Hg := gStepBounds (fst (stepN n st))).
destruct (stepN n st) as [st' xs].
cbn in *.
destruct (step st') as [st'' xs'].
cbn in *.
lia.
Qed.

Lemma fgBoundsStrict st n :
 Z.abs (g st) < Z.abs (f st) ->
 Z.abs (f (fst (stepN n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)) /\
 Z.abs (g (fst (stepN n st))) < Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
induction n;[cbn; lia|].
cbn.
assert (Hf := fStepBounds (fst (stepN n st))).
assert (Hg := gStepBounds (fst (stepN n st))).
destruct (stepN n st) as [st' xs].
cbn in *.
destruct (step st') as [st'' xs'].
cbn in *.
lia.
Qed.

Lemma fixed st n : g st = 0 ->
 f (fst (stepN n st)) = f st /\ g (fst (stepN n st)) = 0.
Proof.
intros Hg.
induction n;[auto|].
cbn.
destruct (stepN n st) as [[eta f g Hf] l].
unfold step.
cbn in *.
destruct IHn as [-> ->].
cbn.
auto.
Qed.

Lemma fixed_f st n : g st = 0 ->
 f (fst (stepN n st)) = f st.
Proof.
intros Hg.
destruct (fixed st n Hg).
assumption.
Qed.

Lemma fixed_g st n : g st = 0 ->
 g (fst (stepN n st)) = 0.
Proof.
intros Hg.
destruct (fixed st n Hg).
assumption.
Qed.

Lemma gcd st d n : Zis_gcd (f st) (g st) d ->
 Zis_gcd (f (fst (stepN n st))) (g (fst (stepN n st))) d.
Proof.
intros Hgcd.
induction n;[auto|].
cbn.
destruct (stepN n st) as [st0 l].
cbn in IHn.
destruct (spec st0);cbn in *;
  revert IHn;
  apply Zis_gcd_ind;
  intros Hd1 Hd2 Hdx;
  apply Zis_gcd_intro; try assumption. 
* assert (Hodd : Z.odd d = true).
  1:{
    destruct Hd1 as [z1 Hd1].
    apply (f_equal Z.odd) in Hd1.
    rewrite Z.add_comm, Z.odd_add_mul_2, Z.mul_comm, Z.odd_mul in Hd1.
    destruct (Z.odd d);auto.
  }
  eapply Gauss;[apply Hd2|].
  apply rel_prime_mod_rev;[lia|].
  rewrite Zmod_odd, Hodd.
  apply rel_prime_1.
* intros x Hxf Hxg.
  apply Hdx; try assumption.
  auto with *.
* assert (Hodd : Z.odd d = true).
  1:{
    destruct Hd1 as [z1 Hd1].
    apply (f_equal Z.odd) in Hd1.
    rewrite Z.add_comm, Z.odd_add_mul_2, Z.mul_comm, Z.odd_mul in Hd1.
    destruct (Z.odd d);auto.
  }
  apply Gauss with 2.
  + replace (2 * (g' - f')) with ((2 * g' + 1) - (2 * f' + 1)) by ring.
    apply Z.divide_sub_r; assumption.
  + apply rel_prime_mod_rev;[lia|].
    rewrite Zmod_odd, Hodd.
    apply rel_prime_1.
* intros x Hxf Hxg.
  apply Hdx; try assumption.
  replace (2 * f' + 1) with ((2 * g' + 1) - (2*(g' - f'))) by ring.
  apply Z.divide_sub_r; try assumption.
  auto with *.
* assert (Hodd : Z.odd d = true).
  1:{
    destruct Hd1 as [z1 Hd1].
    apply (f_equal Z.odd) in Hd1.
    rewrite Z.add_comm, Z.odd_add_mul_2, Z.mul_comm, Z.odd_mul in Hd1.
    destruct (Z.odd d);auto.
  }
  apply Gauss with 2.
  + replace (2 * (g' + f' + 1)) with ((2 * g' + 1) + (2 * f' + 1)) by ring.
    apply Z.divide_add_r; assumption.
  + apply rel_prime_mod_rev;[lia|].
    rewrite Zmod_odd, Hodd.
    apply rel_prime_1.
* intros x Hxf Hxg.
  apply Hdx; try assumption.
  replace (2 * g' + 1) with ((2*(g' + f' + 1)) - (2 * f' + 1)) by ring.
  apply Z.divide_sub_r; try assumption.
  auto with *.
Qed.

Lemma Translate_divsteps n fi gi (Hf : Zodd fi) :
 delta (fst (stepN n (init fi gi Hf))) = divsteps.delta (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)) /\
 f (fst (stepN n (init fi gi Hf))) = divsteps.f (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)) /\
 g (fst (stepN n (init fi gi Hf))) = divsteps.g (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
Proof.
induction n;[cbn;auto|].
destruct IHn as [IHdelta [IHf IHg]].
rewrite Nnat.Nat2N.inj_succ, N.iter_succ.
destruct (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
simpl.
destruct (stepN n (init fi gi Hf)) as [st0 l].
simpl in *.
subst delta0 f0 g0.
destruct (spec st0);
unfold divsteps.step; cbn -[Z.div].
* rewrite Z.even_mul; cbn -[Z.div].
  rewrite (Z.mul_comm 2 g'), Z.div_mul; lia.
* rewrite Z.add_comm, Z.even_add_mul_2; cbn -[Z.div].
  repeat (split;try reflexivity).
  replace (1 + 2 * g' - (2 * f' + 1)) with ((g' - f') * 2) by ring.
  rewrite Z.div_mul; lia.
* rewrite (Z.add_comm _ 1), Z.even_add_mul_2; cbn -[Z.div].
  elim Z.ltb_spec;[lia|intros _];cbn -[Z.div].
  repeat (split;try reflexivity).
  replace (1 + 2 * g' + (2 * f' + 1)) with ((g' + f' + 1) * 2) by ring.
  rewrite Z.div_mul; lia.
Qed.

Lemma Translate_divsteps_g n fi gi (Hf : Zodd fi) :
 g (fst (stepN n (init fi gi Hf))) = divsteps.g (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
Proof.
destruct (Translate_divsteps n fi gi Hf).
tauto.
Qed.

Module Trans.

Record V2 :=
{ x : Z; y : Z }.

Definition scale (c : Z) (vec : V2) :=
{| x := c * (x vec)
 ; y := c * (y vec)
|}.

Lemma scale_mul c1 c2 vec : scale (c1 * c2) vec = scale c1 (scale c2 vec).
Proof.
destruct vec.
unfold scale; simpl; f_equal; ring.
Qed.

Record M2x2 :=
{ u : Z; v : Z; q : Z; r : Z}.

Definition I : M2x2 :=
{| u := 1
 ; v := 0
 ; q := 0
 ; r := 1
|}.

Definition ap (m : M2x2) (vec : V2) : V2 :=
{| x := (u m) * (x vec) + (v m) * (y vec)
 ; y := (q m) * (x vec) + (r m) * (y vec)
|}.

Lemma ap_scale m c vec : ap m (scale c vec) = scale c (ap m vec).
Proof.
destruct m, vec.
unfold ap, scale; simpl; f_equal; ring.
Qed.

Definition mul (m1 m2: M2x2) : M2x2 :=
{| u := (u m1) * (u m2) + (v m1) * (q m2)
 ; v := (u m1) * (v m2) + (v m1) * (r m2)
 ; q := (q m1) * (u m2) + (r m1) * (q m2)
 ; r := (q m1) * (v m2) + (r m1) * (r m2)
|}.

Lemma mul_assoc m1 m2 m3 : mul m1 (mul m2 m3) = mul (mul m1 m2) m3.
Proof.
destruct m1, m2, m3.
unfold mul; simpl; f_equal; ring.
Qed.

Lemma ap_mul m1 m2 vec : ap (mul m1 m2) vec = ap m1 (ap m2 vec).
Proof.
destruct m1, m2, vec.
unfold ap, mul; simpl; f_equal; ring.
Qed.

Definition det (m: M2x2) : Z := (u m) * (r m) - (v m) * (q m).

Lemma det_mul m1 m2 : det (mul m1 m2) = det m1 * det m2.
Proof.
destruct m1, m2.
cbn.
ring.
Qed.

Definition prod : list M2x2 -> M2x2 := fold_right mul I.

Lemma prod_app l1 l2 : prod (l1 ++ l2) = mul (prod l1) (prod l2).
Proof.
induction l1.
1:cbn; destruct (prod l2); unfold mul; cbn; f_equal; ring.
cbn.
rewrite IHl1.
destruct (prod l1); destruct (prod l2); unfold mul; cbn; f_equal; ring.
Qed.

Lemma det_prod ms : det (prod ms) = fold_right Z.mul 1 (map det ms).
Proof.
induction ms; try reflexivity.
simpl.
rewrite det_mul.
congruence.
Qed.

Definition bounded (b : Z) (m : M2x2) :=
  (Z.abs (u m) + Z.abs (v m) <= b /\ -b < u m + v m) /\
  (Z.abs (q m) + Z.abs (r m) <= b /\ -b < q m + r m).

Lemma bounded_I : bounded 1 I.
Proof.
unfold bounded.
simpl.
lia.
Qed.

Definition trans (s : Step) : M2x2 :=
match s with
| Step.H => {| u := 2; v := 0; q := 0; r := 1 |}
| Step.D => {| u := 0; v := 2; q := -1; r := 1 |}
| Step.S => {| u := 2; v := 0; q := 1; r := 1 |}
end.

Definition fg st := {| x := f st; y := g st |}.

Lemma trans_step st :
  scale 2 (fg (fst (step st))) = ap (trans (snd (step st))) (fg st).
Proof.
destruct (spec st);
unfold scale,ap, fg; cbn;
f_equal; ring.
Qed.

Lemma det_trans s : det (trans s) = 2.
Proof.
destruct s; reflexivity.
Qed.

Lemma bounded_mul_trans b m s : bounded b m -> bounded (2*b) (mul (trans s) m).
Proof.
destruct m as [u v q r].
intros [Huv Hqr]; simpl in *.
destruct s; unfold bounded; simpl; lia.
Qed.

Definition transN (n : nat) (st : State) : M2x2 :=
  prod (map trans (snd (stepN n st))).

Lemma transN_S n st : {x | transN (S n) st = mul (trans x) (transN n st)}.
Proof.
unfold transN.
simpl.
destruct (stepN n st) as [st0 xs] eqn:Hxs.
destruct (step st0) as [st1 x].
exists x.
reflexivity.
Qed.

Lemma transN_step n st :
  scale (2^(Z.of_nat n)) (fg (fst (stepN n st))) = ap (transN n st) (fg st).
Proof.
induction n.
 rewrite Z.pow_0_r.
 destruct st; unfold scale, fg, ap; cbn.
 f_equal; ring.
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
unfold transN in *.
simpl.
destruct (stepN n st) as [st0 xs]; simpl in *.
assert (Htrans := trans_step st0).
destruct (step st0) as [st1 x]; simpl in *.
rewrite ap_mul, <- IHn, ap_scale, Z.mul_comm, scale_mul by auto.
f_equal.
apply Htrans.
Qed.

Lemma det_transN n st : det (transN n st) = 2^(Z.of_nat n).
Proof.
revert st.
induction n; try reflexivity.
intros st.
destruct (transN_S n st) as [x ->].
rewrite det_mul, det_trans, Nat2Z.inj_succ, Z.pow_succ_r by lia.
congruence.
Qed.

Lemma bounded_transN n st : bounded (2^(Z.of_nat n)) (transN n st).
Proof.
induction n; try apply bounded_I.
destruct (transN_S n st) as [x ->].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
auto using bounded_mul_trans.
Qed.

Lemma transN_stepN (n m : nat) (st : State) :
  mul (transN n (fst (stepN m st))) (transN m st) = transN (n + m) st.
Proof.
unfold transN.
rewrite stepN_app_snd, map_app, prod_app.
reflexivity.
Qed.

Lemma transHs n st : (2^(Z.of_nat n) | g st) ->
  transN n st = {| u := 2^(Z.of_nat n); v := 0; q := 0; r := 1 |}.
Proof.
induction n;[intros; reflexivity|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
intros Hg.
unfold transN in *.
simpl (snd _).
assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
apply Zdivide_mod in Hg.
apply (f_equal (fun x => x / 2 ^ (Z.of_nat n))) in Hg.
rewrite Z.mul_comm, Z.rem_mul_r, Z.mul_comm, Z_div_plus_full, Z.mod_div, Z.add_0_l in Hg by lia.
rewrite <- gHs in Hg by assumption.
destruct (stepN n st).
transitivity (mul (trans Step.H) {| u := 2^(Z.of_nat n); v := 0; q := 0; r := 1 |}).
2:unfold mul;cbn;f_equal; ring.
rewrite <- IHn by assumption.
destruct (spec s);
simpl in Hg;
try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
           discriminate].
reflexivity.
Qed.

Lemma transSs n st : delta st <= 0 -> Z.of_nat n <= 1 - delta st ->
  transN n st = {| u := 2^(Z.of_nat n); v := 0;
    q := (modInv (-f st) (2^(Z.of_nat n)) * g st) mod (2^(Z.of_nat n)); r := 1 |}.
Proof.
intros Hdelta Hn.
assert (Hrel_prime : rel_prime (f st) 2).
1:{
  apply rel_prime_mod_rev; try lia.
  assert (Hfodd := oddF st).
  apply <- Zodd_bool_iff in Hfodd.
  rewrite Zmod_odd, Hfodd.
  apply rel_prime_1.
}
assert (Hgcd : forall x, 0 <= x -> Z.gcd (f st) (2 ^ x) = 1).
1:{
  intros x Hx.
  apply Zgcd_1_rel_prime.
  apply Zpow_facts.rel_prime_Zpower_r; try lia.
  assumption.
}
replace ((modInv (-f st) (2 ^ Z.of_nat n)
                     * g st) mod 2 ^ Z.of_nat n)
 with ((-modInv (f st) (2 ^ Z.of_nat n)
                     * g st) mod 2 ^ Z.of_nat n).
2:{
  apply Zmult_eqm;[|reflexivity].
  unfold eqm.
  symmetry.
  rewrite <- (Z.mul_1_l (modInv _ _)).
  rewrite <- (Hgcd (Z.of_nat n)), <- Zmult_mod_idemp_l, <- modInv_mul_l, Zmult_mod_idemp_l, <- Z.mul_assoc by lia.
  rewrite <- (Z.opp_involutive (f st)) at 2.
  rewrite Z.mul_opp_l, Z.mul_opp_r, <- Z.mul_opp_l.
  rewrite <- Zmult_mod_idemp_r, modInv_mul_r, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_r by lia.
  rewrite Z.mul_1_r.
  reflexivity.
}
set (w := _ mod _).
apply proj1 with ( (2^(Z.of_nat n) | f st * w + g st)
                /\ (delta (fst (stepN n st)) = Z.of_nat n + delta st)).
revert w Hn; induction n; intros w Hn;
[repeat split;[unfold w;rewrite Z.mod_1_r;reflexivity|apply Z.divide_1_l]|].
destruct IHn as [IHn1 [IHn2 IHn3]];[lia|].
rewrite <- (transN_stepN 1 n), IHn1.
change (stepN (S n) st) with (stepN (1 + n) st).
rewrite stepN_app.
unfold transN.
simpl (fst (_,_)).
simpl (stepN 1 _).
set (st' := fst _).
assert (Hst' := eq_refl st').
revert Hst'.
unfold st' at 2.
assert (Hbound : forall a, 0 <= a mod 2 ^ Z.of_nat n < 2 ^ Z.of_nat n) by
 auto using Z.mod_pos_bound with *.

assert (Hdivide: (2 ^ Z.of_nat (S n) | f st * w + g st)).
1:{
  apply Z.mod_divide; try lia.
  unfold w.
  rewrite <- Zplus_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_assoc,
          Z.mul_opp_r, Z.mul_opp_l, <-Z.mul_opp_r,
          <- Zmult_mod_idemp_l, modInv_mul_r.
  replace (Z.gcd _ _) with 1.
  2:{
   symmetry.
   apply Zgcd_1_rel_prime. 
   apply Zpow_facts.rel_prime_Zpower_r; try lia.
   assumption.
  }
  rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_l.
  ring_simplify (1 * -g st + g st).
  reflexivity.
}
elim (spec);intros d f' g' Hst'.
* repeat split.
  + replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia.
    unfold mul; cbn.
    f_equal; try ring.
    ring_simplify.
    unfold w.
    symmetry.
    apply Zdivide_mod_minus.
    - specialize (Hbound ((-modInv (f st) (2 ^ Z.of_nat n) * g st))).
      replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
      rewrite Z.pow_add_r; lia.
    - set (w0 := (-modInv (f st) (2 ^ Z.of_nat n) * g st) mod 2 ^ Z.of_nat n) in *.
      apply Z.mod_divide; try lia.
      rewrite <- Zminus_mod_idemp_r.
      replace w0 with (1 * w0) by ring.
      rewrite <- Zmult_mod_idemp_l, <- (Hgcd (Z.of_nat (S n))) by lia.
      rewrite <- modInv_mul_l, Zmult_mod_idemp_l, Zminus_mod_idemp_r.
      replace (-modInv (f st) (2 ^ Z.of_nat (S n)) * g st
       - modInv (f st) (2 ^ Z.of_nat (S n))
       * f st
       * w0) with
       (-modInv (f st) (2 ^ Z.of_nat (S n)) *
        (w0 * f st + 1 * g st))
       by ring.
      assert (HtransN := transN_step n st).
      rewrite <- Hst', IHn1 in HtransN.
      unfold fg, scale, ap in HtransN.
      simpl in HtransN.
      injection HtransN; clear HtransN.
      intros Hg' Hf'.
      rewrite <- Hg'.
      replace (2 ^ Z.of_nat n * (2 * g')) with (g' * (2 ^ Z.of_nat n * 2^1)) by ring.
      rewrite <- Z.pow_add_r, Z.mul_assoc by lia.
      replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
      apply Z_mod_mult.
  + assumption.
  + replace (Z.of_nat (S n) + delta st)
    with (1 + (Z.of_nat n + delta st)) by lia.
    rewrite <- IHn3.
    simpl.
    rewrite <- Hst'.
    reflexivity.
* rewrite <- Hst' in IHn3.
  unfold delta at 1 in IHn3.
  lia.
* repeat split.
  + replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia.
    unfold mul; cbn.
    f_equal; try ring.
    ring_simplify.
    unfold w.
    symmetry.
    apply Zdivide_mod_minus.
    - specialize (Hbound ((-modInv (f st) (2 ^ Z.of_nat n) * g st))).
      replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
      rewrite Z.pow_add_r; lia.
    - set (w0 := (-modInv (f st) (2 ^ Z.of_nat n) * g st) mod 2 ^ Z.of_nat n) in *.
      apply Z.mod_divide; try lia.
      rewrite <- Zminus_mod_idemp_r.
      replace (2 ^ Z.of_nat n + w0) with (1 * (2 ^ Z.of_nat n + w0)) by ring.
      rewrite <- Zmult_mod_idemp_l, <- (Hgcd (Z.of_nat (S n))) by lia.
      rewrite <- modInv_mul_l, Zmult_mod_idemp_l, Zminus_mod_idemp_r.
      replace (-modInv (f st) (2 ^ Z.of_nat (S n)) * g st
   - modInv (f st) (2 ^ Z.of_nat (S n)) * f st
       * (2 ^ Z.of_nat n + w0)) with
       (-modInv (f st) (2 ^ Z.of_nat (S n)) *
        (2 ^ Z.of_nat n * f st + 0 * g st + (w0 * f st + 1 * g st)))
       by ring.
      assert (HtransN := transN_step n st).
      rewrite <- Hst'0, IHn1 in HtransN.
      unfold fg, scale, ap in HtransN;
      simpl in HtransN.
      injection HtransN; clear HtransN.
      intros Hg' Hf'.
      rewrite <- Hg', <- Hf'.
      replace (2 ^ Z.of_nat n * (2 * f' + 1) + 2 ^ Z.of_nat n * (2 * g' + 1))
         with ((f' + g' + 1) * (2 ^ Z.of_nat n * 2^1)) by ring.
      rewrite <- Z.pow_add_r, Z.mul_assoc by lia.
      replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
      apply Z_mod_mult.
  + assumption.
  + replace (Z.of_nat (S n) + delta st)
    with (1 + (Z.of_nat n + delta st)) by lia.
    rewrite <- IHn3.
    simpl.
    rewrite <- Hst'0.
    reflexivity.
Qed.

Lemma transDs n st : Zodd (g st) -> 0 < delta st -> 0 < Z.of_nat n <= 1 + delta st ->
  transN n st = {| u := 0; v := 2^(Z.of_nat n); 
    q := -1; r := (modInv (-g st) (2^(Z.of_nat n)) * (-f st)) mod (2^(Z.of_nat n)) |}.
Proof.
intros Hodd Hdelta [Hn0 Hn].
destruct n;[lia|].
rewrite <- Nat.add_1_r, <- transN_stepN.
unfold transN at 2; cbn.
revert Hodd Hdelta Hn.
elim (spec);cbn;intros d f' g' Hodd Hdelta Hn;
[elim (Zeven_not_Zodd _ (Zeven_2p _) Hodd)| |lia].
change (Z.of_nat (S n) <= 1 + Z.pos d) in Hn.
change (Z.pos_sub 1 d) with (1 - Z.pos d).
set (dZ := Z.pos d) in *; clearbody dZ; clear d.
change (mul {| u := 0; v := 2; q := -1; r := 1 |} I)
 with (mul (trans Step.S) {| u := 0; v := 1; q := -1; r := 0 |}).
rewrite !mul_assoc.
clear st.
pose (st0 := {| delta := - dZ;
                f := 2 * g' + 1;
                g := - 2 * f' - 1;
                oddF := Zodd_2p_plus_1 g' |}).
set (st1 := Build_State _ _ _ _).
assert (Hst01 : step st0 = (st1, Step.S)).
1:{
  unfold step.
  assert (Hoddg : Zodd (g st0)) by
   (replace (g st0) with (2*(-f' - 1) + 1) by (cbn;ring); apply Zodd_2p_plus_1).
  destruct Zeven_odd_dec as [Heveng'|Hoddg'];
  [elim (Zodd_not_Zeven _ Hoddg Heveng')|].
  elim (Z.ltb_spec); intros Hd0; cbn in Hd0; try lia.
  simpl (g st0 + f st0).
  replace (-2 * f' - 1 + (2 * g' + 1)) with ((g' - f')*2) by ring.
  rewrite Z_div_mult by lia.
  reflexivity.
}
replace (trans Step.S) with (transN 1 st0)
 by (unfold transN;cbn;rewrite Hst01;reflexivity).
replace st1 with (fst (stepN 1 st0)) by (unfold transN;cbn;rewrite Hst01;reflexivity).
rewrite transN_stepN, transSs; cbn; try lia.
unfold mul; cbn.
f_equal; try ring.
ring_simplify.
do 1 f_equal.
ring.
Qed.

End Trans.

Definition pre_div62Modulo (M a : Z) : Z :=
  a - (((modInv M (2^62))*a) mod 2^62) * M.

Lemma pre_div62Modulo_mod (M a : Z) : pre_div62Modulo M a mod M = a mod M.
Proof.
unfold pre_div62Modulo, Z.sub.
rewrite <- Z.mul_opp_l.
apply Z_mod_plus_full.
Qed.

Lemma pre_div62Modulo_divide M a : Zodd M -> (2^62 | pre_div62Modulo M a).
Proof.
intros HM.
apply Z.mod_divide;[lia|].
unfold pre_div62Modulo.
rewrite <- Zminus_mod_idemp_r, Zmult_mod_idemp_l.
replace (modInv M (2 ^ 62) * a * M) with (modInv M (2 ^ 62) * M * a) by ring.
rewrite <- Zmult_mod_idemp_l, modInv_mul_l.
replace (Z.gcd M (2 ^ 62)) with 1;
[rewrite Z.mul_1_l, Zminus_mod_idemp_r, Z.sub_diag; reflexivity|].
symmetry.
apply Zgcd_1_rel_prime.
apply Zpow_facts.rel_prime_Zpower_r;[lia|].
apply Zgcd_1_rel_prime.
apply Z.bezout_1_gcd.
apply Zodd_ex_iff in HM.
destruct HM as [m HMm].
exists 1; exists (-m).
lia.
Qed.

Definition update_de (M d e : Z) (mtx : Trans.M2x2) : (Z * Z) :=
  let vec := Trans.ap mtx
              {| Trans.x := d + if d <? 0 then M else 0
               ; Trans.y := e + if e <? 0 then M else 0
               |} in
  ( pre_div62Modulo M (Trans.x vec) / 2^62
  , pre_div62Modulo M (Trans.y vec) / 2^62
  ).

Lemma update_de_bound m d e mtx : Zodd m ->
   Z.abs (Trans.u mtx) + Z.abs (Trans.v mtx) <= 2 ^ 62 ->
   Z.abs (Trans.q mtx) + Z.abs (Trans.r mtx) <= 2 ^ 62 ->
   -2 * m < d < m -> -2 * m < e < m ->
   -2 * m < fst (update_de m d e mtx) < m /\ -2 * m < snd (update_de m d e mtx) < m.
Proof.
intros Hoddm Huv Hqr Hmd Hme.
unfold update_de.
set (x := Trans.x _).
set (y := Trans.y _).
assert (Hm1 : 1 <= m) by lia.
assert (Hxbound : Z.abs x <= 2^62 * (m - 1)).
1:{
  cbn.
  eapply Z.le_trans;[apply Z.abs_triangle|].
  rewrite !Z.abs_mul.
  apply Z.le_trans with ((Z.abs (Trans.u mtx) + Z.abs (Trans.v mtx))*(m - 1));[|nia].
  destruct (Z.ltb_spec0 d 0); destruct (Z.ltb_spec0 e 0);
  rewrite Z.mul_add_distr_r; apply Z.add_le_mono; apply Zmult_le_compat_l; lia.
}
assert (Hybound : Z.abs y <= 2^62 * (m - 1)).
1:{
  cbn.
  eapply Z.le_trans;[apply Z.abs_triangle|].
  rewrite !Z.abs_mul.
  apply Z.le_trans with ((Z.abs (Trans.q mtx) + Z.abs (Trans.r mtx))*(m - 1));[|nia].
  destruct (Z.ltb_spec0 d 0); destruct (Z.ltb_spec0 e 0);
  rewrite Z.mul_add_distr_r; apply Z.add_le_mono; apply Zmult_le_compat_l; lia.
}
cbn -[Z.div Z.pow x y].
unfold pre_div62Modulo.
assert (Hxmod : 0 <= (modInv m (2 ^ 62) * x) mod 2 ^ 62 < 2^62) by (apply Z.mod_pos_bound;lia).
assert (Hymod : 0 <= (modInv m (2 ^ 62) * y) mod 2 ^ 62 < 2^62) by (apply Z.mod_pos_bound;lia).
rewrite <- !Z.shiftr_div_pow2 by lia.
split.
* cut (-2*m + 1 <= Z.shiftr (x - (modInv m (2 ^ 62) * x) mod 2 ^ 62 * m) 62 < m);[lia|apply shiftr_bounds;nia].
* cut (-2*m + 1 <= Z.shiftr (y - (modInv m (2 ^ 62) * y) mod 2 ^ 62 * m) 62 < m);[lia|apply shiftr_bounds;nia].
Qed.

Lemma update_de_eqm m x d e st : Zodd m ->
  eqm m (x * d) (f st) ->
  eqm m (x * e) (g st) ->
  eqm m (x * fst (update_de m d e (Trans.transN 62 st))) (f (fst (stepN 62 st))) /\
  eqm m (x * snd (update_de m d e (Trans.transN 62 st))) (g (fst (stepN 62 st))).
Proof.
intros Hoddm Hf Hg.
unfold update_de.
generalize (fun a => pre_div62Modulo_divide m a Hoddm).
generalize (pre_div62Modulo_mod m).
generalize (Trans.transN_step 62 st).
change (2^62) with (2^Z.of_nat 62).
generalize 62%nat; intros n.
intros X; injection X; clear X.
intros Hgqr Hfuv Hpre1 Hpre2.
destruct (Trans.transN n st) as [u v q r].
cbn -[Z.div pre_div62Modulo] in *.
assert (Hn : 0 < 2^Z.of_nat n) by lia.
assert (Hinv : modInv (2^Z.of_nat n) m * (2^Z.of_nat n) mod m = 1 mod m).
1:{
  rewrite modInv_mul_l.
  f_equal.
  rewrite Zgcd_1_rel_prime.
  apply rel_prime_sym.
  apply Zpow_facts.rel_prime_Zpower_r;[lia|].
  apply rel_prime_sym.
  apply prime_rel_prime;[apply prime_2|].
  rewrite Zodd_equiv in Hoddm.
  destruct Hoddm as [b ->].
  intros Hdivide.
  apply (Z.divide_add_cancel_r _ _ _ (Z.divide_factor_l _ _)) in Hdivide.
  apply Z.divide_1_r_abs in Hdivide.
  discriminate.
}
unfold eqm.
rewrite <- !(Zmult_mod_idemp_l x).
replace x with (x*1) by ring.
rewrite <- !(Zmult_mod_idemp_r 1), <-Hinv, !Zmult_mod_idemp_r, !Zmult_mod_idemp_l.
rewrite <-!Z.mul_assoc, <-!Zdivide_Zdiv_eq by auto.
rewrite !Z.mul_assoc, <-!(Zmult_mod_idemp_r (pre_div62Modulo m _)), !Hpre1.
assert (Hab : forall a b, eqm m (a * (d + (if d <? 0 then m else 0)) + b * (e + (if e <? 0 then m else 0))) (a*d + b*e)).
1:{
 intros a b.
 apply Zplus_eqm;apply Zmult_eqm;try apply eqm_refl;destruct (Z.ltb _ _);unfold eqm;
  rewrite <-Zplus_mod_idemp_r, ?Z_mod_same_full, ?Zmod_0_l;f_equal;try ring.
}
rewrite !Hab, !Zmult_mod_idemp_r.
rewrite !(Z.mul_comm (x * _)), !Z.mul_assoc, !(Z.mul_add_distr_r _ _ x).
rewrite <-!Z.mul_assoc, !(Z.mul_comm _ x).
rewrite <-!(Zmult_mod_idemp_l (_ + _)), !(Zplus_mod (_ * (x * d))), <- !(Zmult_mod_idemp_r (x * _)).
rewrite Hf, Hg, !Zmult_mod_idemp_r, <-!Zplus_mod, !Zmult_mod_idemp_l.
rewrite !(Z.mul_comm (_ + _)), <-Hfuv, <-Hgqr, !Z.mul_assoc.
rewrite <-!(Zmult_mod_idemp_l (_ * _)), Hinv, !Zmult_mod_idemp_l, !Z.mul_1_l.
auto.
Qed.