Require Import NArith.
Require Import Util.List.

Require Import Simplicity.Alg.
Require Import Simplicity.Core.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Translate.
Require Import Simplicity.Ty.

Local Open Scope N_scope.

Module StateShape.
(* In this section we prove that executing Simplicity programs on the Bit
 * Machine starting from *any* state, preserves the shape of the state if it
 * doesn't crash or halt.
 * Although spec allows for starting from the Halted state, any program
 * starting from the Halted state must end in the Halted state, which will
 * violating the assumptions of spec that it doesn't end in the Halted state.
 * Hence this scenario vacuously sastifies the spec.
 *)

Definition spec {A B : Ty} (t : Term A B) :=
  forall s0 (s1 : RunState),
   s0 >>- (@Core.eval _ _ t Naive.translate) ->> s1 ->
   stateShape s0 = stateShape s1.

Lemma iden_spec {A : Ty} : spec (@iden A).
Proof.
intros s0 s1.
apply stateShape_copy.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) :
 spec s -> spec t -> spec (comp s t) .
Proof.
intros Hs Ht s0 s5 Hs05.
simpl in Hs05.
apply seq_complete in Hs05.
destruct Hs05 as [s4 Hs04 Hs45].
apply seq_complete in Hs04.
destruct Hs04 as [s3 Hs03 Hs34].
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
pose (inv := dropFrame_complete Hs45);inversion inv as [s4' s5' Hs45'|]; clear inv Hs45.
subst s4; subst s5.
apply Ht in Hs34.
destruct s3 as [|s3];[discriminate|].
pose (inv := moveFrame_complete Hs23);inversion inv as [s2' s3' Hs23'|]; clear inv Hs23.
subst s2; subst s3.
apply Hs in Hs12.
destruct s1 as [|s1];[discriminate|].
pose (inv := newFrame_complete Hs01);inversion inv as [s0' s1' Hs01'|]; clear inv Hs01.
subst s0; subst s1.
revert Hs12 Hs34.
inversion_clear Hs01'.
inversion_clear Hs23'.
inversion_clear Hs45'.
clear.
unfold stateShape, runStateShape; cbn.
do 2 inversion 1.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (@unit A).
Proof.
intros x y Hxy.
cbn in Hxy.
apply nop_complete in Hxy.
congruence.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) :
 spec t -> spec (@injl A B C t).
Proof.
intros Ht s0 s3 Hs03.
simpl in Hs03.
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
rewrite (stateShape_write _ _ _ Hs01).
rewrite (stateShape_skip _ _ _ Hs12).
apply (Ht _ _ Hs23).
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@injr A B C t).
Proof.
intros Ht s0 s3 Hs03.
simpl in Hs03.
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
rewrite (stateShape_write _ _ _ Hs01).
rewrite (stateShape_skip _ _ _ Hs12).
apply (Ht _ _ Hs23).
Qed.

Lemma bump_spec {A B : Ty} (t : Term A B) n (Ht : spec t) x (y : RunState) :
 x >>- bump n (@Core.eval _ _ t Naive.translate) ->> y ->
 stateShape x = stateShape y.
Proof.
unfold bump.
intros Hxy.
apply seq_complete in Hxy.
destruct Hxy as [s2 Hxs2 Hs2y].
apply seq_complete in Hxs2.
destruct Hxs2 as [s1 Hxs1 Hs1s2].
rewrite (stateShape_fwd _ _ _ Hxs1).
destruct s2 as [|s2].
 pose (inv := runHalt (trace Hs2y));inversion inv.
rewrite (Ht _ _ Hs1s2).
apply (stateShape_bwd _ _ _ Hs2y).
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) :
 spec s -> spec t -> spec (case s t).
Proof.
intros Hs Ht x y Hxy.
simpl in Hxy.
remember (Running y) as y'.
revert Heqy'; pattern x; pattern y; revert x y' Hxy.
apply choice_complete;[intros x y' [|] Hb Hxy ->|discriminate];
eauto using bump_spec.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) :
 spec s -> spec t -> spec (pair s t).
Proof.
intros Hs Ht x z Hxz.
simpl in Hxz.
apply seq_complete in Hxz.
destruct Hxz as [y Hxy Hyz].
destruct y as [|y].
 pose (inv := runHalt (trace Hyz));inversion inv.
rewrite (Hs _ _ Hxy).
apply (Ht _ _ Hyz).
Qed.

Lemma take_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@take A B C t).
Proof.
auto.
Qed.

Lemma drop_spec {A B C : Ty} (t : Term B C) :
 spec t -> spec (@drop A B C t).
Proof.
intros Ht x y; cbn.
apply bump_spec.
assumption.
Qed.

Lemma Core_spec {A B : Ty} (t : Term A B) :
 spec t.
Proof.
induction t.
- apply iden_spec.
- apply comp_spec; assumption.
- apply unit_spec.
- apply injl_spec; assumption.
- apply injr_spec; assumption.
- apply case_spec; assumption.
- apply pair_spec; assumption.
- apply take_spec; assumption.
- apply drop_spec; assumption.
Qed.

End StateShape.

Lemma StateSize_Core A B (t : Term A B) s0 s1 :
  s0 >>- @Core.eval _ _ t Naive.translate ->> s1 -> stateSize s1 <= stateSize s0.
Proof.
intros H01.
destruct s1 as [|s1];[apply N.le_0_l|].
unfold stateSize.
rewrite (StateShape.Core_spec _ _ _ H01).
reflexivity.
Qed.

Module MaximumMemory.

Definition extraMemoryBound : Core.Algebra := Core.Pack (Core.Class.Class (fun A B => N)
  (fun A => 0)
  (fun A B C s t => N.of_nat (bitSize B) + N.max s t)
  (fun A => 0)
  (fun A B C t => t)
  (fun A B C t => t)
  (fun A B C D s t => N.max s t)
  (fun A B C s t => N.max s t)
  (fun A B C t => t)
  (fun A B C t => t)
).

Definition MemoryBound {A B : Ty} (t : Term A B) x : N := stateSize x + (@Core.eval _ _ t extraMemoryBound).

Definition spec {A B : Ty} (t : Term A B)  :=
  forall x y (tr : x >>- (@Core.eval _ _ t Naive.translate) ->> y),
   maximumMemoryResidence (trace tr) <= MemoryBound t x.

Lemma iden_spec {A : Ty} : spec (@iden A).
Proof.
intros x y tr.
unfold MemoryBound.
cbn in *.
rewrite MMR_copy, N.add_0_r.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) :
 spec s -> spec t -> spec (comp s t) .
Proof.
intros Hs Ht s0 s5 tr05.
unfold MemoryBound.
cbn in *.
destruct (seq_complete _ _ _ _ tr05) as [s4 tr04 tr45].
rewrite (MMR_seq _ _ _ _ _ tr04 tr45 tr05).
destruct (seq_complete _ _ _ _ tr04) as [s3 tr03 tr34].
rewrite (MMR_seq _ _ _ _ _ tr03 tr34 tr04).
destruct (seq_complete _ _ _ _ tr03) as [s2 tr02 tr23].
rewrite (MMR_seq _ _ _ _ _ tr02 tr23 tr03).
destruct (seq_complete _ _ _ _ tr02) as [s1 tr01 tr12].
rewrite (MMR_seq _ _ _ _ _ tr01 tr12 tr02).
rewrite N.add_assoc.
rewrite MMR_newFrame, MMR_moveFrame, MMR_dropFrame.
transitivity (stateSize s1 + N.max (@Core.eval _ _ s extraMemoryBound) (@Core.eval _ _ t extraMemoryBound)).
 rewrite <- N.add_max_distr_l; do 2 rewrite <- N.max_assoc.
 apply N.max_le_compat.
  apply N.max_lub;[apply N.le_add_r|apply (Hs _ _ tr12)].
 transitivity (stateSize s2 + (@Core.eval _ _ t extraMemoryBound)).
  replace (stateSize s2) with (stateSize s3).
   transitivity (N.max (stateSize s3) (maximumMemoryResidence (trace tr34))).
    rewrite N.max_assoc.
    apply N.max_lub;[reflexivity|].
    etransitivity;[apply (StateSize_Core _ _ _ _ _ tr34)|apply N.le_max_l].
   apply N.max_lub;[apply N.le_add_r|apply (Ht _ _ tr34)].
  destruct (moveFrame_complete tr23) as [s2 s3 T23|];[|reflexivity].
  inversion T23;cbn.
  rewrite fullWriteFrame_size.
  ring.
 apply N.add_le_mono_r.
 apply (StateSize_Core _ _ _ _ _ tr12).
apply N.add_le_mono_r.
destruct (newFrame_complete tr01) as [s0 s1 T01|];[apply N.eq_le_incl|apply N.le_0_l].
inversion T01; cbn.
ring.
Qed.

Lemma unit_spec {A : Ty} : spec (@unit A).
Proof.
intros x y tr.
unfold MemoryBound.
cbn in *.
destruct (trace_subproof _ _ _ _ _); cbn.
rewrite N.add_0_r.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) :
 spec t -> spec (@injl A B C t).
Proof.
intros Ht s0 s3 tr03.
unfold MemoryBound.
cbn in *.
destruct (seq_complete _ _ _ _ tr03) as [s2 tr02 tr23].
rewrite (MMR_seq _ _ _ _ _ tr02 tr23 tr03).
destruct (seq_complete _ _ _ _ tr02) as [s1 tr01 tr12].
rewrite (MMR_seq _ _ _ _ _ tr01 tr12 tr02).
rewrite MMR_write, MMR_skip.
unfold stateSize.
rewrite (stateShape_write _ _ _ tr01), N.max_id, (stateShape_skip _ _ _ tr12).
apply N.max_lub.
 apply N.le_add_r.
apply Ht.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@injr A B C t).
Proof.
intros Ht s0 s3 tr03.
unfold MemoryBound.
cbn in *.
destruct (seq_complete _ _ _ _ tr03) as [s2 tr02 tr23].
rewrite (MMR_seq _ _ _ _ _ tr02 tr23 tr03).
destruct (seq_complete _ _ _ _ tr02) as [s1 tr01 tr12].
rewrite (MMR_seq _ _ _ _ _ tr01 tr12 tr02).
rewrite MMR_write, MMR_skip.
unfold stateSize.
rewrite (stateShape_write _ _ _ tr01), N.max_id, (stateShape_skip _ _ _ tr12).
apply N.max_lub.
 apply N.le_add_r.
apply Ht.
Qed.

Lemma bump_spec {A B : Ty} (t : Term A B) (Ht : spec t) x y n (tr : x >>- bump n (@Core.eval _ _ t Naive.translate) ->> y) :
   maximumMemoryResidence (trace tr) <= MemoryBound t x.
Proof.
unfold bump in tr.
destruct (seq_complete _ _ _ _ tr) as [s2 tr02 tr23].
rewrite (MMR_seq _ _ _ _ _ tr02 tr23).
destruct (seq_complete _ _ _ _ tr02) as [s1 tr01 tr12].
rewrite (MMR_seq _ _ _ _ _ tr01 tr12).
rewrite MMR_bwd, MMR_fwd.
unfold MemoryBound, stateSize.
rewrite (stateShape_fwd _ _ _ tr01).
rewrite (N.max_comm (stateShapeSize _)), <- N.max_assoc, N.max_l.
 apply Ht.
apply MMR_bounds.
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) :
 spec s -> spec t -> spec (case s t).
Proof.
intros Hs Ht s0 s1 tr01.
unfold MemoryBound.
cbn in *.
rewrite <- N.add_max_distr_l.
generalize tr01.
pattern s0; pattern s1.
revert s0 s1 tr01.
apply choice_complete.
 intros s0 s1 [|] Heq tr tr01.
  rewrite <- (trace_right _ _ _ _ tr tr01);[|assumption].
  etransitivity;[apply bump_spec;assumption|apply N.le_max_r].
 rewrite <- (trace_left _ _ _ _ tr tr01);[|assumption].
 etransitivity;[apply bump_spec;assumption|apply N.le_max_l].
unfold runProgram, choice;cbn.
intros tr01.
destruct (trace_subproof _ _ _ _); cbn.
apply N.le_0_l.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) :
 spec s -> spec t -> spec (pair s t).
Proof.
intros Hs Ht s0 s2 tr02.
unfold MemoryBound.
cbn in *.
destruct (seq_complete _ _ _ _ tr02) as [s1 tr01 tr12].
rewrite (MMR_seq _ _ _ _ _ tr01 tr12 tr02).
rewrite <- N.add_max_distr_l.
apply N.max_le_compat.
 apply Hs.
etransitivity;[apply Ht|].
apply N.add_le_mono_r.
apply (StateSize_Core _ _ _ _ _ tr01).
Qed.

Lemma take_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@take A B C t).
Proof.
auto.
Qed.

Lemma drop_spec {A B C : Ty} (t : Term B C) :
 spec t -> spec (@drop A B C t).
Proof.
intros Ht x n Hp;cbn.
apply (bump_spec _ Ht _ _ _ Hp).
Qed.

Lemma Core_spec {A B : Ty} (t : Term A B) :
 spec t.
Proof.
induction t.
- apply iden_spec.
- apply comp_spec; assumption.
- apply unit_spec.
- apply injl_spec; assumption.
- apply injr_spec; assumption.
- apply case_spec; assumption.
- apply pair_spec; assumption.
- apply take_spec; assumption.
- apply drop_spec; assumption.
Qed.

Definition CellBound {A B : Ty} (t : Term A B) : N := N.of_nat (bitSize A) + N.of_nat (bitSize B) + (@Core.eval _ _ t extraMemoryBound).

Lemma CellBound_correct {A B : Ty} (t : Term A B) a y
  (tr : fillContext emptyCtx (LocalStateBegin t a) >>- @Core.eval _ _ t Naive.translate ->> y) :
  maximumMemoryResidence (trace tr) <= CellBound t.
Proof.
etransitivity;[apply (Core_spec _ _ _ tr)|].
unfold MemoryBound, CellBound, stateSize, stateShapeSize; cbn.
rewrite app_nil_r, encode_length, N.add_0_r, <- plus_n_O.
reflexivity.
Qed.

End MaximumMemory.
