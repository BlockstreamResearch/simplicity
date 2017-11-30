Require Import NArith.
Require Import Util.List.
Require Import Util.Option.

Require Import Simplicity.Alg.
Require Import Simplicity.Core.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Translate.
Require Import Simplicity.Ty.

Local Open Scope N_scope.

Module StateShape.
(* In this section we prove that executing Simplicity programs on the Bit
 * Machine starting from *any* state, preserves the shape of the state (if it
 * doesn't crash).
 *)

Definition spec {A B : Ty} (t : Term A B)  :=
  forall x y, runMachine (@Core.eval _ _ t Naive.translate) x = Some y ->
              stateShape x = stateShape y.

Lemma iden_spec {A : Ty} : spec (@iden A).
Proof.
unfold spec.
apply stateShape_copy.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) :
 spec s -> spec t -> spec (comp s t) .
Proof.
intros Hs Ht x z; cbn.
repeat rewrite runMachine_seq; cbn.
set (x1 := Build_State _ _ _ _); specialize (Hs x1).
destruct (runMachine _ x1) as [y0|];[cbn|discriminate].
specialize (Hs _ (eq_refl _)).
unfold moveFrame, runMachine at 3.
destruct (MoveFrame_chk _) as [[[l0 st0] ->] |];[cbn|discriminate].
set (y1 := Build_State _ _ _ _); specialize (Ht y1).
destruct (runMachine _ y1) as [z0|];[cbn|discriminate].
specialize (Ht _ (eq_refl _)).
unfold dropFrame, runMachine.
destruct (DropFrame_chk _) as [[[l1 st1] ->] |];[cbn|discriminate].
intros Hz; inversion Hz as [Hz0]; rewrite <- Hz0; clear z Hz Hz0.
destruct x as [irf arf awf iwf];
unfold stateShape in *; cbn in *.
inversion Hs as [[Hs0 Hs1 Hs2 Hs3 Hs4]].
rewrite Hs0, Hs1, Hs3, Hs4.
clear x1 Hs Hs0 Hs1 Hs2 Hs3 Hs4.
inversion_clear Ht.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (@unit A).
Proof.
intros x y Hxy.
inversion_clear Hxy.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) :
 spec t -> spec (@injl A B C t).
Proof.
intros ht x y; cbn.
repeat rewrite runMachine_seq.
assert (Hx := stateShape_write false x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
rewrite (Hx _ (refl_equal _)); clear -ht.
assert (Hx0 := stateShape_skip (padL B C) x0).
destruct (runMachine _ x0) as [x1|];[cbn|discriminate].
rewrite (Hx0 _ (refl_equal _)); clear -ht.
auto.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@injr A B C t).
Proof.
intros ht x y; cbn.
repeat rewrite runMachine_seq.
assert (Hx := stateShape_write true x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
rewrite (Hx _ (refl_equal _)); clear -ht.
assert (Hx0 := stateShape_skip (padR B C) x0).
destruct (runMachine _ x0) as [x1|];[cbn|discriminate].
rewrite (Hx0 _ (refl_equal _)); clear -ht.
auto.
Qed.

Lemma bump_spec {A B : Ty} (t : Term A B) n (Ht : spec t) x y :
 runMachine (bump n (@Core.eval _ _ t Naive.translate)) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold bump.
repeat rewrite runMachine_seq.
assert (Hx := stateShape_fwd n x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
rewrite (Hx _ (refl_equal _)); clear -Ht.
specialize (Ht x0).
destruct (runMachine _ x0) as [y0|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
assert (Hy := stateShape_bwd n y0).
destruct (runMachine _ y0) as [y1|];[cbn|discriminate].
specialize (Hy _ (refl_equal _)).
intros Hxy.
inversion Hxy.
congruence.
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) :
 spec s -> spec t -> spec (case s t).
Proof.
intros Hs Ht x y; cbn.
rewrite runMachine_choice.
destruct (nextData _) as [| [[|] |] _]; try discriminate;
apply bump_spec; auto.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) :
 spec s -> spec t -> spec (pair s t).
Proof.
intros Hs Ht x z; cbn.
rewrite runMachine_seq.
specialize (Hs x).
destruct (runMachine _ x) as [y|];[|discriminate].
rewrite (Hs y);auto.
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
  forall x n, programMaximumMemoryResidence (@Core.eval _ _ t Naive.translate) x = Some n ->
              n <= MemoryBound t x.

Lemma iden_spec {A : Ty} : spec (@iden A).
Proof.
intros x n; cbn.
rewrite pMMR_copy.
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
inversion_clear 1.
unfold MemoryBound; cbn.
rewrite N.add_0_r.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) :
 spec s -> spec t -> spec (comp s t) .
Proof.
intros Hs Ht x n; cbn.
repeat rewrite pMMR_seq.
repeat rewrite runMachine_seq.
cbn.
set (x0 := Build_State _ _ _ _).
specialize (Hs x0).
destruct (programMaximumMemoryResidence _ x0) as [nx|];[cbn|discriminate].
specialize (Hs _ (refl_equal _)).
assert (Hsx := StateShape.Core_spec s x0).
destruct (runMachine _ x0) as [y|];[cbn|discriminate].
specialize (Hsx _ (refl_equal _)).
rewrite pMMR_moveFrame.
unfold moveFrame, runMachine at 2 3 4.
destruct (MoveFrame_chk y) as [[[l ctx] ->] |];[cbn|discriminate].
set (y0 := Build_State _ _ _ _).
set (y := Build_State _ _ _ _) in Hsx |- *.
specialize (Ht y0).
destruct (programMaximumMemoryResidence _ y0) as [ny|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
assert (Hty := StateShape.Core_spec t y0).
destruct (runMachine _ y0) as [z|];[cbn|discriminate].
specialize (Hty _ (refl_equal _)).
unfold programMaximumMemoryResidence, dropFrame.
destruct (DropFrame_chk z) as [[[l0 ctx0] ->] |];[cbn|discriminate].
inversion_clear 1.
set (z0 := Build_State _ _ _ _) in Hty |- *.
unfold MemoryBound in *; cbn.
unfold stateSize.
rewrite <- Hsx, <- Hty.
fold (stateSize y0); fold (stateSize ctx0); fold (stateSize x0); fold (stateSize x).
rewrite N.add_assoc.
replace (stateSize x + _) with (stateSize x0).
 rewrite <- N.add_max_distr_l,
         (N.max_l (stateSize y0) (stateSize ctx0)),
         (N.max_r (stateSize x) (stateSize x0)),
         (N.max_comm nx _), (N.max_assoc (stateSize x0) _ _), N.max_id,
         N.max_assoc, N.max_comm.
   replace (stateSize y0) with (stateSize x0) in *.
    apply N.max_le_compat; apply N.max_lub; solve [assumption|apply N.le_add_r].
   clear -Hsx.
   unfold stateSize.
   rewrite Hsx.
   unfold y, y0, stateShape, stateShapeSize; cbn.
   rewrite fullWriteFrame_size.
   ring.
  unfold x0; clear.
  destruct x as [irf arf awf iwf]; cbn.
  unfold stateSize, stateShape, stateShapeSize; cbn.
  repeat rewrite N.add_assoc; repeat apply N.add_le_mono_r.
  repeat rewrite <- N.add_assoc; repeat apply N.add_le_mono_l.
  apply N.le_add_r.
 unfold stateSize.
 rewrite Hty.
 unfold z0; clear.
 destruct ctx0 as [irf arf awf iwf]; cbn.
 unfold stateShape, stateShapeSize; cbn.
 repeat rewrite N.add_assoc; repeat apply N.add_le_mono_r.
 rewrite N.add_comm.
 apply N.le_add_r.
unfold x0; clear.
destruct x as [irf arf awf iwf]; cbn.
unfold stateSize, stateShape, stateShapeSize; cbn.
ring.
Qed.

Lemma unit_spec {A : Ty} : spec (@unit A).
Proof.
intros x n; unfold MemoryBound; cbn.
inversion_clear 1.
rewrite N.add_0_r.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) :
 spec t -> spec (@injl A B C t).
Proof.
intros Ht x n; cbn.
repeat rewrite pMMR_seq.
repeat rewrite runMachine_seq.
rewrite pMMR_write.
assert (Hx := stateShape_write false x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
specialize (Hx _ (refl_equal _)).
rewrite pMMR_skip.
assert (Hx0 := stateShape_skip (padL B C) x0).
destruct (runMachine _ x0) as [x1|];[cbn|discriminate].
specialize (Hx0 _ (refl_equal _)).
specialize (Ht x1).
destruct (programMaximumMemoryResidence _ x1) as [nt|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
inversion_clear 1.
unfold MemoryBound, stateSize in *; cbn.
rewrite Hx, Hx0; clear -Ht.
rewrite N.max_id.
apply N.max_lub;[assumption|].
apply N.le_add_r.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@injr A B C t).
Proof.
intros Ht x n; cbn.
repeat rewrite pMMR_seq.
repeat rewrite runMachine_seq.
rewrite pMMR_write.
assert (Hx := stateShape_write true x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
specialize (Hx _ (refl_equal _)).
rewrite pMMR_skip.
assert (Hx0 := stateShape_skip (padR B C) x0).
destruct (runMachine _ x0) as [x1|];[cbn|discriminate].
specialize (Hx0 _ (refl_equal _)).
specialize (Ht x1).
destruct (programMaximumMemoryResidence _ x1) as [nt|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
inversion_clear 1.
unfold MemoryBound, stateSize in *; cbn.
rewrite Hx, Hx0; clear -Ht.
rewrite N.max_id.
apply N.max_lub;[assumption|].
apply N.le_add_r.
Qed.

Lemma bump_spec {A B : Ty} (t : Term A B) (Ht : spec t) :
 forall x n m, programMaximumMemoryResidence (bump n (@Core.eval _ _ t Naive.translate)) x = Some m ->
               m <= MemoryBound t x.
Proof.
intros x n m.
unfold bump.
repeat rewrite pMMR_seq.
repeat rewrite runMachine_seq.
rewrite pMMR_fwd.
assert (Hx := stateShape_fwd n x).
destruct (runMachine _ x) as [x0|];[cbn|discriminate].
specialize (Hx _ (refl_equal _)).
specialize (Ht x0).
unfold programMaximumMemoryResidence in Ht.
unfold programMaximumMemoryResidence at 2.
unfold runMachine.
destruct (Core.eval _) as [[y tr0] |];[cbn in *|discriminate].
specialize (Ht _ (refl_equal _)).
rewrite pMMR_bwd.
assert (Hy := stateShape_bwd n y).
destruct (runMachine _ y) as [y0|];[cbn|discriminate].
specialize (Hy _ (refl_equal _)).
inversion_clear 1.
unfold MemoryBound, stateSize.
rewrite Hx.
etransitivity;[|apply Ht].
rewrite N.max_comm, <- N.max_assoc.
apply N.max_lub;[reflexivity|apply MMR_bounds].
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) :
 spec s -> spec t -> spec (case s t).
Proof.
intros Hs Ht x n; cbn.
unfold MemoryBound; cbn.
rewrite pMMR_choice.
rewrite <- N.add_max_distr_l.
destruct (nextData _) as [| [[|] |] _]; try discriminate;
 intros Hp;etransitivity;[|apply N.le_max_r| |apply N.le_max_l];
 revert Hp;apply bump_spec; assumption.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) :
 spec s -> spec t -> spec (pair s t).
Proof.
intros Hs Ht x n; unfold MemoryBound; cbn.
rewrite pMMR_seq.
specialize (Hs x).
destruct (programMaximumMemoryResidence _ x) as [ns|];[cbn|discriminate].
specialize (Hs _ (refl_equal _)).
assert (Hsx := StateShape.Core_spec s x).
destruct (runMachine _ x) as [y|];[cbn|discriminate].
specialize (Hsx _ (refl_equal _)).
specialize (Ht y).
destruct (programMaximumMemoryResidence _ y) as [nt|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
inversion_clear 1.
rewrite N.max_comm.
transitivity (N.max (MemoryBound s x) (MemoryBound t y)).
 apply N.max_le_compat; assumption.
unfold MemoryBound, stateSize.
rewrite Hsx, N.add_max_distr_l.
reflexivity.
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

Lemma CellBound_correct {A B : Ty} (t : Term A B) a n:
  programMaximumMemoryResidence (@Core.eval _ _ t Naive.translate) (fillContext emptyCtx (LocalStateBegin t a)) = Some n ->
  n <= CellBound t.
Proof.
intros Ht.
etransitivity;[apply (Core_spec _ _ _ Ht)|].
unfold MemoryBound, CellBound, stateSize, stateShapeSize; cbn.
rewrite app_nil_r, encode_length, N.add_0_r, <- plus_n_O.
reflexivity.
Qed.

End MaximumMemory.