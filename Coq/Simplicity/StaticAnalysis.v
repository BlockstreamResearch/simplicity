Require Import PeanoNat.
Require Import Util.List.
Require Import Util.Option.

Require Import Simplicity.Alg.
Require Import Simplicity.Core.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Translate.
Require Import Simplicity.Ty.

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
intros x y; simpl.
unfold copy, runMachine.
destruct (Copy_chk _ _) as [[[l st] [_ ->]] |];[simpl|discriminate].
intros Hxy; inversion_clear Hxy.
do 2 rewrite fillContextShape_correct.
unfold localStateShape; simpl.
rewrite fullWriteFrame_size.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (@unit A).
Proof.
intros x y Hxy.
inversion_clear Hxy.
reflexivity.
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

Lemma injl_spec {A B C : Ty} (t : Term A B) :
 spec t -> spec (@injl A B C t).
Proof.
intros ht x y; cbn.
repeat rewrite runMachine_seq.
unfold write, runMachine at 3.
destruct (Write_chk _) as [[ctx ->] |];[cbn|discriminate].
set (x0 := fillContext _ _).
replace (stateShape _) with (stateShape x0).
 unfold skip, runMachine at 2.
 destruct (Skip_chk _ _) as [[ctx0 ->] |];[cbn|discriminate].
 intros Hx1.
 rewrite <- (ht _ _ Hx1); clear y ht Hx1.
 do 2 rewrite fillContextShape_correct.
 unfold localStateShape; simpl.
 rewrite fullWriteFrame_size, repeat_length.
 reflexivity.
unfold x0; do 2 rewrite fillContextShape_correct.
unfold localStateShape; simpl.
rewrite fullWriteFrame_size.
reflexivity.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) :
 spec t -> spec (@injr A B C t).
Proof.
intros ht x y; cbn.
repeat rewrite runMachine_seq.
unfold write, runMachine at 3.
destruct (Write_chk _) as [[ctx ->] |];[cbn|discriminate].
set (x0 := fillContext _ _).
replace (stateShape _) with (stateShape x0).
 unfold skip, runMachine at 2.
 destruct (Skip_chk _ _) as [[ctx0 ->] |];[cbn|discriminate].
 intros Hx1.
 rewrite <- (ht _ _ Hx1); clear y ht Hx1.
 do 2 rewrite fillContextShape_correct.
 unfold localStateShape; simpl.
 rewrite fullWriteFrame_size, repeat_length.
 reflexivity.
unfold x0; do 2 rewrite fillContextShape_correct.
unfold localStateShape; simpl.
rewrite fullWriteFrame_size.
reflexivity.
Qed.

Lemma bump_spec {A B : Ty} (t : Term A B) n (Ht : spec t) x y :
 runMachine (bump n (@Core.eval _ _ t Naive.translate)) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold bump.
repeat rewrite runMachine_seq.
unfold fwd, runMachine at 3.
destruct (Fwd_chk _) as [[[l0 st0] [_ ->]] |];[cbn|discriminate].
set (x1 := fillReadFrame _ _); specialize (Ht x1).
destruct (runMachine _ x1) as [y0|];[cbn|discriminate].
specialize (Ht _ (refl_equal _)).
unfold bwd, runMachine.
destruct (Bwd_chk _) as [[[l1 st1] [_ ->]] |];[cbn|discriminate].
intros Hxy.
inversion_clear Hxy.
unfold x1 in *; clear x1.
repeat rewrite fillReadFrameShape_correct in *.
cbn in *.
do 2 rewrite rev_length, Nat.add_0_r in Ht.
assumption.
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






