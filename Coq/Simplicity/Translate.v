Require Import PeanoNat.
Require Import Util.List.
Require Import Util.Option.

Require Import Simplicity.Alg.
Require Import Simplicity.Core.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Ty.

Local Open Scope ty_scope.
Local Open Scope mc_scope.

Fixpoint bitSize (X : Ty) : nat :=
match X with
| Unit => 0
| Sum A B => 1 + max (bitSize A) (bitSize B)
| Prod A B => bitSize A + bitSize B
end.

Definition padL (X Y : Ty) : nat := max (bitSize X) (bitSize Y) - bitSize X.
Definition padR (X Y : Ty) : nat := max (bitSize X) (bitSize Y) - bitSize Y.

Lemma padL_bitSize (X Y : Ty) : (padL X Y + bitSize X = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padL.
apply Nat.sub_add.
apply Nat.le_max_l.
Qed.

Lemma padR_bitSize (X Y : Ty) : (padR X Y + bitSize Y = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padL.
apply Nat.sub_add.
apply Nat.le_max_r.
Qed.

Fixpoint encode {X : Ty} : X -> list Cell :=
match X with
| Unit => fun _ => nil
| Sum A B => fun ab =>
  match ab with
  | inl a => Some false :: repeat None (padL A B) ++ encode a
  | inr b => Some true  :: repeat None (padR A B) ++ encode b
  end
| Prod A B => fun ab =>
  let (a, b) := ab in encode a ++ encode b
end.

Lemma encode_length {X : Ty} : forall x : X, length (encode x) = bitSize X.
Proof.
induction X.
- reflexivity.
- intros [a|b]; cbn; rewrite app_length, repeat_length;
  [rewrite IHX1, padL_bitSize | rewrite IHX2, padR_bitSize];
  reflexivity.
- intros [a b]; cbn.
  rewrite app_length, IHX1, IHX2.
  reflexivity.
Qed.

Definition LocalStateBegin {A B : Ty} (t : Term A B) (a : A) :=
  {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |}.

Definition LocalStateEnd {A B : Ty} (t : Term A B) (a : A) :=
  {| readLocalState := encode a; writeLocalState := fullWriteFrame (encode (eval t a)) |}.

Definition spec {A B : Ty} (f : State -> option State) (t : Term A B)  :=
  forall a ctx, f (fillContext ctx (LocalStateBegin t a))
  = Some (fillContext ctx (LocalStateEnd t a)).

Module Naive.

Lemma iden_spec {A : Ty} : spec (runMachine (copy (bitSize A))) (@iden A).
Proof.
intros a ctx.
unfold LocalStateBegin.
cbn.
rewrite <- (encode_length a), State.copy_correct.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) ps pt :
 spec (runMachine ps) s -> spec (runMachine pt) t ->
 spec (runMachine (newFrame (bitSize B) ;; ps ;; moveFrame ;; pt ;; dropFrame)) (comp s t) .
Proof.
intros Hs Ht a ctx.
repeat rewrite runMachine_append.
unfold fillContext at 1.
simpl (runMachine _ _).
unfold State.newFrame, option_bind at 4, newWriteFrame.
simpl (option_join _).
rewrite <- (Plus.plus_0_r (bitSize B)).
pose (ctx1 := {| inactiveReadFrames := inactiveReadFrames ctx
               ; activeFrames :=
                 {| readFrame := readFrame (activeFrames ctx)
                  ; writeFrame := newWriteFrame 0
                  |}
               ; inactiveWriteFrames := {| writeData := writeData (writeFrame (activeFrames ctx))
                                         ; writeEmpty := bitSize C + writeEmpty (writeFrame (activeFrames ctx))
                                         |} :: inactiveWriteFrames ctx
               |}).
change (runMachine ps _) with (runMachine ps (fillContext ctx1 (LocalStateBegin s a))).
rewrite Hs.

unfold option_bind at 2.
simpl (option_join _); clear ctx1.
rewrite app_nil_r, rev_involutive, <- (app_nil_r (encode (_ a))).
pose (ctx1 := {| inactiveReadFrames := {| prevData := prevData (readFrame (activeFrames ctx))
                                        ; nextData := encode a ++ nextData (readFrame (activeFrames ctx))
                                        |} :: inactiveReadFrames ctx
               ; activeFrames :=
                 {| readFrame := {| prevData := nil; nextData := nil; |}
                  ; writeFrame := writeFrame (activeFrames ctx)
                  |}
               ; inactiveWriteFrames := inactiveWriteFrames ctx
               |}).
change (runMachine pt _) with (runMachine pt (fillContext ctx1 (LocalStateBegin t (eval s a)))).
rewrite Ht.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (runMachine nop) (@unit A).
Proof.
intros a ctx.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) pt :
 spec (runMachine pt) t ->
 spec (runMachine (write false ;; skip (padL B C) ;; pt)) (@injl A B C t).
Proof.
intros Ht a ctx.
repeat rewrite runMachine_append.
unfold LocalStateBegin, newWriteFrame, option_bind at 2.
simpl (option_join _).
rewrite <- padL_bitSize.
change (State.skip _ _) with
 (State.skip (padL B C) (fillContext ctx
   {| readLocalState := encode a
    ; writeLocalState :=
      {| writeData := Some false :: nil; writeEmpty := padL B C + bitSize B |}
    |})).
rewrite State.skip_correct, <- (rev_repeat _ (padL B C)),
        <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize B)).
pose (h0 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some false :: repeat None (padL B C)) |}).
change (fillContext ctx _) at 1 with (fillContext ctx (appendLocalState h0 (LocalStateBegin t a))).
rewrite <- context_action; cbn.
rewrite Ht, context_action.
unfold h0, appendLocalState; cbn.
rewrite app_nil_r, app_assoc, <- rev_app_distr.
reflexivity.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) pt :
 spec (runMachine pt) t ->
 spec (runMachine (write true ;; skip (padR B C) ;; pt)) (@injr A B C t) .
Proof.
intros Ht a ctx.
repeat rewrite runMachine_append.
unfold LocalStateBegin, newWriteFrame, option_bind at 2.
simpl (option_join _).
rewrite <- padR_bitSize.
change (State.skip _ _) with
 (State.skip (padR B C) (fillContext ctx
   {| readLocalState := encode a
    ; writeLocalState :=
      {| writeData := Some true :: nil; writeEmpty := padR B C + bitSize C |}
    |})).
rewrite State.skip_correct, <- (rev_repeat _ (padR B C)),
        <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize C)).
pose (h0 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some true :: repeat None (padR B C)) |}).
change (fillContext ctx _) at 1 with (fillContext ctx (appendLocalState h0 (LocalStateBegin t a))).
rewrite <- context_action; cbn.
rewrite Ht, context_action.
unfold h0, appendLocalState; cbn.
rewrite app_nil_r, app_assoc, <- rev_app_distr.
reflexivity.
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) ps pt :
 spec (runMachine ps) s -> spec (runMachine pt) t ->
 spec (runMachine (read (bump (1 + padL A B) ps) (bump (1 + padR A B) pt))) (case s t).
Proof.
intros Hs Ht [[a|b] c] ctx;
unfold LocalStateBegin, LocalStateEnd; cbn -[bump]; rewrite <- app_assoc.
- set (ac := (a, c) : tySem (A * C)).
  change (encode a ++ _) with (encode ac).
  pose (l := Some false :: repeat None (padL A B)).
  pose (h0 := bumpLocalState l).
  pose (ls1 := LocalStateBegin s ac).
  pose (ls1' := LocalStateEnd s ac).
  change (fillContext ctx _) at 1 with (fillContext ctx (appendLocalState ls1 h0)).
  change (fillContext ctx _) at 2 with (fillContext ctx (appendLocalState ls1' h0)).
  rewrite <- (repeat_length (@None bool) (padL A B)).
  change (bump _) with (bump (length l)).
  apply runMachine_bump.
  apply Hs.
- set (bc := (b, c) : tySem (B * C)).
  change (encode b ++ _) with (encode bc).
  pose (l := Some true :: repeat None (padR A B)).
  pose (h0 := bumpLocalState l).
  pose (ls1 := LocalStateBegin t bc).
  pose (ls1' := LocalStateEnd t bc).
  change (fillContext ctx _) at 1 with (fillContext ctx (appendLocalState ls1 h0)).
  change (fillContext ctx _) at 2 with (fillContext ctx (appendLocalState ls1' h0)).
  rewrite <- (repeat_length (@None bool) (padR A B)).
  change (bump _) with (bump (length l)).
  apply runMachine_bump.
  apply Ht.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) ps pt :
 spec (runMachine ps) s -> spec (runMachine pt) t ->
 spec (runMachine (ps ;; pt)) (pair s t).
Proof.
intros Hs Ht a ctx.
rewrite runMachine_append.
unfold LocalStateBegin, fullWriteFrame, newWriteFrame; cbn.

rewrite <- (app_nil_r (encode a)) at 1.
pose (ls1 := {| readLocalState := nil; writeLocalState := newWriteFrame (bitSize C) |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin s a))).
rewrite <- context_action, Hs, context_action.
unfold appendLocalState; cbn; clear ls1.

rewrite (app_nil_r (rev _)), <- (Plus.plus_0_r (bitSize C)).
pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (encode (eval s a)) |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
rewrite <- context_action, Ht, context_action.
unfold appendLocalState; cbn; clear ls1.

rewrite app_nil_r, <- rev_app_distr.
reflexivity.
Qed.

Lemma take_spec {A B C : Ty} (t : Term A C) pt :
 spec (runMachine pt) t ->
 spec (runMachine pt) (@take A B C t).
Proof.
intros Ht [a b] ctx.
unfold LocalStateBegin; cbn.
rewrite <- (Plus.plus_0_r (bitSize C)).
pose (ls1 := {| readLocalState := encode b; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
rewrite <- context_action, Ht, context_action.
unfold appendLocalState; cbn.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma drop_spec {A B C : Ty} (t : Term B C) pt :
 spec (runMachine pt) t ->
 spec (runMachine (bump (bitSize A) pt)) (@drop A B C t).
Proof.
intros Ht [a b] ctx.
pose (ls1 := LocalStateBegin t b).
pose (ls1' := LocalStateEnd t b).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (bumpLocalState (encode a)))).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState ls1' (bumpLocalState (encode a)))).
rewrite <- (encode_length a).
apply runMachine_bump.
apply Ht.
Qed.

Definition translate : Core.type := Core.Pack (Core.Class.Class (fun A B => MachineCode.T)
  (fun A => copy (bitSize A))
  (fun A B C ps pt => newFrame (bitSize B) ;; ps ;; moveFrame ;; pt ;; dropFrame)
  (fun A => nop)
  (fun A B C pt => write false ;; skip (padL B C) ;; pt)
  (fun A B C pt => write true ;; skip (padR B C) ;; pt)
  (fun A B C D ps pt => read (bump (1 + padL A B) ps) (bump (1 + padR A B) pt))
  (fun A B C ps pt => ps ;; pt)
  (fun A B C pt => pt)
  (fun A B C pt => bump (bitSize A) pt)
).

Lemma translate_spec {A B : Ty} (t : Term A B) :
 spec (runMachine (@Core.eval _ _ t translate)) t.
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

Local Open Scope core_alg_scope.

Lemma translate_spec_parametric {A B : Ty} (t : forall {term : Core.type}, term A B) (Ht : Core.Parametric (@t)):
  forall a ctx, runMachine (@t translate) (fillContext ctx {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |})
  = Some (fillContext ctx {| readLocalState := encode a; writeLocalState := fullWriteFrame (encode (|[ t ]| a)) |}).
Proof.
intros a.
pose (t0 := t Core.Term : Term A B).
rewrite (Core.term_eval Ht).
rewrite (Core.term_eval Ht CoreSem).
rewrite <- CoreSem_correct.
apply translate_spec.
Qed.

End Naive.