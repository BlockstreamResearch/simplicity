Require Import PeanoNat.
Require Import List.

Require Import Simplicity.Alg.
Require Import Simplicity.Core.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Ty.

Lemma rev_S_tail {A} : forall (a : A) n, repeat a n ++ (a :: nil) = repeat a (S n).
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma rev_repeat {A} : forall (a : A) n, rev (repeat a n) = repeat a n.
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn.
rewrite rev_S_tail.
reflexivity.
Qed.

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
- intros [].
  reflexivity.
- intros [a|b]; simpl; rewrite app_length, repeat_length;
  [rewrite IHX1, padL_bitSize | rewrite IHX2, padR_bitSize];
  reflexivity.
- intros [a b]; simpl.
  rewrite app_length, IHX1, IHX2.
  reflexivity.
Qed.

Definition spec {A B : Ty} (f : State -> option State) (t : Term A B)  :=
  forall a ctx, f (fillContext ctx {| readHole := encode a; writeHole := newWriteFrame (bitSize B) |})
  = Some (fillContext ctx {| readHole := encode a; writeHole := fullWriteFrame (encode (eval t a)) |}).

Module Naive.

Lemma iden_spec {A : Ty} : spec (runMachine (copy (bitSize A))) (@iden A).
Proof.
intros a ctx.
simpl.
rewrite <- (encode_length a), State.copy_correct.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C)
 ps pt : spec (runMachine ps) s -> spec (runMachine pt) t
      -> spec (runMachine (newFrame (bitSize B) ;; ps ;; moveFrame ;; pt ;; dropFrame)) (comp s t) .
Proof.
intros Hs Ht a ctx.
repeat rewrite runMachine_append.
unfold fillContext at 1.
simpl (runMachine _ _).
unfold State.newFrame.
unfold option_bind at 4.
simpl (option_join _).
pose (ctx1 := {| inactiveReadFrames := inactiveReadFrames ctx
               ; activeFrames :=
                 {| readFrame := readFrame (activeFrames ctx)
                  ; writeFrame := newWriteFrame 0
                  |}
               ; inactiveWriteFrames := {| writeData := writeData (writeFrame (activeFrames ctx))
                                         ; writeEmpty := bitSize C + writeEmpty (writeFrame (activeFrames ctx))
                                         |} :: inactiveWriteFrames ctx
               |}).
pose (h1 := {| readHole := encode a; writeHole := newWriteFrame (bitSize B) |}).
unfold newWriteFrame.
rewrite <- (Plus.plus_0_r (bitSize B)).
change (runMachine ps _) with (runMachine ps (fillContext ctx1 h1)).
unfold h1; rewrite Hs.

unfold option_bind at 2.
simpl (option_join _); clear ctx1 h1.
rewrite app_nil_r, rev_involutive.
pose (ctx1 := {| inactiveReadFrames := {| prevData := prevData (readFrame (activeFrames ctx))
                                        ; nextData := encode a ++ nextData (readFrame (activeFrames ctx))
                                        |} :: inactiveReadFrames ctx
               ; activeFrames :=
                 {| readFrame := {| prevData := nil; nextData := nil; |}
                  ; writeFrame := writeFrame (activeFrames ctx)
                  |}
               ; inactiveWriteFrames := inactiveWriteFrames ctx
               |}).
pose (h1 := {| readHole := encode (eval s a); writeHole := newWriteFrame (bitSize C) |}).
rewrite <- (app_nil_r (encode (_ a))).
change (runMachine pt _) with (runMachine pt (fillContext ctx1 h1)).
unfold h1; rewrite Ht.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (runMachine nop) (@unit A).
Proof.
intros a ctx.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B)
 pt : spec (runMachine pt) t
      -> spec (runMachine (write false ;; skip (padL B C) ;; pt)) (@injl A B C t).
Proof.
intros Ht a ctx.
repeat rewrite runMachine_append.
unfold newWriteFrame.
simpl (bitSize _).
rewrite <- padL_bitSize.
unfold option_bind at 2.
simpl (option_join _).
change (State.skip (padL B C) _) with
 (State.skip (padL B C) (fillContext ctx {| readHole := encode a; writeHole :=
   {| writeData := Some false :: nil; writeEmpty := padL B C + bitSize B |} |})).
rewrite State.skip_correct.
rewrite <- (rev_repeat _ (padL B C)).
pose (h0 := {| readHole := nil; writeHole := fullWriteFrame (Some false :: repeat None (padL B C)) |}).
pose (h1 := {| readHole := encode a; writeHole := newWriteFrame (bitSize B) |}).
rewrite <- (app_nil_r (encode a)).
rewrite <- (Plus.plus_0_r (bitSize B)).
change (fillContext ctx _) at 1 with (fillContext ctx (appendHole h0 h1)).
rewrite <- context_action.
unfold h1, option_bind; simpl.
rewrite Ht.
rewrite context_action.
unfold h0, appendHole.
simpl.
rewrite app_nil_r.
rewrite app_assoc.
rewrite <- rev_app_distr.
reflexivity.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C)
 pt : spec (runMachine pt) t
      -> spec (runMachine (write true ;; skip (padR B C) ;; pt)) (@injr A B C t) .
Proof.
intros Ht a ctx.
repeat rewrite runMachine_append.
unfold newWriteFrame.
simpl (bitSize _).
rewrite <- padR_bitSize.
unfold option_bind at 2.
simpl (option_join _).
change (State.skip (padR B C) _) with
 (State.skip (padR B C) (fillContext ctx {| readHole := encode a; writeHole :=
   {| writeData := Some true :: nil; writeEmpty := padR B C + bitSize C |} |})).
rewrite State.skip_correct.
rewrite <- (rev_repeat _ (padR B C)).
pose (h0 := {| readHole := nil; writeHole := fullWriteFrame (Some true :: repeat None (padR B C)) |}).
pose (h1 := {| readHole := encode a; writeHole := newWriteFrame (bitSize C) |}).
rewrite <- (app_nil_r (encode a)).
rewrite <- (Plus.plus_0_r (bitSize C)).
change (fillContext ctx _) at 1 with (fillContext ctx (appendHole h0 h1)).
rewrite <- context_action.
unfold h1, option_bind; simpl.
rewrite Ht.
rewrite context_action.
unfold h0, appendHole.
simpl.
rewrite app_nil_r.
rewrite app_assoc.
rewrite <- rev_app_distr.
reflexivity.
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D)
 ps pt : spec (runMachine ps) s -> spec (runMachine pt) t
      -> spec (runMachine (read (bump (1 + padL A B) ps) (bump (1 + padR A B) pt))) (case s t).
Proof.
intros Hs Ht [[a|b] c] ctx;
cbn -[bump]; rewrite <- app_assoc.
- set (ac := (a, c) : tySem (A * C)).
  change (encode a ++ _) with (encode ac).
  pose (l := Some false :: repeat None (padL A B)).
  pose (h0 := bumpHole l).
  pose (h1 := {| readHole := encode ac; writeHole := newWriteFrame (bitSize D) |}).
  pose (h1' := {| readHole := encode ac; writeHole := fullWriteFrame (encode (eval s (a, c))) |}).
  change (fillContext ctx _) at 1 with (fillContext ctx (appendHole h1 h0)).
  change (fillContext ctx _) at 2 with (fillContext ctx (appendHole h1' h0)).
  rewrite <- (repeat_length (@None bool) (padL A B)).
  change (bump _) with (bump (length l)).
  apply runMachine_bump.
  apply Hs.
- set (bc := (b, c) : tySem (B * C)).
  change (encode b ++ _) with (encode bc).
  pose (l := Some true :: repeat None (padR A B)).
  pose (h0 := bumpHole l).
  pose (h1 := {| readHole := encode bc; writeHole := newWriteFrame (bitSize D) |}).
  pose (h1' := {| readHole := encode bc; writeHole := fullWriteFrame (encode (eval t (b, c))) |}).
  change (fillContext ctx _) at 1 with (fillContext ctx (appendHole h1 h0)).
  change (fillContext ctx _) at 2 with (fillContext ctx (appendHole h1' h0)).
  rewrite <- (repeat_length (@None bool) (padR A B)).
  change (bump _) with (bump (length l)).
  apply runMachine_bump.
  apply Ht.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C)
 ps pt : spec (runMachine ps) s -> spec (runMachine pt) t
      -> spec (runMachine (ps ;; pt)) (pair s t).
Proof.
intros Hs Ht a ctx.
rewrite runMachine_append.
unfold fullWriteFrame, newWriteFrame.
simpl.

pose (h1 := {| readHole := nil; writeHole := newWriteFrame (bitSize C) |}).
pose (h2 := {| readHole := encode a; writeHole := newWriteFrame (bitSize B) |}).
rewrite <- (app_nil_r (encode a)) at 1.
change (fillContext _ _) at 1 with (fillContext ctx (appendHole h1 h2)).
rewrite <- context_action.
unfold h2.
rewrite Hs.
rewrite context_action.
unfold appendHole, option_bind.
simpl; clear h1 h2.

pose (h1 := {| readHole := nil; writeHole := fullWriteFrame (encode (eval s a)) |}).
pose (h2 := {| readHole := encode a; writeHole := newWriteFrame (bitSize C) |}).
rewrite (app_nil_r (rev _)).
rewrite <- (Plus.plus_0_r (bitSize C)).
change (fillContext _ _) at 1 with (fillContext ctx (appendHole h1 h2)).
rewrite <- context_action.
unfold h2.
rewrite Ht, context_action.
unfold appendHole.
simpl; clear h1 h2.
rewrite app_nil_r, rev_app_distr.
reflexivity.
Qed.

Lemma take_spec {A B C : Ty} (t : Term A C)
 pt : spec (runMachine pt) t
      -> spec (runMachine pt) (@take A B C t).
Proof.
intros Ht [a b] ctx.
simpl.
pose (h1 := {| readHole := encode b; writeHole := newWriteFrame 0 |}).
pose (h2 := {| readHole := encode a; writeHole := newWriteFrame (bitSize C) |}).
rewrite <- (Plus.plus_0_r (bitSize C)).
change (fillContext _ _) at 1 with (fillContext ctx (appendHole h1 h2)).
rewrite <- context_action.
unfold h2.
rewrite Ht, context_action.
unfold appendHole;simpl.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma drop_spec {A B C : Ty} (t : Term B C)
 pt : spec (runMachine pt) t
      -> spec (runMachine (bump (bitSize A) pt)) (@drop A B C t).
Proof.
intros Ht [a b] ctx.
pose (h1 := {| readHole := encode b; writeHole := newWriteFrame (bitSize C) |}).
pose (h1' := {| readHole := encode b; writeHole := fullWriteFrame (encode (eval t b)) |}).
pose (h2 := {| readHole := encode a; writeHole := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendHole h1 h2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendHole h1' h2)).
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

Lemma translate_spec {A B : Ty} (t : Term A B)
 : spec (runMachine (@Core.eval _ _ t translate)) t.
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
  forall a ctx, runMachine (@t translate) (fillContext ctx {| readHole := encode a; writeHole := newWriteFrame (bitSize B) |})
  = Some (fillContext ctx {| readHole := encode a; writeHole := fullWriteFrame (encode (|[ t ]| a)) |}).
Proof.
intros a.
pose (t0 := t Core.Term : Term A B).
rewrite (Core.term_eval Ht).
rewrite (Core.term_eval Ht CoreSem).
rewrite <- CoreSem_correct.
apply translate_spec.
Qed.

End Naive.