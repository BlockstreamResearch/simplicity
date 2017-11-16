Require Import PeanoNat.
Require Import Util.List.
Require Import Util.Option.
Require Import Util.Thrist.

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

(* We take advantage that x - y = 0 when x <= y for natural numbers. *)
Definition padL (X Y : Ty) : nat := bitSize Y - bitSize X.
Definition padR (X Y : Ty) : nat := bitSize X - bitSize Y.

Lemma padL_bitSize (X Y : Ty) : (padL X Y + bitSize X = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padL.
apply Nat.max_case_strong; intros HXY.
- rewrite <- Nat.sub_0_le in HXY.
  rewrite HXY.
  reflexivity.
- rewrite Nat.sub_add; auto.
Qed.

Lemma padR_bitSize (X Y : Ty) : (padR X Y + bitSize Y = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padR.
apply Nat.max_case_strong; intros HXY.
- rewrite Nat.sub_add; auto.
- rewrite <- Nat.sub_0_le in HXY.
  rewrite HXY.
  reflexivity.
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

Definition spec {A B : Ty} (p : Program) (t : Term A B)  :=
  forall a ctx, runMachine p (fillContext ctx (LocalStateBegin t a)) = Some (fillContext ctx (LocalStateEnd t a)).

Module Naive.

Lemma iden_spec {A : Ty} : spec (copy (bitSize A)) (@iden A).
Proof.
intros a ctx.
unfold LocalStateBegin, runMachine.
rewrite <- (encode_length a), copy_correct.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (s : Term A B) (t : Term B C) ps pt :
 spec ps s -> spec pt t ->
 spec (newFrame (bitSize B) ;;; ps ;;; moveFrame ;;; pt ;;; dropFrame) (comp s t) .
Proof.
intros Hs Ht a ctx.
repeat rewrite runMachine_seq.
unfold runMachine at 5; cbn.
rewrite <- (Plus.plus_0_r (bitSize B)).
pose (ctx1 := {| inactiveReadFrames := inactiveReadFrames ctx
               ; activeReadFrame := activeReadFrame ctx
               ; activeWriteFrame := newWriteFrame 0
               ; inactiveWriteFrames :=
                 {| writeData := writeData (activeWriteFrame ctx)
                  ; writeEmpty := bitSize C + writeEmpty (activeWriteFrame ctx)
                  |} :: inactiveWriteFrames ctx
               |}).
change (runMachine ps _) with (runMachine ps (fillContext ctx1 (LocalStateBegin s a))).
rewrite Hs; cbn; clear ctx1.
rewrite app_nil_r, rev_involutive, <- (app_nil_r (encode (_ a))).
pose (ctx1 := {| inactiveReadFrames :=
                 {| prevData := prevData (activeReadFrame ctx)
                  ; nextData := encode a ++ nextData (activeReadFrame ctx)
                  |} :: inactiveReadFrames ctx
               ; activeReadFrame := {| prevData := nil; nextData := nil; |}
               ; activeWriteFrame := activeWriteFrame ctx
               ; inactiveWriteFrames := inactiveWriteFrames ctx
               |}).
change (runMachine pt _) with (runMachine pt (fillContext ctx1 (LocalStateBegin t (eval s a)))).
rewrite Ht.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec nop (@unit A).
Proof.
intros a ctx.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (t : Term A B) pt :
 spec pt t ->
 spec (write false ;;; skip (padL B C) ;;; pt) (@injl A B C t).
Proof.
intros Ht a ctx.
repeat rewrite runMachine_seq.
pose (ls1 := {| readLocalState := encode a; writeLocalState := newWriteFrame (max (bitSize B) (bitSize C)) |}).
pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame 1 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
unfold runMachine at 3.
rewrite <- context_action, write_correct; cbn; rewrite context_action.
unfold appendLocalState; cbn; clear ls1 ls2.
rewrite <- padL_bitSize.
pose (ls1 := {| readLocalState := encode a; writeLocalState := {| writeData := Some false :: nil; writeEmpty := bitSize B |}|}).
pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame (padL B C)|}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
unfold runMachine at 2.
rewrite <- context_action, skip_correct; cbn; rewrite context_action.
unfold appendLocalState; cbn; clear ls1 ls2.
rewrite <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize B)).
pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some false :: repeat None (padL B C))|}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
rewrite <- context_action, Ht, context_action.
unfold appendLocalState; cbn -[rev]; clear ls1.
rewrite <- rev_app_distr, app_nil_r.
reflexivity.
Qed.

Lemma injr_spec {A B C : Ty} (t : Term A C) pt :
 spec pt t ->
 spec (write true ;;; skip (padR B C) ;;; pt) (@injr A B C t).
Proof.
intros Ht a ctx.
repeat rewrite runMachine_seq.
pose (ls1 := {| readLocalState := encode a; writeLocalState := newWriteFrame (max (bitSize B) (bitSize C)) |}).
pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame 1 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
unfold runMachine at 3.
rewrite <- context_action, write_correct; cbn; rewrite context_action.
unfold appendLocalState; cbn; clear ls1 ls2.
rewrite <- padR_bitSize.
pose (ls1 := {| readLocalState := encode a; writeLocalState := {| writeData := Some true :: nil; writeEmpty := bitSize C |}|}).
pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame (padR B C)|}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
unfold runMachine at 2.
rewrite <- context_action, skip_correct; cbn; rewrite context_action.
unfold appendLocalState; cbn; clear ls1 ls2.
rewrite <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize C)).
pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some true :: repeat None (padR B C))|}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
rewrite <- context_action, Ht, context_action.
unfold appendLocalState; cbn -[rev]; clear ls1.
rewrite <- rev_app_distr, app_nil_r.
reflexivity.
Qed.

Lemma caseL_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) ps pt :
 spec ps s ->
 forall a c ctx,
  runMachine (bump (1 + padL A B) ps ||| bump (1 + padR A B) pt)
    (fillContext ctx (LocalStateBegin (case s t) (inl a, c))) =
  Some (fillContext ctx (LocalStateEnd (case s t) (inl a, c))).
Proof.
intros Hs a c ctx.
rewrite runMachine_choice; unfold LocalStateBegin, LocalStateEnd; cbn.
rewrite <- app_assoc.
rewrite <- (@repeat_length Cell None (padL A B)) at 1.
set (prefix := Some false :: repeat None (padL A B)).
pose (ls2 := {| readLocalState := prefix; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin s (a,c)) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd s (a,c)) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin s (a,c))) {| prevData := nil; nextData := prefix |}).
apply runMachine_bump.
apply (Hs _ (fillReadFrame ctx {| prevData := rev (prefix); nextData := nil |})).
Qed.

Lemma caseR_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) ps pt :
 spec pt t ->
 forall b c ctx,
  runMachine (bump (1 + padL A B) ps ||| bump (1 + padR A B) pt)
    (fillContext ctx (LocalStateBegin (case s t) (inr b, c))) =
  Some (fillContext ctx (LocalStateEnd (case s t) (inr b, c))).
Proof.
intros Ht b c ctx.
rewrite runMachine_choice; unfold LocalStateBegin, LocalStateEnd; cbn.
rewrite <- app_assoc.
rewrite <- (@repeat_length Cell None (padR A B)) at 1.
set (prefix := Some true :: repeat None (padR A B)).
pose (ls2 := {| readLocalState := prefix; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin t (b,c)) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd t (b,c)) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin t (b,c))) {| prevData := nil; nextData := prefix |}).
apply runMachine_bump.
apply (Ht _ (fillReadFrame ctx {| prevData := rev (prefix); nextData := nil |})).
Qed.

Lemma case_spec {A B C D : Ty} (s : Term (A * C) D) (t : Term (B * C) D) ps pt :
 spec ps s -> spec pt t ->
 spec (bump (1 + padL A B) ps ||| bump (1 + padR A B) pt) (case s t).
Proof.
intros Hs Ht [[a|b] c] ctx.
- apply caseL_spec; assumption.
- apply caseR_spec; assumption.
Qed.

Lemma pair_spec {A B C : Ty} (s : Term A B) (t : Term A C) ps pt :
 spec ps s -> spec pt t ->
 spec (ps ;;; pt) (pair s t).
Proof.
intros Hs Ht a ctx.
rewrite runMachine_seq.
unfold LocalStateBegin.
rewrite <- (app_nil_r (encode a)) at 1.
pose (ls1 := {| readLocalState := nil; writeLocalState := newWriteFrame (bitSize C) |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin s a))).
rewrite <- context_action, Hs, context_action; cbn.
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
 spec pt t ->
 spec pt (@take A B C t).
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
 spec pt t ->
 spec (bump (bitSize A) pt) (@drop A B C t).
Proof.
intros Ht [a b] ctx.
pose (ls2 := {| readLocalState := encode a; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin t b) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd t b) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin t b)) {| prevData := nil; nextData := encode a |}).
rewrite <- (encode_length a).
apply runMachine_bump.
apply (Ht _ (fillReadFrame ctx {| prevData := rev (encode a); nextData := nil |})).
Qed.

Definition translate : Core.Algebra := Core.Pack (Core.Class.Class (fun A B => Program)
  (fun A => copy (bitSize A))
  (fun A B C ps pt => newFrame (bitSize B) ;;; ps ;;; moveFrame ;;; pt ;;; dropFrame)
  (fun A => nop)
  (fun A B C pt => write false ;;; skip (padL B C) ;;; pt)
  (fun A B C pt => write true ;;; skip (padR B C) ;;; pt)
  (fun A B C D ps pt => bump (1 + padL A B) ps ||| bump (1 + padR A B) pt)
  (fun A B C ps pt => ps ;;; pt)
  (fun A B C pt => pt)
  (fun A B C pt => bump (bitSize A) pt)
).

Lemma translate_spec {A B : Ty} (t : Term A B) :
 spec (@Core.eval _ _ t translate) t.
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

Local Open Scope thrist_scope.

Theorem translate_correct {A B : Ty} (t : Term A B) a ctx :
 { thr : fillContext ctx (LocalStateBegin t a)
     ->> fillContext ctx (LocalStateEnd t a)
 | @Core.eval _ _ t translate (fillContext ctx (LocalStateBegin t a)) = Some (existT _ _ thr)
 }.
generalize (translate_spec t a ctx).
unfold runMachine.
destruct (Core.eval _) as [[y thr] |];[|abstract discriminate].
cbn; intros Hy.
assert (Hy' : y = fillContext ctx (LocalStateEnd t a)).
 abstract (injection Hy; auto).
refine (exist _ (thr |><| eq_nil Hy') _).
abstract
(f_equal
;destruct Hy'
;cbn
;rewrite thrist_app_nil
;reflexivity
).
Defined.

Local Open Scope core_alg_scope.

Theorem translate_correct_parametric {A B : Ty} (t : forall {term : Core.Algebra}, term A B) (Ht : Core.Parametric (@t)) a ctx :
 { thr : fillContext ctx {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |}
     ->> fillContext ctx {| readLocalState := encode a; writeLocalState := fullWriteFrame (encode (|[ t ]| a)) |}
 | @t translate (fillContext ctx {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |}) = Some (existT _ _ thr)
 }.
set (ctxB := fillContext ctx _).
set (ctxA := fillContext ctx _).
set (t0 := t Core.Term : Term A B) in *.
assert (H0 : option_map (projT1 (P:=fun y0 : State => ctxA ->> y0)) (t translate ctxA) =
        Some (fillContext ctx (LocalStateEnd t0 a))) by
  abstract (rewrite (Core.term_eval Ht); apply (translate_spec t0 a ctx)).
destruct (t translate ctxA) as [[y thr] |]; cbn in H0;[|abstract discriminate].
enough (y = ctxB) as Hy.
 refine (exist _ (thr |><| eq_nil Hy) _).
 abstract (destruct Hy; cbn; rewrite thrist_app_nil; reflexivity).
abstract
(injection H0; clear H0
;intros ->
;unfold ctxB
;rewrite (Core.term_eval Ht), <- CoreSem_correct
;reflexivity
).
Defined.

End Naive.