Require Import PeanoNat.
Require Import Util.List.
Require Import Util.Option.
Require Import Util.Thrist.
Require Import Eqdep_dec.
Require Import Omega.

Definition Cell := option bool.

(* Write-only frames are append only.  We represent the frame by, writeData,
 * the list of cells before the frame's cursor, and by writeEmpty, which
 * contains the number of undefined cells after the cursor.
 *
 * The writeData store the list of cells in reverse order! This is analogous to
 * the zipper used in ReadFrame below.
 *)
Record WriteFrame :=
 { writeData : list Cell
 ; writeEmpty : nat
 }.

Definition writeSize wf := length (writeData wf) + (writeEmpty wf).

Definition newWriteFrame n : WriteFrame := {| writeData := nil; writeEmpty := n |}.

(* Note that fullWriteFrame take a list of cells in forward order and
 * transforms it into the reverse representation.
 *)
Definition fullWriteFrame l : WriteFrame := {| writeData := rev l; writeEmpty := 0 |}.

Lemma fullWriteFrame_size l : writeSize (fullWriteFrame l) = length l.
Proof.
cbn.
rewrite rev_length.
auto with arith.
Qed.

(* Read-only frames are represented in zipper format.  The cells before the
 * cursor are stored in prevData in reverse order.  The cells after the cursor
 * are stored in nextData in forward order.
 *)
Record ReadFrame :=
 { prevData : list Cell
 ; nextData : list Cell
 }.

Definition readSize rf := length (prevData rf) + length (nextData rf).

Definition setFrame l := {| prevData := nil; nextData := l |}.

(* The full state of the Bit Machine is captured by a list of inactive
 * read-only and write-only frames.  The top of the two stacks are held in the
 * activeReadFrame and activeWriteFrame.  This ensures that both stacks are
 * non-empty.
 *)
Record State :=
 { inactiveReadFrames : list ReadFrame
 ; activeReadFrame : ReadFrame
 ; activeWriteFrame : WriteFrame
 ; inactiveWriteFrames : list WriteFrame
 }.

Lemma State_dec (x y : State) : {x = y} + {x <> y}.
Proof.
repeat (decide equality).
Qed.

Record StateShape :=
 { inactiveReadFrameSizes : list nat
 ; activeReadFrameSize : nat
 ; activeWriteFrameSize : nat
 ; inactiveWriteFrameSizes : list nat
 }.

Definition stateShape s :=
 {| inactiveReadFrameSizes := map readSize (inactiveReadFrames s)
  ; activeReadFrameSize := readSize (activeReadFrame s)
  ; activeWriteFrameSize := writeSize (activeWriteFrame s)
  ; inactiveWriteFrameSizes := map writeSize (inactiveWriteFrames s)
  |}.

Definition stateShapeSize s :=
  nat_sum (inactiveReadFrameSizes s) +
  activeReadFrameSize s +
  activeWriteFrameSize s +
  nat_sum (inactiveWriteFrameSizes s).

Definition stateSize s := stateShapeSize (stateShape s).

(* Logically, the state of the Bit Machine is commonly divided between the part
 * of the state that we are focused on and the rest of state.  The focused part
 * consists of some fragment of data after the cursor in the read-only frame,
 * which contains the encoding of the input to some sub-expression in
 * Simplicity, and some fragment of data around the cursor in the write-only
 * frame, which contins the, partially written, output of some sub-expression.
 *
 * This focused part of the state is captured by the LocalState type.
 * The remainder of the state is captured by the Context type, and happens to
 * be isomorphic to the State type.  The fillContext function combines the
 * LocalState with some context to produce a complete state.
 *)
Definition Context := State.

Definition emptyCtx : Context :=
 {| inactiveReadFrames := nil
  ; activeReadFrame := setFrame nil
  ; activeWriteFrame := newWriteFrame 0
  ; inactiveWriteFrames := nil
  |}.

Record LocalState :=
 { readLocalState : list Cell
 ; writeLocalState : WriteFrame
 }.

Record LocalStateShape :=
 { readLocalStateSize : nat
 ; writeLocalStateSize : nat
 }.

Definition localStateShape ls :=
 {| readLocalStateSize := length (readLocalState ls)
  ; writeLocalStateSize := writeSize (writeLocalState ls)
  |}.

Definition localStateShapeSize ls :=
  readLocalStateSize ls +
  writeLocalStateSize ls.

Definition localStateSize ls := localStateShapeSize (localStateShape ls).

Definition fillContext (ctx : Context) (h : LocalState) : State :=
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeReadFrame :=
      {| prevData := prevData (activeReadFrame ctx)
       ; nextData := readLocalState h ++ nextData (activeReadFrame ctx)
       |}
  ; activeWriteFrame :=
      {| writeData := writeData (writeLocalState h) ++ writeData (activeWriteFrame ctx)
       ; writeEmpty := writeEmpty (writeLocalState h) + writeEmpty (activeWriteFrame ctx)
       |}
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition fillContextShape (ctx : StateShape) (h : LocalStateShape) : StateShape :=
 {| inactiveReadFrameSizes := inactiveReadFrameSizes ctx
  ; activeReadFrameSize := activeReadFrameSize ctx + readLocalStateSize h
  ; activeWriteFrameSize := activeWriteFrameSize ctx + writeLocalStateSize h
  ; inactiveWriteFrameSizes := inactiveWriteFrameSizes ctx
  |}.

Lemma fillContextShape_correct ctx h :
  stateShape (fillContext ctx h) = fillContextShape (stateShape ctx) (localStateShape h).
Proof.
destruct ctx as [irf [prf nrf] awf iwf].
destruct h as [rl wl].
unfold stateShape, fillContextShape; simpl.
f_equal;[unfold readSize|unfold writeSize]; simpl;
rewrite app_length; omega.
Qed.

(* Sometimes we need to focus in on part of the LocalState.  We can divide the
 * LocalState into a localer state and its (relative) context.  Both the
 * localer state and its context are isomorphic to the LocalState type and we
 * do not give them separate types.
 * We define appendLocalState to combine ls2, a LocalState representing the
 * localer state, with ls1, a LocalState representing its relative context.
 * Note that this append operation makes LocalState a monoid.
 *)

Definition appendLocalState (ls1 ls2 : LocalState) : LocalState :=
 {| readLocalState := readLocalState ls2 ++ readLocalState ls1
  ; writeLocalState :=
    {| writeData := writeData (writeLocalState ls2) ++ writeData (writeLocalState ls1)
     ; writeEmpty := writeEmpty (writeLocalState ls2) + writeEmpty (writeLocalState ls1)
     |}
  |}.

(* The monoid for LocalState above makes fillContext into a (right) monoid
 * action on Contexts.
 *)
Lemma context_action ctx ls1 ls2 :
  fillContext (fillContext ctx ls1) ls2 = fillContext ctx (appendLocalState ls1 ls2).
Proof.
unfold fillContext.
cbn.
repeat rewrite app_assoc.
rewrite Plus.plus_assoc.
reflexivity.
Qed.

Definition fillReadFrame (ctx : Context) (h : ReadFrame) : State :=
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeReadFrame :=
      {| prevData := prevData h ++ prevData (activeReadFrame ctx)
       ; nextData := nextData h ++ nextData (activeReadFrame ctx)
       |}
  ; activeWriteFrame := activeWriteFrame ctx
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition fillReadFrameShape (ctx : StateShape) (h : nat) : StateShape :=
 {| inactiveReadFrameSizes := inactiveReadFrameSizes ctx
  ; activeReadFrameSize := activeReadFrameSize ctx + h
  ; activeWriteFrameSize := activeWriteFrameSize ctx
  ; inactiveWriteFrameSizes := inactiveWriteFrameSizes ctx
  |}.

Lemma fillReadFrameShape_correct ctx h :
  stateShape (fillReadFrame ctx h) = fillReadFrameShape (stateShape ctx) (readSize h).
Proof.
destruct ctx as [irf [prf nrf] awf iwf].
destruct h as [rl wl].
unfold stateShape, fillReadFrameShape; simpl.
f_equal.
unfold readSize; simpl.
repeat rewrite app_length; omega.
Qed.

Module MachineCode.

(* This machine code type specifies all legal basic Bit Machine state
 * transitions.
 *)
Inductive T : State -> State -> Set :=
| NewFrame : forall n ctx,
    T ctx
      {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := newWriteFrame n
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}
| MoveFrame : forall l ctx,
    T {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := fullWriteFrame l
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}
      {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := setFrame l
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}
| DropFrame : forall rf ctx,
    T {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := rf
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}
      ctx
| Write : forall b ctx,
    T (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame 1
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (Some b :: nil)
                        |})
| Skip : forall n ctx,
    T (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame n
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (repeat None n)
                        |})
| Copy : forall l ctx,
    T (fillContext ctx {| readLocalState := l
                        ; writeLocalState := newWriteFrame (length l)
                        |})
      (fillContext ctx {| readLocalState := l
                        ; writeLocalState := fullWriteFrame l
                        |})
| Fwd : forall l ctx,
    T (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |})
      (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |})
| Bwd : forall l ctx,
    T (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |})
      (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |}).

End MachineCode.

(* For each basic instruction we define function to check if a given state s is
 * valid state that the instruction can execute in.  If it is valid we return
 * a witness proving that s can be expressed in the form of a valid state. Each
 * function also has a correctness function that proves that any state that is
 * in the form of a valid state, the check function return success.  The
 * NewFrame instruction is valid in every state and therefore doesn't have a
 * check function.
 *)
Definition MoveFrame_chk s :
  option { lctx : list Cell * Context | let (l, ctx) := lctx in s =
      {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := fullWriteFrame l
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}}.
destruct s as [irf arf [l n] [|awf iwf]].
 exact None.
destruct n as [|n];[|exact None].
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := arf
              ; activeWriteFrame := awf
              ; inactiveWriteFrames := iwf
              |}).
left.
exists (rev l, ctx).
unfold fullWriteFrame.
abstract (rewrite rev_involutive; reflexivity).
Defined.

Lemma MoveFrame_chk_correct l ctx : MoveFrame_chk
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeReadFrame := activeReadFrame ctx
  ; activeWriteFrame := fullWriteFrame l
  ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
  |} = Some (exist _ (l, ctx) (refl_equal _)).
Proof.
cbn.
set (H := (MoveFrame_chk_subproof _ _ _ _ _)).
generalize H; clear H.
rewrite (rev_involutive l).
apply (K_dec_set State_dec).
destruct ctx as [irf arf awf iwf].
reflexivity.
Qed.

Definition DropFrame_chk s :
  option { rfctx : ReadFrame * Context | let (rf, ctx) := rfctx in s =
      {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := rf
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}}.
destruct s as [[|arf irf] rf awf iwf].
 exact None.
left.
exists (rf, {| inactiveReadFrames := irf
             ; activeReadFrame := arf
             ; activeWriteFrame := awf
             ; inactiveWriteFrames := iwf
             |}).
reflexivity.
Defined.

Lemma DropFrame_chk_correct rf ctx : DropFrame_chk
 {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
  ; activeReadFrame := rf
  ; activeWriteFrame := activeWriteFrame ctx
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |} = Some (exist _ (rf, ctx) (refl_equal _)).
Proof.
destruct ctx; reflexivity.
Qed.

Definition Write_chk s :
  option { ctx : Context | s =
    fillContext ctx {| readLocalState := nil
                     ; writeLocalState := newWriteFrame 1
                     |}}.
destruct s as [irf [rp rn] [wd [|we]] iwf].
 exact None.
left.
exists {| inactiveReadFrames := irf
        ; activeReadFrame := {| prevData := rp; nextData := rn |}
        ; activeWriteFrame := {| writeData := wd; writeEmpty := we |}
        ; inactiveWriteFrames := iwf
        |}.
reflexivity.
Defined.

Lemma Write_chk_correct ctx : Write_chk
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame 1
                    |})
  = Some (exist _ ctx (refl_equal _)).
Proof.
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition Skip_chk n s :
  option { ctx : Context | s =
    fillContext ctx {| readLocalState := nil
                     ; writeLocalState := newWriteFrame n
                     |}}.
destruct s as [irf [rp rn] [wd we] iwf].
generalize (Nat.leb_spec n we).
destruct (n <=? we);intros H;[|exact None].
left.
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := {| prevData := rp; nextData := rn |}
              ; activeWriteFrame := {| writeData := wd; writeEmpty := we - n |}
              ; inactiveWriteFrames := iwf
              |}).
exists ctx.
abstract (
  unfold fillContext; cbn;
  inversion_clear H as [Hn|];
  rewrite <- (Minus.le_plus_minus _ _ Hn);
  reflexivity).
Defined.

Lemma Skip_chk_correct n ctx : Skip_chk n
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame n
                    |})
  = Some (exist _ ctx (refl_equal _)).
Proof.
cbn.
destruct (Nat.leb_spec n (n + writeEmpty (activeWriteFrame ctx))) as [H0|H0];
 [|elim (Lt.lt_not_le _ _ H0); auto with arith].
set (H := (Skip_chk_subproof _ _ _ _ _ _ _ _)).
generalize H; clear H.
rewrite Minus.minus_plus.
apply (K_dec_set State_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition Copy_chk n s :
  option { lctx : list Cell * Context | let (l, ctx) := lctx in n = length l /\ s =
    fillContext ctx {| readLocalState := l
                     ; writeLocalState := newWriteFrame (length l)
                     |}}.
destruct s as [irf [rp rn] [wd we] iwf].
generalize (Nat.leb_spec n we).
destruct (n <=? we);intros Hwe;[|exact None].
generalize (Nat.leb_spec n (length rn)).
destruct (n <=? length rn);intros Hrn;[|exact None].
left.
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := {| prevData := rp; nextData := skipn n rn |}
              ; activeWriteFrame := {| writeData := wd; writeEmpty := we - n |}
              ; inactiveWriteFrames := iwf
              |}).
exists (firstn n rn, ctx).
split.
- abstract
(inversion_clear Hrn as [H|];
 rewrite (firstn_length_le _ H);
 reflexivity).
- abstract
(inversion_clear Hrn as [H|];
 rewrite (firstn_length_le _ H);
 clear H;
 unfold fillContext; cbn;
 inversion_clear Hwe as [H|];
 rewrite firstn_skipn, <- (Minus.le_plus_minus _ _ H);
 reflexivity).
Defined.

Lemma Copy_chk_correct l ctx : Copy_chk (length l)
  (fillContext ctx {| readLocalState := l
                    ; writeLocalState := newWriteFrame (length l)
                    |})
  = Some (exist _ (l, ctx) (conj (refl_equal _) (refl_equal _))).
Proof.
cbn.
destruct (Nat.leb_spec (length l) (length l + writeEmpty (activeWriteFrame ctx))) as [H0|H0];
 [|elim (Lt.lt_not_le _ _ H0); auto with arith].
destruct (Nat.leb_spec (length l) (length (l ++ nextData (activeReadFrame ctx)))) as [H1|H1];
 [|elim (Lt.lt_not_le _ _ H1); rewrite app_length; auto with arith].
set (H := (Copy_chk_subproof _ _ _)).
generalize H; clear H.
set (H := (Copy_chk_subproof0 _ _ _ _ _ _ _ _ _)).
generalize H; clear H.
rewrite firstn_app_3, Minus.minus_plus, skipn_app_3.
intros H; elim H using (K_dec_set State_dec); clear H.
apply (K_dec_set Nat.eq_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition Fwd_chk n s :
  option { lctx : list Cell * Context | let (l, ctx) := lctx in n = length l /\ s =
    fillReadFrame ctx {| prevData := nil
                       ; nextData := l
                       |}}.
destruct s as [irf [rp rn] awf iwf].
generalize (Nat.leb_spec n (length rn)).
destruct (n <=? length rn);intros Hrn;[|exact None].
left.
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := {| prevData := rp; nextData := skipn n rn |}
              ; activeWriteFrame := awf
              ; inactiveWriteFrames := iwf
              |}).
exists (firstn n rn, ctx).
abstract(
split;[
 inversion_clear Hrn as [H|];
 rewrite (firstn_length_le _ H);
 reflexivity
|unfold fillReadFrame; cbn;
 inversion_clear Hrn as [H|];
 rewrite firstn_skipn;
 reflexivity
]).
Defined.

Lemma Fwd_chk_correct l ctx : Fwd_chk (length l)
  (fillReadFrame ctx {| prevData := nil
                      ; nextData := l
                      |})
  = Some (exist _ (l, ctx) (conj (refl_equal _) (refl_equal _))).
Proof.
cbn.
destruct (Nat.leb_spec (length l) (length (l ++ nextData (activeReadFrame ctx)))) as [H0|H0];
 [|elim (Lt.lt_not_le _ _ H0); rewrite app_length; auto with arith].
set (H := (Fwd_chk_subproof _ _ _ _ _ _ _)).
generalize H; clear H.
rewrite firstn_app_3, skipn_app_3.
intros [eq0 eq1].
elim eq0 using (K_dec_set Nat.eq_dec).
elim eq1 using (K_dec_set State_dec).
clear eq0 eq1.
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition Bwd_chk n s :
  option { lctx : list Cell * Context | let (l, ctx) := lctx in n = length l /\ s =
    fillReadFrame ctx {| prevData := rev l
                       ; nextData := nil
                       |}}.
destruct s as [irf [rp rn] awf iwf].
generalize (Nat.leb_spec n (length rp)).
destruct (n <=? length rp);intros Hrp;[|exact None].
left.
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := {| prevData := skipn n rp; nextData := rn |}
              ; activeWriteFrame := awf
              ; inactiveWriteFrames := iwf
              |}).
exists (rev (firstn n rp), ctx).
abstract(split;
[inversion_clear Hrp as [H|];
 rewrite rev_length, (firstn_length_le _ H);
 reflexivity
|unfold fillReadFrame; cbn;
 inversion_clear Hrp as [H|];
 rewrite rev_involutive, firstn_skipn;
 reflexivity
]).
Defined.

Lemma Bwd_chk_correct l ctx : Bwd_chk (length l)
  (fillReadFrame ctx {| prevData := rev l
                      ; nextData := nil
                      |})
  = Some (exist _ (l, ctx) (conj (refl_equal _) (refl_equal _))).
Proof.
cbn.
destruct (Nat.leb_spec (length l) (length (rev l ++ prevData (activeReadFrame ctx)))) as [H0|H0];
 [|elim (Lt.lt_not_le _ _ H0); rewrite app_length, rev_length; auto with arith].
set (H := (Bwd_chk_subproof _ _ _ _ _ _ _)).
generalize H; clear H.
replace (firstn (length l)) with (@firstn Cell (length (rev l))) by
  (rewrite rev_length; reflexivity).
replace (skipn (length l)) with (@skipn Cell (length (rev l))) by
  (rewrite rev_length; reflexivity).
rewrite firstn_app_3, skipn_app_3, rev_involutive.
intros [eq0 eq1].
elim eq0 using (K_dec_set Nat.eq_dec).
elim eq1 using (K_dec_set State_dec).
clear eq0 eq1.
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Local Open Scope thrist_scope.

Notation "x ~~> y" := (MachineCode.T x y) (at level 70) : type_scope.
Notation "x ->> y" := (Thrst MachineCode.T x y) (at level 70) : type_scope.

(* A Bit Machine programs takes an inital state, x, and tries to produce a
 * thrist of basic state transformations to some final state, y. However, a
 * can potentially crash instead if it cannot execute successfully given the
 * inital state.
 *)
Definition Program := forall x : State, option { y : State & x ->> y }.

(* The nop program has no basic instructions. *)
Definition nop : Program :=
  fun x => Some (existT _ x []).

(* For each basic instruction we define a program that executes only that
 * single instruction.  For each instruction we have a correctness lemma
 * that describes the result of the program when executed with an initial
 * state that is legal for that instruction.
 *)

(* The newFrame instruction is legal to execute in any initial state.  We don't
 * provide a correctness function for it since it can be evaluated inside Coq
 * on any abstract input (i.e. it doesn't need any iota reductions).
 *)
Definition newFrame (n : nat) : Program :=
  fun x => Some (existT _ _ (MachineCode.NewFrame n x <| [])).

Definition moveFrame : Program.
intros s.
destruct (MoveFrame_chk s) as [P|];[left|right].
destruct P as [[l ctx] Hs].
exact (existT _ _ (eq_nil Hs |> MachineCode.MoveFrame l ctx)).
Defined.

Lemma moveFrame_correct : forall l ctx, moveFrame
  {| inactiveReadFrames := inactiveReadFrames ctx
   ; activeReadFrame := activeReadFrame ctx
   ; activeWriteFrame := fullWriteFrame l
   ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
   |} = Some (existT _ _ (MachineCode.MoveFrame l ctx <| [])).
Proof.
intros l ctx.
unfold moveFrame.
rewrite MoveFrame_chk_correct.
reflexivity.
Qed.

Definition dropFrame : Program.
intros s.
destruct (DropFrame_chk s) as [P|];[left|right].
destruct P as [[rf ctx] Hs].
exact (existT _ _ (eq_nil Hs |> MachineCode.DropFrame rf ctx)).
Defined.

Lemma dropFrame_correct : forall rf ctx, dropFrame
  {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
   ; activeReadFrame := rf
   ; activeWriteFrame := activeWriteFrame ctx
   ; inactiveWriteFrames := inactiveWriteFrames ctx
   |} = Some (existT _ _ (MachineCode.DropFrame rf ctx <| [])).
Proof.
intros l ctx.
unfold dropFrame.
rewrite DropFrame_chk_correct.
reflexivity.
Qed.

Definition write (b : bool) : Program.
intros s.
destruct (Write_chk s) as [P|];[left|right].
destruct P as [ctx Hs].
exact (existT _ _ (eq_nil Hs |> MachineCode.Write b ctx)).
Defined.

Lemma write_correct : forall b ctx, write b
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame 1
                    |}) = Some (existT _ _ (MachineCode.Write b ctx <| [])).
Proof.
intros l ctx.
unfold write.
rewrite Write_chk_correct.
reflexivity.
Qed.

Definition skip (n : nat) : Program.
intros s.
destruct (Skip_chk n s) as [P|];[left|right].
destruct P as [ctx Hs].
exact (existT _ _ (eq_nil Hs |> MachineCode.Skip n ctx)).
Defined.

Lemma skip_correct : forall n ctx, skip n
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame n
                    |}) = Some (existT _ _ (MachineCode.Skip n ctx <| [])).
Proof.
intros l ctx.
unfold skip.
rewrite Skip_chk_correct.
reflexivity.
Qed.

Definition copy (n : nat) : Program.
intros s.
destruct (Copy_chk n s) as [P|];[left|right].
destruct P as [[l ctx] [_ Hs]].
exact (existT _ _ (eq_nil Hs |> MachineCode.Copy l ctx)).
Defined.

Lemma copy_correct : forall l ctx, copy (length l)
  (fillContext ctx {| readLocalState := l
                    ; writeLocalState := newWriteFrame (length l)
                    |}) = Some (existT _ _ (MachineCode.Copy l ctx <| [])).
Proof.
intros l ctx.
unfold copy.
rewrite Copy_chk_correct.
reflexivity.
Qed.

Definition fwd (n : nat) : Program.
intros s.
destruct (Fwd_chk n s) as [P|];[left|right].
destruct P as [[l ctx] [_ Hs]].
exact (existT _ _ (eq_nil Hs |> MachineCode.Fwd l ctx)).
Defined.

Lemma fwd_correct : forall l ctx, fwd (length l)
  (fillReadFrame ctx {| prevData := nil
                      ; nextData := l
                      |}) = Some (existT _ _ (MachineCode.Fwd l ctx <| [])).
Proof.
intros l ctx.
unfold fwd.
rewrite Fwd_chk_correct.
reflexivity.
Qed.

Definition bwd (n : nat) : Program.
intros s.
destruct (Bwd_chk n s) as [P|];[left|right].
destruct P as [[l ctx] [_ Hs]].
exact (existT _ _ (eq_nil Hs |> MachineCode.Bwd l ctx)).
Defined.

Lemma bwd_correct : forall l ctx, bwd (length l)
  (fillReadFrame ctx {| prevData := rev l
                      ; nextData := nil
                      |}) = Some (existT _ _ (MachineCode.Bwd l ctx <| [])).
Proof.
intros l ctx.
unfold bwd.
rewrite Bwd_chk_correct.
reflexivity.
Qed.

(* The basic instruction crash always crashes the machine.  Crash doesn't
 * appear in the MachineCode.T because there is no state that is can
 * successfuly be executed in.  For the same reason it has no correctness
 * lemma.
 *)
Definition crash : Program :=
  fun x => None.

(* There are two combinators for building larger programs from smaller ones:
 * seq runs two programs, one after the other.  choice runs one of two programs
 * depending on whether the Cell value under the cursor on the active read
 * frame is a 0 or a 1.
 *)
Definition seq (p1 p2 : Program) : Program.
intros x.
destruct (p1 x) as [[y thr1]|];[|exact None].
destruct (p2 y) as [[z thr2]|];[|exact None].
exact (Some (existT _ _ (thr1 |><| thr2))).
Defined.
Notation "p1 ;;; p2" := (seq p1 p2) (at level 40, left associativity) : mc_scope.

Definition choice (p1 p2 : Program) : Program.
intros x.
destruct (nextData (activeReadFrame x)) as [|[b|] tl];[exact None| |exact None].
exact ((if b then p2 else p1) x).
Defined.
Notation "p1 ||| p2" := (choice p1 p2) (at level 50, left associativity) : mc_scope.

Local Open Scope mc_scope.

(* bump is notation for a program that is run where the active read frame's
 * cursor is temporarily advanced.
 *)
Definition bump n p : Program := fwd n ;;; p ;;; bwd n.

(* runMachine extracts the final state after executing a program, if
 * successful.
 *)
Definition runMachine (p : Program) (s : State) : option State :=
option_map (@projT1 _ _) (p s).


(* The following lemma describe the behaviour of program cominators with
 * runMachine.
 *)
Lemma runMachine_seq (p1 p2 : Program) (s : State) :
 runMachine (p1 ;;; p2) s = option_bind (runMachine p2) (runMachine p1 s).
Proof.
unfold runMachine, seq.
destruct (p1 s) as [[s0 thr0]|];[|reflexivity].
cbn.
destruct (p2 s0) as [[s1 thr1]|];reflexivity.
Qed.

Lemma runMachine_choice (p1 p2 : Program) (s : State) :
 runMachine (p1 ||| p2) s = match nextData (activeReadFrame s) with
 | Some b :: _ => runMachine (if b then p2 else p1) s
 | _ => None
 end.
Proof.
destruct s as [irf [rp [|[|] tl]] awf iwf]; reflexivity.
Qed.

Lemma runMachine_bump (p : Program) l ctx0 ctx1 :
 runMachine p
   (fillReadFrame ctx0 {| prevData := rev l; nextData := nil |}) =
   Some (fillReadFrame ctx1 {| prevData := rev l; nextData := nil |}) ->
 runMachine (bump (length l) p)
   (fillReadFrame ctx0 {| prevData := nil; nextData := l |}) =
   Some (fillReadFrame ctx1 {| prevData := nil; nextData := l |}).
Proof.
intros Hp.
unfold bump.
repeat rewrite runMachine_seq.
unfold runMachine at 3.
rewrite fwd_correct; cbn.
rewrite Hp; cbn.
unfold runMachine.
rewrite bwd_correct.
reflexivity.
Qed.
