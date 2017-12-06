Require Import PeanoNat.
Require Import NArith.
Require Import Util.List.
Require Import Util.Option.
Require Import Util.Thrist.
Require Import Eqdep_dec.

Local Open Scope N_scope.

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

Definition writeSize wf := N.of_nat (length (writeData wf)) + N.of_nat (writeEmpty wf).

Definition newWriteFrame n : WriteFrame := {| writeData := nil; writeEmpty := n |}.

(* Note that fullWriteFrame take a list of cells in forward order and
 * transforms it into the reverse representation.
 *)
Definition fullWriteFrame l : WriteFrame := {| writeData := rev l; writeEmpty := 0 |}.

Lemma fullWriteFrame_size l : writeSize (fullWriteFrame l) = N.of_nat (length l).
Proof.
unfold writeSize; cbn.
rewrite rev_length.
ring.
Qed.

(* Read-only frames are represented in zipper format.  The cells before the
 * cursor are stored in prevData in reverse order.  The cells after the cursor
 * are stored in nextData in forward order.
 *)
Record ReadFrame :=
 { prevData : list Cell
 ; nextData : list Cell
 }.

Definition readSize rf := N.of_nat (length (prevData rf)) + N.of_nat (length (nextData rf)).

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
 { inactiveReadFrameSizes : list N
 ; activeReadFrameSize : N
 ; activeWriteFrameSize : N
 ; inactiveWriteFrameSizes : list N
 }.

Definition stateShape s :=
 {| inactiveReadFrameSizes := map readSize (inactiveReadFrames s)
  ; activeReadFrameSize := readSize (activeReadFrame s)
  ; activeWriteFrameSize := writeSize (activeWriteFrame s)
  ; inactiveWriteFrameSizes := map writeSize (inactiveWriteFrames s)
  |}.

Definition stateShapeSize s :=
  N_sum (inactiveReadFrameSizes s) +
  activeReadFrameSize s +
  activeWriteFrameSize s +
  N_sum (inactiveWriteFrameSizes s).

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
 { readLocalStateSize : N
 ; writeLocalStateSize : N
 }.

Definition localStateShape ls :=
 {| readLocalStateSize := N.of_nat (length (readLocalState ls))
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
rewrite app_length; repeat rewrite Nat2N.inj_add; ring.
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

Definition fillReadFrameShape (ctx : StateShape) (h : N) : StateShape :=
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
repeat rewrite app_length, Nat2N.inj_add; ring.
Qed.

Module MachineCode.

(* Although the types for the following instructions have the form of a
 * Proposition (i.e. they have at most one inhabitant) we put them in the Set
 * universe because we want to compute with the witness values.
 *)
Module NewFrame.

Inductive T n ctx : State -> Set :=
op : T n ctx
      {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := newWriteFrame n
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}.

(* This isn't really needed, but we add it for completeness *)
Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : State & T n s0 s1}.
right.
econstructor.
constructor.
Defined.

End NewFrame.

Module MoveFrame.

Inductive T : State -> State -> Set :=
op : forall l ctx, 
    T {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := fullWriteFrame l
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}
      {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := setFrame l
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}.

Definition chk s0 : (forall s1, T s0 s1 -> False)+{s1 : State & T s0 s1}.
destruct s0 as [irf arf [l n] [|awf iwf]].
 left;abstract (inversion 1).
destruct n as [|n];[|left;abstract (inversion 1)].
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := arf
              ; activeWriteFrame := awf
              ; inactiveWriteFrames := iwf
              |}).
right.
exists {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := setFrame (rev l)
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}.
pattern l at 1.
elim (rev_involutive l).
exact (op _ ctx).
Defined.

End MoveFrame.

Module DropFrame.

Inductive T : State -> State -> Set :=
op : forall rf ctx, 
    T {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := rf
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}
      ctx.

Definition chk s0 : (forall s1, T s0 s1 -> False)+{s1 : State & T s0 s1}.
destruct s0 as [[|arf irf] rf awf iwf].
 left;abstract (inversion 1).
right.
pose (ctx := {| inactiveReadFrames := irf
              ; activeReadFrame := arf
              ; activeWriteFrame := awf
              ; inactiveWriteFrames := iwf
              |}).
exists ctx.
exact (op rf ctx).
Defined.

End DropFrame.

Module Write.

Inductive T b : State -> State -> Set :=
op : forall ctx, 
    T b 
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame 1
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (Some b :: nil)
                        |}).

Definition chk b s0 : (forall s1, T b s0 s1 -> False)+{s1 : State & T b s0 s1}.
destruct s0 as [irf [rp rn] [wd [|we]] iwf].
 left;abstract (inversion 1).
right.
eexists.
exact (op _ {| inactiveReadFrames := irf
        ; activeReadFrame := {| prevData := rp; nextData := rn |}
        ; activeWriteFrame := {| writeData := wd; writeEmpty := we |}
        ; inactiveWriteFrames := iwf
        |}).
Defined.

End Write.

Module Skip.

Inductive T n : State -> State -> Set :=
op : forall ctx, 
    T n
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame n
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (repeat None n)
                        |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : State & T n s0 s1}.
destruct s0 as [irf [rp rn] [wd we] iwf].
generalize (Nat.leb_spec n we).
destruct (n <=? we)%nat;intros H.
 right.
 pose (ctx := {| inactiveReadFrames := irf
               ; activeReadFrame := {| prevData := rp; nextData := rn |}
               ; activeWriteFrame := {| writeData := wd; writeEmpty := we - n |}
               ; inactiveWriteFrames := iwf
               |}).
 exists (fillContext ctx {| readLocalState := nil
                          ; writeLocalState := fullWriteFrame (repeat None n)
                          |}).
 elim (Minus.le_plus_minus_r n we).
  exact (op _ ctx).
 abstract (inversion_clear H; assumption).
left.
abstract(
 inversion 1;
 apply (Lt.lt_not_le we n);
 [inversion_clear H; assumption
 |replace <- we;auto with arith
 ]).
Defined.

End Skip.

Module Copy.

Inductive T n : State -> State -> Set :=
op : forall l ctx, length l = n -> 
    T n
      (fillContext ctx {| readLocalState := l
                        ; writeLocalState := newWriteFrame n
                        |})
      (fillContext ctx {| readLocalState := l
                        ; writeLocalState := fullWriteFrame l
                        |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : State & T n s0 s1}.
destruct s0 as [irf [rp rn] [wd we] iwf].
generalize (Nat.leb_spec n we).
destruct (n <=? we)%nat;intros Hwe.
 generalize (Nat.leb_spec n (length rn)).
 destruct (n <=? length rn)%nat;intros Hrn.
  right.
  pose (ctx := {| inactiveReadFrames := irf
                ; activeReadFrame := {| prevData := rp; nextData := skipn n rn |}
                ; activeWriteFrame := {| writeData := wd; writeEmpty := we - n |}
                ; inactiveWriteFrames := iwf
                |}).
  pose (l := firstn n rn).
  exists (fillContext ctx {| readLocalState := l
                           ; writeLocalState := fullWriteFrame l
                           |}).
  elim (firstn_skipn n rn).
  elim (Minus.le_plus_minus_r n we).
   refine (op n l ctx _).
   abstract (apply (firstn_length_le _); inversion_clear Hrn; assumption).
  abstract (inversion_clear Hwe; assumption).
 left.
 abstract (
  inversion 1;
  apply (Lt.lt_not_le (length rn) n);
  [inversion_clear Hrn; assumption
  |replace <- rn; replace <- n; rewrite app_length; auto with arith
  ]).
left.
abstract(
 inversion 1;
 apply (Lt.lt_not_le we n);
 [inversion_clear Hwe; assumption
 |replace <- we;auto with arith
 ]).
Defined.

End Copy.

Module Fwd.

Inductive T n : State -> State -> Set :=
op : forall l ctx, length l = n -> 
    T n
      (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |})
      (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : State & T n s0 s1}.
Proof.
destruct s0 as [irf [rp rn] awf iwf].
generalize (Nat.leb_spec n (length rn)).
destruct (n <=? length rn)%nat;intros Hrn.
 right.
 pose (ctx := {| inactiveReadFrames := irf
               ; activeReadFrame := {| prevData := rp; nextData := skipn n rn |}
               ; activeWriteFrame := awf
               ; inactiveWriteFrames := iwf
               |}).
 pose (l := firstn n rn).
 exists (fillReadFrame ctx {| prevData := rev l
                            ; nextData := nil
                            |}).
 elim (firstn_skipn n rn).
 refine (op n l ctx _).
 abstract (apply (firstn_length_le _); inversion_clear Hrn; assumption).
left.
abstract (
 inversion 1;
 apply (Lt.lt_not_le (length rn) n);
 [inversion_clear Hrn; assumption
 |replace <- rn; replace <- n; rewrite app_length; auto with arith
 ]).
Defined.

End Fwd.

Module Bwd.

Inductive T n : State -> State -> Set :=
op : forall l ctx, length l = n -> 
    T n
      (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |})
      (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : State & T n s0 s1}.
destruct s0 as [irf [rp rn] awf iwf].
generalize (Nat.leb_spec n (length rp)).
destruct (n <=? length rp)%nat;intros Hrp.
 right.
 pose (ctx := {| inactiveReadFrames := irf
               ; activeReadFrame := {| prevData := skipn n rp; nextData := rn |}
               ; activeWriteFrame := awf
               ; inactiveWriteFrames := iwf
               |}).
 pose (l := rev (firstn n rp)).
 exists (fillReadFrame ctx {| prevData := nil
                            ; nextData := l
                            |}).
 elim (firstn_skipn n rp).
 elim (rev_involutive (firstn n rp)).
 refine (op n l ctx _).
 abstract (unfold l; rewrite rev_length; apply (firstn_length_le _); inversion_clear Hrp; assumption).
left.
abstract(
 inversion 1;
 apply (Lt.lt_not_le (length rp) n);
 [inversion_clear Hrp; assumption
 |replace <- rp; replace <- n; rewrite app_length, rev_length; auto with arith
 ]).
Defined.

End Bwd.

(* This machine code type specifies all legal basic Bit Machine state
 * transitions.
 *)
Inductive T (s0 s1 : State) : Set :=
| NewFrame : forall n, NewFrame.T n s0 s1 -> T s0 s1
| MoveFrame : MoveFrame.T s0 s1 -> T s0 s1
| DropFrame : DropFrame.T s0 s1 -> T s0 s1
| Write : forall b, Write.T b s0 s1 -> T s0 s1
| Skip : forall n, Skip.T n s0 s1 -> T s0 s1
| Copy : forall n, Copy.T n s0 s1 -> T s0 s1
| Fwd : forall n, Fwd.T n s0 s1 -> T s0 s1
| Bwd : forall n, Bwd.T n s0 s1 -> T s0 s1.
Arguments NewFrame [s0 s1].
Arguments MoveFrame [s0 s1].
Arguments DropFrame [s0 s1].
Arguments Write [s0 s1].
Arguments Skip [s0 s1].
Arguments Copy [s0 s1].
Arguments Fwd [s0 s1].
Arguments Bwd [s0 s1].

Definition newFrame n ctx : T _ _ :=
 NewFrame _ (NewFrame.op n ctx).

Definition moveFrame l ctx : T _ _ :=
 MoveFrame (MoveFrame.op l ctx).

Definition dropFrame l ctx : T _ _ :=
 DropFrame (DropFrame.op l ctx).

Definition write b ctx : T _ _ :=
 Write _ (Write.op b ctx).

Definition skip n ctx : T _ _ :=
 Skip _ (Skip.op n ctx).

Definition copy l ctx : T _ _ :=
 Copy _ (Copy.op (length l) l ctx (refl_equal _)).

Definition fwd l ctx : T _ _ :=
 Fwd _ (Fwd.op (length l) l ctx (refl_equal _)).

Definition bwd l ctx : T _ _ :=
 Bwd _ (Bwd.op (length l) l ctx (refl_equal _)).

End MachineCode.

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
  fun x => Some (existT _ _ (MachineCode.newFrame n x <| [])).

Definition moveFrame : Program.
intros s0.
destruct (MachineCode.MoveFrame.chk s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.MoveFrame t <| []).
Defined.

Lemma moveFrame_correct : forall l ctx, moveFrame
  {| inactiveReadFrames := inactiveReadFrames ctx
   ; activeReadFrame := activeReadFrame ctx
   ; activeWriteFrame := fullWriteFrame l
   ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
   |} = Some (existT _ _ (MachineCode.moveFrame l ctx <| [])).
Proof.
intros l ctx.
cbn.
generalize (rev_involutive (rev l)).
rewrite (rev_involutive l).
apply K_dec_set.
 repeat decide equality.
destruct ctx; reflexivity.
Qed.

Definition dropFrame : Program.
intros s0.
destruct (MachineCode.DropFrame.chk s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.DropFrame t <| []).
Defined.

Lemma dropFrame_correct : forall rf ctx, dropFrame
  {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
   ; activeReadFrame := rf
   ; activeWriteFrame := activeWriteFrame ctx
   ; inactiveWriteFrames := inactiveWriteFrames ctx
   |} = Some (existT _ _ (MachineCode.dropFrame rf ctx <| [])).
Proof.
intros rf ctx.
destruct ctx; reflexivity.
Qed.

Definition write (b : bool) : Program.
intros s0.
destruct (MachineCode.Write.chk b s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.Write b t <| []).
Defined.

Lemma write_correct : forall b ctx, write b
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame 1
                    |}) = Some (existT _ _ (MachineCode.write b ctx <| [])).
Proof.
intros b [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition skip (n : nat) : Program.
intros s0.
destruct (MachineCode.Skip.chk n s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.Skip n t <| []).
Defined.

Lemma skip_correct : forall n ctx, skip n
  (fillContext ctx {| readLocalState := nil
                    ; writeLocalState := newWriteFrame n
                    |}) = Some (existT _ _ (MachineCode.skip n ctx <| [])).
Proof.
intros n ctx.
unfold skip.
cbn.
set (H := Nat.leb_spec _ _).
generalize H; clear H.
rewrite (Compare_dec.leb_correct n (n + writeEmpty (activeWriteFrame ctx))%nat)
  by auto with arith.
intros H.
set (e := Minus.le_plus_minus_r _ _ _).
generalize e; clear e.
rewrite Minus.minus_plus.
apply (K_dec_set Nat.eq_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition copy (n : nat) : Program.
intros s0.
destruct (MachineCode.Copy.chk n s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.Copy n t <| []).
Defined.

Lemma copy_correct : forall l ctx, copy (length l)
  (fillContext ctx {| readLocalState := l
                    ; writeLocalState := newWriteFrame (length l)
                    |}) = Some (existT _ _ (MachineCode.copy l ctx <| [])).
Proof.
intros l ctx.
unfold copy.
cbn.
set (H := Nat.leb_spec _ (_ + writeEmpty _)%nat).
generalize H; clear H.
rewrite (Compare_dec.leb_correct (length l) (length l + writeEmpty (activeWriteFrame ctx))%nat)
  by auto with arith.
intros H.
set (H1 := Nat.leb_spec _ _).
generalize H1; clear H1.
rewrite (Compare_dec.leb_correct (length l) (length (l ++ nextData (activeReadFrame ctx))))
  by (rewrite app_length;auto with arith).
intros H1.
set (e := Minus.le_plus_minus_r _ _ _).
generalize e; clear e.
rewrite Minus.minus_plus.
apply (K_dec_set Nat.eq_dec).
set (e := firstn_skipn _ _).
generalize e; clear e.
generalize (MachineCode.Copy.chk_subproof _ _ H1).
rewrite firstn_app_3, skipn_app_3; intros e.
apply (K_dec_set).
 repeat decide equality.
revert e.
apply (K_dec_set Nat.eq_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition fwd (n : nat) : Program.
intros s0.
destruct (MachineCode.Fwd.chk n s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.Fwd n t <| []).
Defined.

Lemma fwd_correct : forall l ctx, fwd (length l)
  (fillReadFrame ctx {| prevData := nil
                      ; nextData := l
                      |}) = Some (existT _ _ (MachineCode.fwd l ctx <| [])).
Proof.
intros l ctx.
unfold fwd; cbn.
set (H := Nat.leb_spec _ _).
generalize H; clear H.
rewrite (Compare_dec.leb_correct (length l) (length (l ++ nextData (activeReadFrame ctx))))
  by (rewrite app_length;auto with arith).
intros H1.
set (e := firstn_skipn _ _).
generalize e; clear e.
generalize (MachineCode.Fwd.chk_subproof _ _ H1).
rewrite firstn_app_3, skipn_app_3; intros e.
apply (K_dec_set).
 repeat decide equality.
revert e.
apply (K_dec_set Nat.eq_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
reflexivity.
Qed.

Definition bwd (n : nat) : Program.
intros s0.
destruct (MachineCode.Bwd.chk n s0) as [|[s1 t]];[right|left].
eexists.
exact (MachineCode.Bwd n t <| []).
Defined.

Lemma bwd_correct : forall l ctx, bwd (length l)
  (fillReadFrame ctx {| prevData := rev l
                      ; nextData := nil
                      |}) = Some (existT _ _ (MachineCode.bwd l ctx <| [])).
Proof.
intros l ctx.
unfold bwd; cbn.
set (H := Nat.leb_spec _ _).
generalize H; clear H.
rewrite (Compare_dec.leb_correct (length l) (length (rev l ++ prevData (activeReadFrame ctx))))
  by (rewrite app_length, rev_length;auto with arith).
intros H1.
set (e := firstn_skipn _ _).
generalize e; clear e.
generalize (MachineCode.Bwd.chk_subproof _ _ H1).
rewrite <- rev_length.
rewrite firstn_app_3, skipn_app_3; intros e.
apply K_dec_set.
 repeat decide equality.
set (e1 := rev_involutive (rev l)).
generalize e1; clear e1.
revert e; rewrite rev_involutive; intros e.
apply K_dec_set.
 repeat decide equality.
revert e.
rewrite rev_length.
apply (K_dec_set Nat.eq_dec).
destruct ctx as [irf [rp rn] [wd we] iwf].
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

Lemma stateShape_copy n x y :
 runMachine (copy n) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold copy, runMachine.
destruct (MachineCode.Copy.chk _ x) as [|[s1 [l ctx Hl]]];[discriminate|cbn].
inversion_clear 1.
do 2 rewrite fillContextShape_correct.
f_equal.
unfold localStateShape; cbn.
rewrite fullWriteFrame_size.
congruence.
Qed.

Lemma stateShape_write b x y :
 runMachine (write b) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold write, runMachine.
destruct (MachineCode.Write.chk _ x) as [|[s1 [ctx]]];[discriminate|cbn].
inversion_clear 1.
do 2 rewrite fillContextShape_correct.
reflexivity.
Qed.

Lemma stateShape_skip n x y :
 runMachine (skip n) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold skip, runMachine.
destruct (MachineCode.Skip.chk _ x) as [|[s1 [ctx]]];[discriminate|cbn].
inversion_clear 1.
do 2 rewrite fillContextShape_correct.
f_equal.
unfold localStateShape; cbn.
rewrite fullWriteFrame_size, repeat_length.
reflexivity.
Qed.

Lemma stateShape_fwd n x y :
 runMachine (fwd n) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold fwd, runMachine.
destruct (MachineCode.Fwd.chk _ x) as [|[s1 [ctx]]];[discriminate|cbn].
inversion_clear 1.
do 2 rewrite fillReadFrameShape_correct.
f_equal.
unfold readSize; cbn.
rewrite rev_length.
ring.
Qed.

Lemma stateShape_bwd n x y :
 runMachine (bwd n) x = Some y ->
 stateShape x = stateShape y.
Proof.
unfold bwd, runMachine.
destruct (MachineCode.Bwd.chk _ x) as [|[s1 [ctx]]];[discriminate|cbn].
inversion_clear 1.
do 2 rewrite fillReadFrameShape_correct.
f_equal.
unfold readSize; cbn.
rewrite rev_length.
ring.
Qed.

Fixpoint maximumMemoryResidence {x y} (tr : x ->> y) : N :=
match tr with
| Thrist.nil _ _ => stateSize y
| Thrist.cons _ _ z _ _ tr0 => N.max (stateSize z) (maximumMemoryResidence tr0)
end.

Lemma MMR_app {x y z} (tr0 : x ->> y) (tr1 : y ->> z) :
 maximumMemoryResidence (tr0 |><| tr1) =
 N.max (maximumMemoryResidence tr0) (maximumMemoryResidence tr1).
Proof.
induction tr0;cbn.
 induction tr1;cbn;[|rewrite N.max_assoc];rewrite N.max_id; reflexivity.
rewrite <- N.max_assoc, IHtr0.
reflexivity.
Qed.

Lemma MMR_bounds {x y} (tr0 : x ->> y) :
 N.max (stateSize x) (stateSize y) <= maximumMemoryResidence tr0.
Proof.
apply N.max_lub.
 destruct tr0.
  reflexivity.
 apply N.le_max_l.
induction tr0.
 reflexivity.
etransitivity;[exact IHtr0|apply N.le_max_r].
Qed.

Definition programMaximumMemoryResidence (p : Program) x : option N :=
  option_map (fun tr => maximumMemoryResidence (projT2 tr)) (p x).

Lemma pMMR_moveFrame x :
 programMaximumMemoryResidence moveFrame x =
 option_map (fun _ => stateSize x) (runMachine moveFrame x).
Proof.
unfold moveFrame, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.MoveFrame.chk x) as [|[s1 [ctx]]];[reflexivity|cbn].
f_equal.
apply N.max_l.
unfold stateSize, stateShape, stateShapeSize.
cbn.
rewrite fullWriteFrame_size.
apply N.eq_le_incl.
ring.
Qed.

Lemma pMMR_copy n x :
 programMaximumMemoryResidence (copy n) x =
 option_map (fun _ => stateSize x) (runMachine (copy n) x).
Proof.
assert (Hx := stateShape_copy n x).
unfold copy, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.Copy.chk n x) as [|[s1 [l ctx Hl]]];[reflexivity|cbn in *].
unfold stateSize.
rewrite (Hx _ (refl_equal _)), N.max_id.
reflexivity.
Qed.

Lemma pMMR_write b x :
 programMaximumMemoryResidence (write b) x =
 option_map (fun _ => stateSize x) (runMachine (write b) x).
Proof.
assert (Hx := stateShape_write b x).
unfold write, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.Write.chk b x) as [|[s1 [ctx]]];[reflexivity|cbn in *].
unfold stateSize.
rewrite (Hx _ (refl_equal _)), N.max_id.
reflexivity.
Qed.

Lemma pMMR_skip n x :
 programMaximumMemoryResidence (skip n) x =
 option_map (fun _ => stateSize x) (runMachine (skip n) x).
Proof.
assert (Hx := stateShape_skip n x).
unfold skip, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.Skip.chk n x) as [|[s1 [ctx]]];[reflexivity|cbn in *].
unfold stateSize.
rewrite (Hx _ (refl_equal _)), N.max_id.
reflexivity.
Qed.

Lemma pMMR_fwd n x :
 programMaximumMemoryResidence (fwd n) x =
 option_map (fun _ => stateSize x) (runMachine (fwd n) x).
Proof.
assert (Hx := stateShape_fwd n x).
unfold fwd, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.Fwd.chk n x) as [|[s1 [l ctx Hl]]];[reflexivity|cbn in *].
unfold stateSize.
rewrite (Hx _ (refl_equal _)), N.max_id.
reflexivity.
Qed.

Lemma pMMR_bwd n x :
 programMaximumMemoryResidence (bwd n) x =
 option_map (fun _ => stateSize x) (runMachine (bwd n) x).
Proof.
assert (Hx := stateShape_bwd n x).
unfold bwd, programMaximumMemoryResidence, runMachine in *.
destruct (MachineCode.Bwd.chk n x) as [|[s1 [l ctx Hl]]];[reflexivity|cbn in *].
unfold stateSize.
rewrite (Hx _ (refl_equal _)), N.max_id.
reflexivity.
Qed.

Lemma pMMR_seq (p q : Program) x :
 programMaximumMemoryResidence (p ;;; q) x =
 option_map2 N.max (option_bind (programMaximumMemoryResidence q) (runMachine p x))
                   (programMaximumMemoryResidence p x).
Proof.
unfold seq, programMaximumMemoryResidence, runMachine.
destruct (p x) as [[y tr0]|];[cbn|reflexivity].
destruct (q y) as [[z tr1]|];[cbn|reflexivity].
rewrite MMR_app, N.max_comm; reflexivity.
Qed.

Lemma pMMR_choice (p1 p2 : Program) (s : State) :
 programMaximumMemoryResidence (p1 ||| p2) s = match nextData (activeReadFrame s) with
 | Some b :: _ => programMaximumMemoryResidence (if b then p2 else p1) s
 | _ => None
 end.
Proof.
destruct s as [irf [rp [|[|] tl]] awf iwf]; reflexivity.
Qed.
