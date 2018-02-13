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

(* The full running state of the Bit Machine is captured by a list of inactive
 * read-only and write-only frames.  The top of the two stacks are held in the
 * activeReadFrame and activeWriteFrame.  This ensures that both stacks are
 * non-empty.
 *)
Record RunState :=
 { inactiveReadFrames : list ReadFrame
 ; activeReadFrame : ReadFrame
 ; activeWriteFrame : WriteFrame
 ; inactiveWriteFrames : list WriteFrame
 }.

(* The state of the Bit Machine can either be a running state or a halted
 * state.
 *)
Inductive State :=
| Halted : State
| Running : RunState -> State.
Coercion Running : RunState >-> State.

Lemma State_dec (x y : State) : {x = y} + {x <> y}.
Proof.
repeat (decide equality).
Qed.

Record RunStateShape :=
 { inactiveReadFrameSizes : list N
 ; activeReadFrameSize : N
 ; activeWriteFrameSize : N
 ; inactiveWriteFrameSizes : list N
 }.

Inductive StateShape :=
| HaltedSS : StateShape
| RunningSS : RunStateShape -> StateShape.
Coercion RunningSS : RunStateShape >-> StateShape.

Definition runStateShape s :=
 {| inactiveReadFrameSizes := map readSize (inactiveReadFrames s)
  ; activeReadFrameSize := readSize (activeReadFrame s)
  ; activeWriteFrameSize := writeSize (activeWriteFrame s)
  ; inactiveWriteFrameSizes := map writeSize (inactiveWriteFrames s)
  |}.

Definition stateShape s :=
match s with
| Running s0 => RunningSS (runStateShape s0)
| Halted => HaltedSS
end.

Definition stateShapeSize s :=
match s with
| RunningSS s0 =>
  N_sum (inactiveReadFrameSizes s0) +
  activeReadFrameSize s0 +
  activeWriteFrameSize s0 +
  N_sum (inactiveWriteFrameSizes s0)
| HaltedSS => 0
end.

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
Definition Context := RunState.

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

Definition fillContext (ctx : Context) (h : LocalState) : RunState :=
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

Definition fillContextShape (ctx : RunStateShape) (h : LocalStateShape) : StateShape :=
 {| inactiveReadFrameSizes := inactiveReadFrameSizes ctx
  ; activeReadFrameSize := activeReadFrameSize ctx + readLocalStateSize h
  ; activeWriteFrameSize := activeWriteFrameSize ctx + writeLocalStateSize h
  ; inactiveWriteFrameSizes := inactiveWriteFrameSizes ctx
  |}.

Lemma fillContextShape_correct ctx h :
  stateShape (fillContext ctx h) = fillContextShape (runStateShape ctx) (localStateShape h).
Proof.
destruct ctx as [irf [prf nrf] awf iwf].
destruct h as [rl wl].
unfold stateShape, runStateShape, fillContextShape; simpl.
repeat f_equal; [unfold readSize|unfold writeSize]; simpl;
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

Definition fillReadFrame (ctx : Context) (h : ReadFrame) : RunState :=
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeReadFrame :=
      {| prevData := prevData h ++ prevData (activeReadFrame ctx)
       ; nextData := nextData h ++ nextData (activeReadFrame ctx)
       |}
  ; activeWriteFrame := activeWriteFrame ctx
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition fillReadFrameShape (ctx : RunStateShape) (h : N) : StateShape :=
 {| inactiveReadFrameSizes := inactiveReadFrameSizes ctx
  ; activeReadFrameSize := activeReadFrameSize ctx + h
  ; activeWriteFrameSize := activeWriteFrameSize ctx
  ; inactiveWriteFrameSizes := inactiveWriteFrameSizes ctx
  |}.

Lemma fillReadFrameShape_correct ctx h :
  stateShape (fillReadFrame ctx h) = fillReadFrameShape (runStateShape ctx) (readSize h).
Proof.
destruct ctx as [irf [prf nrf] awf iwf].
destruct h as [rl wl].
unfold stateShape, runStateShape, fillReadFrameShape; simpl.
repeat f_equal.
unfold readSize; simpl.
repeat rewrite app_length, Nat2N.inj_add; ring.
Qed.

Module MachineCode.

(* Although the types for the following instructions have the form of a
 * Proposition (i.e. they have at most one inhabitant) we put them in the Set
 * universe because we want to compute with the witness values.
 *)
Module NewFrame.

Inductive T n ctx : RunState -> Set :=
op : T n ctx
      {| inactiveReadFrames := inactiveReadFrames ctx
       ; activeReadFrame := activeReadFrame ctx
       ; activeWriteFrame := newWriteFrame n
       ; inactiveWriteFrames := activeWriteFrame ctx :: inactiveWriteFrames ctx
       |}.

(* This isn't really needed, but we add it for completeness *)
Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : RunState & T n s0 s1}.
right.
econstructor.
constructor.
Defined.

End NewFrame.

Module MoveFrame.

Inductive T : RunState -> RunState -> Set :=
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

Definition chk s0 : (forall s1, T s0 s1 -> False)+{s1 : RunState & T s0 s1}.
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

Inductive T : RunState -> RunState -> Set :=
op : forall rf ctx,
    T {| inactiveReadFrames := activeReadFrame ctx :: inactiveReadFrames ctx
       ; activeReadFrame := rf
       ; activeWriteFrame := activeWriteFrame ctx
       ; inactiveWriteFrames := inactiveWriteFrames ctx
       |}
      ctx.

Definition chk s0 : (forall s1, T s0 s1 -> False)+{s1 : RunState & T s0 s1}.
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

Inductive T b : RunState -> RunState -> Set :=
op : forall ctx,
    T b
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame 1
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (Some b :: nil)
                        |}).

Definition chk b s0 : (forall s1, T b s0 s1 -> False)+{s1 : RunState & T b s0 s1}.
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

Inductive T n : RunState -> RunState -> Set :=
op : forall ctx,
    T n
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := newWriteFrame n
                        |})
      (fillContext ctx {| readLocalState := nil
                        ; writeLocalState := fullWriteFrame (repeat None n)
                        |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : RunState & T n s0 s1}.
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

Inductive T n : RunState -> RunState -> Set :=
op : forall l ctx, length l = n ->
    T n
      (fillContext ctx {| readLocalState := l
                        ; writeLocalState := newWriteFrame n
                        |})
      (fillContext ctx {| readLocalState := l
                        ; writeLocalState := fullWriteFrame l
                        |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : RunState & T n s0 s1}.
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

Inductive T n : RunState -> RunState -> Set :=
op : forall l ctx, length l = n ->
    T n
      (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |})
      (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : RunState & T n s0 s1}.
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

Inductive T n : RunState -> RunState -> Set :=
op : forall l ctx, length l = n ->
    T n
      (fillReadFrame ctx {| prevData := rev l
                          ; nextData := nil
                          |})
      (fillReadFrame ctx {| prevData := nil
                          ; nextData := l
                          |}).

Definition chk n s0 : (forall s1, T n s0 s1 -> False)+{s1 : RunState & T n s0 s1}.
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
 * transitions.  Notice that all legal state transitions begin in a RunState
 * and only Abort ends in a Halted state.
 *)
Inductive T : State -> State -> Set :=
| NewFrame : forall s0 s1 n, NewFrame.T n s0 s1 -> T s0 s1
| MoveFrame : forall s0 s1, MoveFrame.T s0 s1 -> T s0 s1
| DropFrame : forall s0 s1, DropFrame.T s0 s1 -> T s0 s1
| Write : forall s0 s1 b, Write.T b s0 s1 -> T s0 s1
| Skip : forall s0 s1 n, Skip.T n s0 s1 -> T s0 s1
| Copy : forall s0 s1 n, Copy.T n s0 s1 -> T s0 s1
| Fwd : forall s0 s1 n, Fwd.T n s0 s1 -> T s0 s1
| Bwd : forall s0 s1 n, Bwd.T n s0 s1 -> T s0 s1
| Abort : forall (s0 : RunState), T s0 Halted.
Arguments NewFrame [s0 s1].
Arguments MoveFrame [s0 s1].
Arguments DropFrame [s0 s1].
Arguments Write [s0 s1].
Arguments Skip [s0 s1].
Arguments Copy [s0 s1].
Arguments Fwd [s0 s1].
Arguments Bwd [s0 s1].
Arguments Abort [s0].

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

(* When starting from the Halted state, the final state must also be
 * Halted, and the only trace possible is the empty trace.
 *)
Lemma runHalt : forall P : forall s, (Halted ->> s) -> Prop,
  P Halted [] -> forall s (tr : Halted ->> s), P s tr.
Proof.
remember Halted as h.
intros P HP s tr.
induction tr.
assumption.
elimtype False.
rewrite Heqh in p.
inversion p.
Qed.

(* A Bit Machine programs takes an inital state, x, and tries to produce a
 * thrist of basic state transformations to some final state, y. However, a
 * program can potentially crash instead if it encounters an instruction that
 * cannot execute successfully from the given state.
 *)
Definition Program := forall x : State, option { y : State & x ->> y }.

(* runProgram lives in Prop so the witness, tr, isn't directly extractable.
 * However, the trace function below can be used to (indirectly) extract this
 * witness value.
 *)
Definition runProgram (p : Program) s0 s1 := exists tr : s0 ->> s1, (p s0) = Some (existT _ _ tr).

Notation "s0 >>- p ->> s1" := (runProgram p s0 s1) (at level 70, p at next level) : type_scope.

Definition trace {p s0 s1} : s0 >>- p ->> s1 -> s0 ->> s1.
unfold runProgram.
intros Htr.
destruct (p s0) as [[s1' Hs1]|].
 replace s1 with s1'.
  exact Hs1.
 abstract (destruct Htr as [tr Htr]; inversion_clear Htr; reflexivity).
abstract (elimtype False; destruct Htr as [tr Htr]; discriminate).
Defined.

Lemma trace_correct {p s0 s1} (tr : s0 >>- p ->> s1) : p s0 = Some (existT _ _ (trace tr)).
Proof.
revert tr.
unfold trace, runProgram.
destruct (p s0) as [[s1' Hs1]|].
 intros tr.
 set (eq:= trace_subproof _ _ _ _ _).
 destruct eq; reflexivity.
intros [tr Htr].
discriminate.
Qed.

(* The nop program has no instructions. *)
Definition nop : Program :=
  fun x => Some (existT _ x []).

Lemma nop_correct s : s >>- nop ->> s.
Proof.
eexists.
reflexivity.
Qed.

Lemma nop_complete s1 s2 : s1 >>- nop ->> s2 -> s1 = s2.
Proof.
intros [tr Htr].
unfold nop, runProgram in Htr.
inversion_clear Htr.
reflexivity.
Qed.

(* For each instruction we define a program that executes only that single
 * instruction.  For each instruction we have a correctness lemma that
 * describes the result of the program when executed with an initial state
 * that is legal for that instruction.
 *)

(* This function is used to build a program from a single instruction.
 * When in the Halted state we ignore the instruction and return the
 * empty trace.
 *)
Definition makeProgram {T : RunState -> RunState -> Set}
                  (inj : forall {s0 s1}, T s0 s1 -> s0 ~~> s1)
                  (dec : forall s0, (forall s1, T s0 s1 -> False)+{s1 : RunState & T s0 s1})
                  : Program :=
fun s0 : State =>
match s0 with
| Halted => Some (existT _ _ [])
| Running s0' =>
 match dec s0' with
 | inl _ => None
 | inr (existT _ s2 t) =>
     Some (existT (fun y : State => s0' ->> y) s2 (inj t <| []))
 end
end.

Lemma op_complete {T : RunState -> RunState -> Set}
                  (inj : forall s0 s1, T s0 s1 -> s0 ~~> s1)
                  (dec : forall s0, (forall s1, T s0 s1 -> False)+{s1 : RunState & T s0 s1})
                  (P : State -> State -> Type)
                  (HT : forall s0 s1, T s0 s1 -> P s0 s1)
                  (HHalted : P Halted Halted)
                  s0 s1 :
  s0 >>- makeProgram inj dec ->> s1 -> P s0 s1.
unfold makeProgram, runProgram.
destruct s0 as [|s0].
 destruct s1 as [|s1].
  intros _; exact HHalted.
 abstract (intros Htr; elimtype False; destruct Htr; discriminate).
destruct (dec s0) as [|[s1' Hs1]].
 abstract (intros Htr; elimtype False; destruct Htr; discriminate).
intros Htr.
replace s1 with (Running s1').
 exact (HT _ _ Hs1).
abstract(
 destruct Htr as [tr Htr];
 inversion Htr;
 auto
).
Defined.

Definition newFrame (n : nat) : Program := makeProgram (fun s0 s1 => @MachineCode.NewFrame s0 s1 n) (MachineCode.NewFrame.chk n).

Lemma newFrame_correct n (s : RunState) : s >>- newFrame n ->> {|
       inactiveReadFrames := inactiveReadFrames s;
       activeReadFrame := activeReadFrame s;
       activeWriteFrame := newWriteFrame n;
       inactiveWriteFrames := activeWriteFrame s :: inactiveWriteFrames s |}.
Proof.
eexists.
reflexivity.
Qed.

Definition newFrame_complete n : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.NewFrame.T n s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- newFrame n ->> s1 -> P s0 s1
:= op_complete _ _.

Definition moveFrame : Program := makeProgram MachineCode.MoveFrame MachineCode.MoveFrame.chk.

Lemma moveFrame_correct : forall l irf arf awf iwf,
  {| inactiveReadFrames := irf
   ; activeReadFrame := arf
   ; activeWriteFrame := fullWriteFrame l
   ; inactiveWriteFrames := awf :: iwf
   |}
  >>- moveFrame ->>
  {| inactiveReadFrames := arf :: irf
   ; activeReadFrame := setFrame l
   ; activeWriteFrame := awf
   ; inactiveWriteFrames := iwf
   |}.
Proof.
eexists.
cbn.
generalize (rev_involutive (rev l)).
rewrite (rev_involutive l).
apply K_dec_set.
 repeat decide equality.
reflexivity.
Qed.

Definition moveFrame_complete : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.MoveFrame.T s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- moveFrame ->> s1 -> P s0 s1
:= op_complete _ _.

Definition dropFrame : Program := makeProgram MachineCode.DropFrame MachineCode.DropFrame.chk.

Lemma dropFrame_correct : forall rf s,
  {| inactiveReadFrames := activeReadFrame s :: inactiveReadFrames s
   ; activeReadFrame := rf
   ; activeWriteFrame := activeWriteFrame s
   ; inactiveWriteFrames := inactiveWriteFrames s
   |} >>- dropFrame ->> s.
Proof.
eexists.
destruct s; reflexivity.
Qed.

Definition dropFrame_complete : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.DropFrame.T s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- dropFrame ->> s1 -> P s0 s1
:= op_complete _ _.

Definition write (b : bool) : Program := makeProgram (fun s0 s1 => @MachineCode.Write s0 s1 b) (MachineCode.Write.chk b).

Lemma write_correct : forall b ctx,
  fillContext ctx {| readLocalState := nil; writeLocalState := newWriteFrame 1 |}
  >>- write b ->>
  fillContext ctx
   {| readLocalState := nil; writeLocalState := fullWriteFrame (Some b :: nil) |}.
Proof.
eexists.
reflexivity.
Qed.

Definition write_complete b : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.Write.T b s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- write b ->> s1 -> P s0 s1
:= op_complete _ _.

Definition skip (n : nat) : Program := makeProgram (fun s0 s1 => @MachineCode.Skip s0 s1 n) (MachineCode.Skip.chk n).

Lemma skip_correct : forall n ctx,
  fillContext ctx {| readLocalState := nil; writeLocalState := newWriteFrame n |}
  >>- skip n ->>
  fillContext ctx
   {| readLocalState := nil; writeLocalState := fullWriteFrame (repeat None n) |}.
Proof.
eexists.
unfold skip, makeProgram.
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
reflexivity.
Qed.

Definition skip_complete n : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.Skip.T n s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- skip n ->> s1 -> P s0 s1
:= op_complete _ _.

Definition copy (n : nat) : Program := makeProgram (fun s0 s1 => @MachineCode.Copy s0 s1 n) (MachineCode.Copy.chk n).

Lemma copy_correct : forall l ctx,
  fillContext ctx {| readLocalState := l; writeLocalState := newWriteFrame (length l) |}
  >>- copy (length l) ->>
  fillContext ctx {| readLocalState := l; writeLocalState := fullWriteFrame l |}.
Proof.
eexists.
unfold copy, makeProgram.
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
reflexivity.
Qed.

Definition copy_complete n : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.Copy.T n s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- copy n ->> s1 -> P s0 s1
:= op_complete _ _.

Definition fwd (n : nat) : Program := makeProgram (fun s0 s1 => @MachineCode.Fwd s0 s1 n) (MachineCode.Fwd.chk n).

Lemma fwd_correct : forall l ctx,
  fillReadFrame ctx {| prevData := nil; nextData := l |}
  >>- fwd (length l) ->>
  fillReadFrame ctx {| prevData := rev l; nextData := nil |}.
Proof.
eexists.
unfold fwd, makeProgram; cbn.
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
reflexivity.
Qed.

Definition fwd_complete n : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.Fwd.T n s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- fwd n ->> s1 -> P s0 s1
:= op_complete _ _.

Definition bwd (n : nat) : Program := makeProgram (fun s0 s1 => @MachineCode.Bwd s0 s1 n) (MachineCode.Bwd.chk n).

Lemma bwd_correct : forall l ctx,
  fillReadFrame ctx {| prevData := rev l; nextData := nil |}
  >>- bwd (length l) ->>
  fillReadFrame ctx {| prevData := nil; nextData := l |}.
Proof.
eexists.
unfold bwd, makeProgram; cbn.
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
reflexivity.
Qed.

Definition bwd_complete n : forall (P : State -> State -> Type),
       (forall s0 s1 : RunState, MachineCode.Bwd.T n s0 s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- bwd n ->> s1 -> P s0 s1
:= op_complete _ _.

(* The basic instruction abort halts the machine. Of course if the machine
 * is already halted, it does nothing, like every other program starting from
 * the halted state.
 *)
Definition abort : Program :=
fun s0 : State => Some
match s0 with
| Halted => existT _ _ []
| Running s0' => existT _ _ (MachineCode.Abort <| [])
end.

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
intros [|x];[exact (Some (existT _ _ []))|].
destruct (nextData (activeReadFrame x)) as [|[b|] tl];[exact None| |exact None].
exact ((if b then p2 else p1) x).
Defined.
Notation "p1 ||| p2" := (choice p1 p2) (at level 50, left associativity) : mc_scope.

Local Open Scope mc_scope.

Lemma seq_correct p q s0 s1 s2 :
 s0 >>- p ->> s1 ->
 s1 >>- q ->> s2 ->
 s0 >>- p ;;; q ->> s2.
Proof.
intros [trp Hp] [trq Hq].
eexists.
unfold seq.
rewrite Hp, Hq.
reflexivity.
Qed.

Lemma seq_complete p q s0 s2 :
 s0 >>- p ;;; q ->> s2 ->
 { s1 | s0 >>- p ->> s1 & s1 >>- q ->> s2}.
unfold seq, runProgram.
destruct (p s0) as [[s1 tr1]|].
- intros Hpq.
  exists s1.
   exists tr1; reflexivity.
  abstract (
   destruct (q s1) as [[s2' tr2]|];
   [destruct Hpq as [tr Htr];
    inversion Htr;
    exists tr2; reflexivity
   |destruct Hpq; discriminate
   ]).
- abstract (intros Hpq; elimtype False; destruct Hpq; discriminate).
Defined.

Lemma choice_left_correct p q s0 s1 :
 head (nextData (activeReadFrame s0)) = Some (Some false) ->
 s0 >>- p ->> s1 ->
 s0 >>- p ||| q ->> s1.
Proof.
unfold choice, runProgram.
destruct (nextData _) as [|[[|]|] tl]; try discriminate.
auto.
Qed.

Lemma choice_right_correct p q s0 s1 :
 head (nextData (activeReadFrame s0)) = Some (Some true) ->
 s0 >>- q ->> s1 ->
 s0 >>- p ||| q ->> s1.
Proof.
unfold choice, runProgram.
destruct (nextData _) as [|[[|]|] tl]; try discriminate.
auto.
Qed.

Lemma choice_complete p q : forall (P : State -> State -> Type),
       (forall (s0 : RunState) s1 b, head (nextData (activeReadFrame s0)) = Some (Some b) ->
                                     s0 >>- (if b then q else p) ->> s1 -> P s0 s1) ->
       P Halted Halted ->
       forall s0 s1 : State,
       s0 >>- p ||| q ->> s1 -> P s0 s1.
intros P H HHalted s0 s1.
unfold choice, runProgram.
destruct s0 as [|s0].
 destruct s1.
  intros _; exact HHalted.
 try abstract (intros Hpq; elimtype False; destruct Hpq; discriminate).
specialize (H s0 s1).
destruct (nextData _) as [|[b|]];
 try abstract (intros Hpq; elimtype False; destruct Hpq; discriminate).
intros Htr.
apply (H b).
 reflexivity.
assumption.
Defined.

Lemma trace_left p q (s0 : RunState) s1 (trp : s0 >>- p ->> s1) (trpq : s0 >>- p ||| q ->> s1) :
 head (nextData (activeReadFrame s0)) = Some (Some false) ->
 trace trp = trace trpq.
Proof.
intros H.
unfold trace, runProgram, choice in *.
destruct (nextData _) as [|b];[discriminate|cbn in *].
revert trpq.
inversion_clear H.
destruct (p s0) as [[s1' Hs1]|];[|intros [ ]; discriminate].
destruct (trace_subproof _ _ _ _ trp).
intros trpq.
generalize (trace_subproof s0 s1' s1' Hs1 trpq).
apply (K_dec_set State_dec).
reflexivity.
Qed.

Lemma trace_right p q (s0 : RunState) s1 (trq : s0 >>- q ->> s1) (trpq : s0 >>- p ||| q ->> s1) :
 head (nextData (activeReadFrame s0)) = Some (Some true) ->
 trace trq = trace trpq.
Proof.
intros H.
unfold trace, runProgram, choice in *.
destruct (nextData _) as [|b];[discriminate|cbn in *].
revert trpq.
inversion_clear H.
destruct (q s0) as [[s1' Hs1]|];[|intros [ ]; discriminate].
destruct (trace_subproof _ _ _ _ trq).
intros trpq.
generalize (trace_subproof s0 s1' s1' Hs1 trpq).
apply (K_dec_set State_dec).
reflexivity.
Qed.

(* bump is notation for a program that is run where the active read frame's
 * cursor is temporarily advanced.
 *)
Definition bump n p : Program := fwd n ;;; p ;;; bwd n.

Lemma bump_correct p l ctx0 ctx1 :
 fillReadFrame ctx0 {| prevData := rev l; nextData := nil |}
 >>- p ->>
 fillReadFrame ctx1 {| prevData := rev l; nextData := nil |} ->
 fillReadFrame ctx0 {| prevData := nil; nextData := l |}
 >>- bump (length l) p ->>
 fillReadFrame ctx1 {| prevData := nil; nextData := l |}.
Proof.
intros Hp.
unfold bump.
repeat eapply seq_correct;[apply fwd_correct|exact Hp|apply bwd_correct].
Qed.

Lemma bump_complete p l ctx0 ctx1 :
 fillReadFrame ctx0 {| prevData := nil; nextData := l |}
 >>- bump (length l) p ->>
 fillReadFrame ctx1 {| prevData := nil; nextData := l |} ->
 fillReadFrame ctx0 {| prevData := rev l; nextData := nil |}
 >>- p ->>
 fillReadFrame ctx1 {| prevData := rev l; nextData := nil |}.
Proof.
unfold bump.
intros Hb.
apply seq_complete in Hb.
destruct Hb as [s2 Hb Hs2].
apply seq_complete in Hb.
destruct Hb as [s1 Hs1 Hb].
replace (_ (fillReadFrame _ _)) with s1.
 replace (_ (fillReadFrame _ _)) with s2.
  assumption.
 clear - Hs2.
 remember (_ (fillReadFrame ctx1 {| prevData := nil; nextData := l |})) as s1.
 destruct Hs2 as [s2 s1 Hs2|] using bwd_complete;[|discriminate].
 injection Heqs1; clear Heqs1; intros ->.
 unfold fillReadFrame.
 destruct s2; destruct ctx1; cbn in *.
 inversion Hs2; cbn in *.
 replace l0 with l in *.
  rewrite (app_inv_head _ _ _ H6).
  reflexivity.
 apply (f_equal (firstn (length l0))) in H6.
 rewrite firstn_app_3 in H6.
 replace (length l0) in H6.
 rewrite firstn_app_3 in H6.
 congruence.
clear - Hs1.
remember (_ (fillReadFrame ctx0 {| prevData := nil; nextData := l |})) as s2.
destruct Hs1 as [s2 s1 Hs1|] using fwd_complete;[|discriminate].
injection Heqs2; clear Heqs2; intros ->.
unfold fillReadFrame.
destruct s1; destruct ctx0; cbn in *.
inversion Hs1; cbn in *.
replace l0 with l in *.
 rewrite (app_inv_head _ _ _ H2).
 reflexivity.
apply (f_equal (firstn (length l0))) in H2.
rewrite firstn_app_3 in H2.
replace (length l0) in H2.
rewrite firstn_app_3 in H2.
congruence.
Qed.

Lemma stateShape_write b x y :
 x >>- write b ->> y ->
 stateShape x = stateShape y.
Proof.
intros Hxy.
destruct Hxy as [x' y' Hxy|] using write_complete;[|reflexivity].
inversion_clear Hxy.
do 2 rewrite fillContextShape_correct.
reflexivity.
Qed.

Lemma stateShape_skip n x y :
 x >>- skip n ->> y ->
 stateShape x = stateShape y.
Proof.
intros Hxy.
destruct Hxy as [x' y' Hxy|] using skip_complete;[|reflexivity].
inversion_clear Hxy.
do 2 rewrite fillContextShape_correct.
f_equal.
unfold localStateShape; cbn.
rewrite fullWriteFrame_size, repeat_length.
reflexivity.
Qed.

Lemma stateShape_copy n x y :
 x >>- copy n ->> y ->
 stateShape x = stateShape y.
Proof.
intros Hxy.
destruct Hxy as [x' y' Hxy|] using copy_complete;[|reflexivity].
inversion_clear Hxy.
do 2 rewrite fillContextShape_correct.
f_equal.
unfold localStateShape; cbn.
rewrite fullWriteFrame_size.
congruence.
Qed.

Lemma stateShape_fwd n x y :
 x >>- fwd n ->> y ->
 stateShape x = stateShape y.
Proof.
intros Hxy.
destruct Hxy as [x' y' Hxy|] using fwd_complete;[|reflexivity].
inversion_clear Hxy.
do 2 rewrite fillReadFrameShape_correct.
f_equal.
unfold readSize; cbn.
rewrite rev_length.
ring.
Qed.

Lemma stateShape_bwd n x y :
 x >>- bwd n ->> y ->
 stateShape x = stateShape y.
Proof.
intros Hxy.
destruct Hxy as [x' y' Hxy|] using bwd_complete;[|reflexivity].
inversion_clear Hxy.
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

Lemma MMR_newFrame n x y (tr : x >>- newFrame n ->> y) :
   maximumMemoryResidence (trace tr) = stateSize y.
Proof.
unfold runProgram in tr.
unfold trace.
unfold newFrame in *.
destruct x as [|x];cbn;destruct (trace_subproof _ _ _ _ tr);[reflexivity|cbn;clear].
apply N.max_r.
destruct x.
unfold stateSize, stateShape, stateShapeSize.
cbn.
rewrite N.add_assoc.
repeat apply N.add_le_mono_r.
rewrite <- N.add_assoc.
repeat apply N.add_le_mono_l.
apply N.le_add_r.
Qed.

Lemma MMR_moveFrame x y (tr : x >>- moveFrame ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
unfold runProgram in tr.
unfold trace.
unfold moveFrame, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.MoveFrame.chk x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);cbn.
apply N.max_l.
unfold stateSize, stateShape, stateShapeSize.
inversion Hy.
cbn.
rewrite fullWriteFrame_size.
apply N.eq_le_incl.
ring.
Qed.

Lemma MMR_dropFrame x y (tr : x >>- dropFrame ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
unfold runProgram in tr.
unfold trace.
unfold dropFrame, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.DropFrame.chk x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);cbn.
apply N.max_l.
unfold stateSize, stateShape, stateShapeSize.
inversion Hy.
cbn.
repeat apply N.add_le_mono_r.
rewrite N.add_comm, <- N.add_assoc.
repeat apply N.add_le_mono_l.
apply N.le_add_r.
Qed.

Lemma MMR_write b x y (tr : x >>- write b ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
assert (Hx := stateShape_write _ _ _ tr).
unfold runProgram in tr.
unfold trace.
unfold write, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.Write.chk b x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);simpl.
unfold stateSize.
rewrite Hx.
apply N.max_id.
Qed.

Lemma MMR_skip n x y (tr : x >>- skip n ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
assert (Hx := stateShape_skip _ _ _ tr).
unfold runProgram in tr.
unfold trace.
unfold skip, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.Skip.chk n x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);simpl.
unfold stateSize.
rewrite Hx.
apply N.max_id.
Qed.

Lemma MMR_copy n x y (tr : x >>- copy n ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
assert (Hx := stateShape_copy _ _ _ tr).
unfold runProgram in tr.
unfold trace.
unfold copy, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.Copy.chk n x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);simpl.
unfold stateSize.
rewrite Hx.
apply N.max_id.
Qed.

Lemma MMR_fwd n x y (tr : x >>- fwd n ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
assert (Hx := stateShape_fwd _ _ _ tr).
unfold runProgram in tr.
unfold trace.
unfold fwd, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.Fwd.chk n x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);simpl.
unfold stateSize.
rewrite Hx.
apply N.max_id.
Qed.

Lemma MMR_bwd n x y (tr : x >>- bwd n ->> y) :
   maximumMemoryResidence (trace tr) = stateSize x.
Proof.
assert (Hx := stateShape_bwd _ _ _ tr).
unfold runProgram in tr.
unfold trace.
unfold bwd, makeProgram in *.
destruct x as [|x];[cbn;destruct (trace_subproof _ _ _ _ tr);reflexivity|].
destruct (MachineCode.Bwd.chk n x) as [|[y' Hy]]in *.
 destruct tr; discriminate.
destruct (trace_subproof x y y' _ tr);simpl.
unfold stateSize.
rewrite Hx.
apply N.max_id.
Qed.

Lemma MMR_seq (p q : Program) x y z (trp : x >>- p ->> y) (trq : y >>- q ->> z) (trpq : x >>- p ;;; q ->> z) :
 maximumMemoryResidence (trace trpq) =
 N.max (maximumMemoryResidence (trace trp)) (maximumMemoryResidence (trace trq)).
Proof.
unfold runProgram in *.
unfold trace.
unfold seq in *.
destruct (p x) as [[y' Hy]|];[|destruct trp; discriminate].
destruct (trace_subproof x y y' Hy trp).
destruct (q y') as [[z' Hz]|];[|destruct trq; discriminate].
destruct (trace_subproof y' z z' Hz trq).
destruct (trace_subproof x z' z' (Hy |><| Hz) trpq).
apply MMR_app.
Qed.
