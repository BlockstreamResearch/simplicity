Require Import PeanoNat.
Require Import Util.List.
Require Import Util.Option.

Definition Cell := option bool.

Module MachineCode.

Inductive T : Set :=
| End : T
| Crash : T
| Write : bool -> T -> T
| Copy : nat -> T -> T
| Skip : nat -> T -> T
| Fwd : nat -> T -> T
| Bwd : nat -> T -> T
| NewFrame : nat -> T -> T
| MoveFrame : T -> T
| DropFrame : T -> T
| Read : T -> T -> T.

Fixpoint append (x y : T) : T :=
match x with
| End => y
| Crash => Crash
| Write b k => Write b (append k y)
| Copy n k => Copy n (append k y)
| Skip n k => Skip n (append k y)
| Fwd n k => Fwd n (append k y)
| Bwd n k => Bwd n (append k y)
| NewFrame n k => NewFrame n (append k y)
| MoveFrame k => MoveFrame (append k y)
| DropFrame k => DropFrame (append k y)
| Read k0 k1 => Read (append k0 y) (append k1 y)
end.

End MachineCode.
Bind Scope mc_scope with MachineCode.T.

Definition crash : MachineCode.T := MachineCode.Crash.
Definition write (b : bool) : MachineCode.T := MachineCode.Write b MachineCode.End.
Definition copy (n : nat) : MachineCode.T := MachineCode.Copy n MachineCode.End.
Definition skip (n : nat) : MachineCode.T := MachineCode.Skip n MachineCode.End.
Definition fwd (n : nat) : MachineCode.T := MachineCode.Fwd n MachineCode.End.
Definition bwd (n : nat) : MachineCode.T := MachineCode.Bwd n MachineCode.End.
Definition newFrame (n : nat) : MachineCode.T := MachineCode.NewFrame n MachineCode.End.
Definition moveFrame : MachineCode.T := MachineCode.MoveFrame MachineCode.End.
Definition dropFrame : MachineCode.T := MachineCode.DropFrame MachineCode.End.
Definition read (k0 k1 : MachineCode.T) : MachineCode.T := MachineCode.Read k0 k1.

Notation "p ;; q" := (MachineCode.append p q) (at level 40, left associativity) : mc_scope.

Definition nop : MachineCode.T := MachineCode.End.
Definition bump n p : MachineCode.T := fwd n ;; p ;; bwd n.

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

Definition writeToFrame v f : option WriteFrame :=
match writeEmpty f with
| O => None
| (S n) => Some {| writeData := v :: writeData f; writeEmpty := n |}
end.

Fixpoint writeListFrame l f : option WriteFrame :=
match l with
| nil => Some f
| hd :: tl => option_bind (writeListFrame tl) (writeToFrame hd f)
end.

(* Read-only frames are represented in zipper format.  The cells before the
 * cursor are stored in prevData in reverse order.  The cells after the cursor
 * are stored in nextData in forward order.
 *)
Record ReadFrame :=
 { prevData : list Cell
 ; nextData : list Cell
 }.

Definition readSize rf := length (prevData rf) + length (nextData rf).

Definition setFrame l :=
 {| prevData := nil
  ; nextData := l
  |}.

Definition resetFrame wf :=
match writeEmpty wf with
| O => Some (setFrame (rev (writeData wf)))
| S _ => None
end.

Definition advFrame f :=
match nextData f with
| nil => None
| hd :: tl => Some {| prevData := hd :: prevData f; nextData := tl |}
end.

Definition retFrame f :=
match prevData f with
| nil => None
| hd :: tl => Some {| prevData := tl; nextData := hd :: nextData f |}
end.

Fixpoint fwdFrame n f :=
match n with
| O => Some f
| (S m) => option_bind (fwdFrame m) (advFrame f)
end.

Fixpoint bwdFrame n f :=
match n with
| O => Some f
| (S m) => option_bind (bwdFrame m) (retFrame f)
end.

Definition sliceFrame n f :=
if Nat.leb n (length (nextData f))
then Some (firstn n (nextData f))
else None.

Lemma fwdFrame_correct l : forall pd nd,
   fwdFrame (length l) {| prevData := pd; nextData := l ++ nd |}
 = Some {| prevData := rev l ++ pd; nextData := nd |}.
Proof.
induction l;[reflexivity|].
intros pd nd.
cbn.
rewrite IHl, <- app_assoc.
reflexivity.
Qed.

Lemma bwdFrame_correct l : forall pd nd,
   bwdFrame (length l) {| prevData := l ++ pd; nextData := nd |}
 = Some {| prevData := pd; nextData := rev l ++ nd |}.
Proof.
induction l;[reflexivity|].
intros pd nd.
cbn.
rewrite IHl, <- app_assoc.
reflexivity.
Qed.

Lemma sliceFrame_correct l pd nd :
  sliceFrame (length l) {| prevData := pd; nextData := l ++ nd |} = Some l.
Proof.
unfold sliceFrame; cbn.
rewrite app_length.
case (Nat.leb_spec0 _ _);[intros _|intros []; auto with *].
rewrite (plus_n_O (length l)), firstn_app_2, firstn_O, app_nil_r.
reflexivity.
Qed.

Definition readFromFrame f := hd None (nextData f).

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

Definition stateSize s :=
  fold_right plus 0 (map readSize (inactiveReadFrames s)) +
  readSize (activeReadFrame s) +
  writeSize (activeWriteFrame s) +
  fold_right plus 0 (map writeSize (inactiveWriteFrames s)).

Definition oModActiveReadFrame f s : option State :=
  option_map (fun x =>
    {| inactiveReadFrames := inactiveReadFrames s
     ; activeReadFrame := x
     ; activeWriteFrame := activeWriteFrame s
     ; inactiveWriteFrames := inactiveWriteFrames s
     |}) (f (activeReadFrame s)).

Definition oModActiveWriteFrame f s : option State :=
  option_map (fun x =>
    {| inactiveReadFrames := inactiveReadFrames s
     ; activeReadFrame := activeReadFrame s
     ; activeWriteFrame := x
     ; inactiveWriteFrames := inactiveWriteFrames s
     |}) (f (activeWriteFrame s)).

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

Module State.

Definition write b :=
  oModActiveWriteFrame (writeToFrame (Some b)).

Definition copy n s :=
  oModActiveWriteFrame (fun wf => option_bind (fun l => writeListFrame l wf) (sliceFrame n (activeReadFrame s))) s.

Definition skip n :=
  oModActiveWriteFrame (writeListFrame (repeat None n)).

Definition fwd n :=
  oModActiveReadFrame (fwdFrame n).

Definition bwd n :=
  oModActiveReadFrame (bwdFrame n).

Definition newFrame n s :=
  Some {| inactiveReadFrames := inactiveReadFrames s
        ; activeReadFrame := activeReadFrame s
        ; activeWriteFrame := newWriteFrame n
        ; inactiveWriteFrames := activeWriteFrame s :: inactiveWriteFrames s
        |}.

Definition moveFrame s :=
match inactiveWriteFrames s with
| nil => None
| hd :: tl => option_map (fun x =>
  {| inactiveReadFrames := activeReadFrame s :: inactiveReadFrames s
   ; activeReadFrame := x
   ; activeWriteFrame := hd
   ; inactiveWriteFrames := tl
   |}) (resetFrame (activeWriteFrame s))
end.

Definition dropFrame s :=
match inactiveReadFrames s with
| nil => None
| hd :: tl => Some
  {| inactiveReadFrames := tl
   ; activeReadFrame := hd
   ; activeWriteFrame := activeWriteFrame s
   ; inactiveWriteFrames := inactiveWriteFrames s
   |}
end.

Lemma skip_correct n m l0 l1 (ctx : Context) :
  skip n (fillContext ctx {| readLocalState := l0
                           ; writeLocalState :=
                             {| writeData := l1
                              ; writeEmpty := n + m
                           |} |})
= Some (fillContext ctx {| readLocalState := l0
                         ; writeLocalState :=
                           {| writeData := repeat None n ++ l1
                            ; writeEmpty := m
                         |} |}).
Proof.
unfold skip, fillContext, oModActiveWriteFrame.
cbn.
revert l1.
induction n;[reflexivity|].
intros l1.
cbn.
set (wd := writeData (activeWriteFrame ctx)).
change (None :: (repeat None n ++ l1) ++ wd) with ((repeat None (S n) ++ l1) ++ wd).
rewrite <- repeat_S_tail.
rewrite <- (app_assoc _ _ l1).
apply (IHn (None :: l1)).
Qed.

Lemma copy_correct (l : list Cell) (ctx : Context) :
  copy (length l) (fillContext ctx {| readLocalState := l
                                    ; writeLocalState := newWriteFrame (length l)
                                    |})
= Some (fillContext ctx {| readLocalState := l
                         ; writeLocalState := fullWriteFrame l
                         |}).
Proof.
unfold copy, fillContext, oModActiveWriteFrame; cbn.
rewrite sliceFrame_correct; cbn.
set (rf := (Build_ReadFrame _ _)); clearbody rf.
set (wd := writeData _); clearbody wd; revert wd.
induction l;[reflexivity|];intros wd; cbn.
rewrite IHl, <- app_assoc.
reflexivity.
Qed.

End State.

Fixpoint runMachine (p : MachineCode.T) s : option State :=
match p with
| MachineCode.End => Some s
| MachineCode.Crash => None
| MachineCode.Write b k => option_bind (runMachine k) (State.write b s)
| MachineCode.Copy n k => option_bind (runMachine k) (State.copy n s)
| MachineCode.Skip n k => option_bind (runMachine k) (State.skip n s)
| MachineCode.Fwd n k => option_bind (runMachine k) (State.fwd n s)
| MachineCode.Bwd n k => option_bind (runMachine k) (State.bwd n s)
| MachineCode.NewFrame n k => option_bind (runMachine k) (State.newFrame n s)
| MachineCode.MoveFrame k => option_bind (runMachine k) (State.moveFrame s)
| MachineCode.DropFrame k => option_bind (runMachine k) (State.dropFrame s)
| MachineCode.Read k0 k1 => option_bind
  (fun b : bool => if b then runMachine k1 s else runMachine k0 s)
  (readFromFrame (activeReadFrame s))
end.

Lemma runMachine_append p q s :
  runMachine (p ;; q) s = option_bind (runMachine q) (runMachine p s).
Proof.
revert q s; induction p; intros q s; try reflexivity;
 simpl; rewrite option_bind_assoc; apply option_bind_ext; auto.
intros [|]; auto.
Qed.

Definition bumpContext (ctx : Context) l : Context :=
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeReadFrame :=
    {| prevData := rev l ++ prevData (activeReadFrame ctx)
     ; nextData := nextData (activeReadFrame ctx)
     |}
  ; activeWriteFrame := activeWriteFrame ctx
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition bumpLocalState l : LocalState := {| readLocalState := l; writeLocalState := newWriteFrame 0 |}.

Lemma runMachine_bump ctx l ls1 ls2 p :
    runMachine p (fillContext (bumpContext ctx l) ls1) = Some (fillContext (bumpContext ctx l) ls2)
 -> runMachine (bump (length l) p) (fillContext ctx (appendLocalState ls1 (bumpLocalState l)))
    = Some (fillContext ctx (appendLocalState ls2 (bumpLocalState l))).
Proof.
intros Hp.
unfold bump.
repeat rewrite runMachine_append.
unfold fillContext.
simpl (runMachine (fwd _) _).
unfold State.fwd, oModActiveReadFrame.
simpl (option_map _ _).
rewrite <- app_assoc, fwdFrame_correct.
unfold option_bind at 2; simpl (option_join _).
change (runMachine p _) with (runMachine p (fillContext (bumpContext ctx l) ls1)).
rewrite Hp.
unfold option_bind; cbn.
unfold State.bwd, oModActiveReadFrame; cbn.
rewrite <- rev_length, bwdFrame_correct, rev_involutive, <- app_assoc.
reflexivity.
Qed.
