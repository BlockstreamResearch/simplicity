Require Import PeanoNat.
Require Import List.

Definition option_join {A} (x : option (option A)) : option A :=
match x with
| None => None
| Some x => x
end.

Definition option_bind {A B} (f : A -> option B) (x : option A) : option B :=
option_join (option_map f x).

Lemma option_bind_ext {A B} (f1 f2 : A -> option B) :
  (forall a, f1 a = f2 a) -> forall x, option_bind f1 x = option_bind f2 x.
Proof.
intros H [a|];[apply H|reflexivity].
Qed.

Lemma option_bind_assoc {A B C} (g : B -> option C) (f : A -> option B) x :
  option_bind g (option_bind f x) = option_bind (fun a => option_bind g (f a)) x.
Proof.
destruct x as [a|];reflexivity.
Qed.

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

Record WriteFrame :=
 { writeData : list Cell
 ; writeEmpty : nat
 ; writeSize := length writeData + writeEmpty
 }.

Definition newWriteFrame n : WriteFrame := Build_WriteFrame nil n.
Definition fullWriteFrame l : WriteFrame := Build_WriteFrame (rev l) 0.

Definition writeToFrame v f : option WriteFrame :=
match writeEmpty f with
| O => None
| (S n) => Some (Build_WriteFrame (v :: writeData f) n)
end.

Fixpoint writeListFrame l f : option WriteFrame :=
match l with
| nil => Some f
| hd :: tl => option_bind (writeListFrame tl) (writeToFrame hd f)
end.

Record ReadFrame :=
 { prevData : list Cell
 ; nextData : list Cell
 ; readSize := length prevData + length nextData
 }.

Definition resetFrame wf :=
match writeEmpty wf with
| O => Some (Build_ReadFrame nil (rev (writeData wf)))
| S _ => None
end.

Definition advFrame f :=
match nextData f with
| nil => None
| hd :: tl => Some (Build_ReadFrame (hd :: prevData f) tl)
end.

Definition retFrame f :=
match prevData f with
| nil => None
| hd :: tl => Some (Build_ReadFrame tl (hd :: nextData f))
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
simpl.
unfold option_bind, advFrame; simpl.
intros pd nd.
rewrite IHl, <- app_assoc.
reflexivity.
Qed.

Lemma bwdFrame_correct l : forall pd nd,
   bwdFrame (length l) {| prevData := l ++ pd; nextData := nd |}
 = Some {| prevData := pd; nextData := rev l ++ nd |}.
Proof.
induction l;[reflexivity|].
simpl.
unfold option_bind, retFrame; simpl.
intros pd nd.
rewrite IHl, <- app_assoc.
reflexivity.
Qed.

Lemma sliceFrame_correct l pd nd :
  sliceFrame (length l) {| prevData := pd; nextData := l ++ nd |} = Some l.
Proof.
unfold sliceFrame; simpl.
rewrite app_length.
case (Nat.leb_spec0 _ _).
 intros _.
 rewrite (plus_n_O (length l)), firstn_app_2, firstn_O, app_nil_r.
 reflexivity.
intros [].
auto with *.
Qed.

Definition readFromFrame f := hd None (nextData f).

Record ActiveFrames :=
 { readFrame : ReadFrame
 ; writeFrame : WriteFrame
 ; activeSize := readSize readFrame + writeSize writeFrame
 }.

Definition oModReadFrame f act : option ActiveFrames :=
  option_map (fun x => Build_ActiveFrames x (writeFrame act)) 
       (f (readFrame act)).

Definition oModWriteFrame f act : option ActiveFrames :=
  option_map (fun x => Build_ActiveFrames (readFrame act) x) 
       (f (writeFrame act)).

Record State :=
 { inactiveReadFrames : list ReadFrame
 ; activeFrames : ActiveFrames
 ; inactiveWriteFrames : list WriteFrame
 ; stateSize := fold_right plus 0 (map readSize inactiveReadFrames) +
                activeSize activeFrames +
                fold_right plus 0 (map writeSize inactiveWriteFrames)
 }.

Definition oModActive f s : option State :=
  option_map (fun x => Build_State (inactiveReadFrames s) x (inactiveWriteFrames s)) 
       (f (activeFrames s)).

Definition Context := State.

Record Hole :=
 { readHole : list Cell
 ; writeHole : WriteFrame
 }.

Definition fillContext (ctx : Context) (h : Hole) : State :=
 {| inactiveReadFrames := inactiveReadFrames ctx
  ; activeFrames :=
    {| readFrame :=
      {| prevData := prevData (readFrame (activeFrames ctx))
       ; nextData := readHole h ++ nextData (readFrame (activeFrames ctx))
       |}
     ; writeFrame :=
      {| writeData := writeData (writeHole h) ++ writeData (writeFrame (activeFrames ctx))
       ; writeEmpty := writeEmpty (writeHole h) + writeEmpty (writeFrame (activeFrames ctx))
       |}
     |}
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition appendHole (h1 h2 : Hole) : Hole :=
 {| readHole := readHole h2 ++ readHole h1
  ; writeHole :=
    {| writeData := writeData (writeHole h2) ++ writeData (writeHole h1)
     ; writeEmpty := writeEmpty (writeHole h2) + writeEmpty (writeHole h1)
     |}
  |}.

Lemma context_action ctx h1 h2 :
  fillContext (fillContext ctx h1) h2 = fillContext ctx (appendHole h1 h2).
Proof.
unfold fillContext.
simpl.
repeat rewrite app_assoc.
rewrite Plus.plus_assoc.
reflexivity.
Qed.

Module State.

Definition write b :=
  oModActive (oModWriteFrame (writeToFrame (Some b))).

Definition copy n :=
  oModActive (fun act => option_bind (fun l => oModWriteFrame (writeListFrame l) act) (sliceFrame n (readFrame act))).

Definition skip n :=
  oModActive (oModWriteFrame (writeListFrame (repeat None n))).

Definition fwd n :=
  oModActive (oModReadFrame (fwdFrame n)).

Definition bwd n :=
  oModActive (oModReadFrame (bwdFrame n)).

Definition newFrame n s := Some (Build_State
   (inactiveReadFrames s)
   (Build_ActiveFrames (readFrame (activeFrames s)) (newWriteFrame n))
   (writeFrame (activeFrames s) :: inactiveWriteFrames s)).

Definition moveFrame s :=
match inactiveWriteFrames s with
| nil => None
| hd :: tl => option_map (fun x => Build_State
  (readFrame (activeFrames s) :: inactiveReadFrames s)
  (Build_ActiveFrames x hd)
  tl) (resetFrame (writeFrame (activeFrames s)))
end.

Definition dropFrame s :=
match inactiveReadFrames s with
| nil => None
| hd :: tl => Some (Build_State
  tl
  (Build_ActiveFrames hd (writeFrame (activeFrames s)))
  (inactiveWriteFrames s))
end.

Lemma skip_correct n m l0 l1 (ctx : Context) :
  skip n (fillContext ctx {| readHole := l0; writeHole := {| writeData := l1; writeEmpty := n + m |} |})
= Some (fillContext ctx {| readHole := l0; writeHole := {| writeData := repeat None n ++ l1; writeEmpty := m |} |}).
Proof.
unfold skip.
unfold oModActive.
unfold oModWriteFrame.
unfold fillContext.
simpl.
revert l1.
induction n;[reflexivity|].
intros l1.
simpl.
unfold writeToFrame.
simpl.
set (wd := writeData (writeFrame (activeFrames ctx))).
change (None :: (repeat None n ++ l1) ++ wd) with ((repeat None (S n) ++ l1) ++ wd).
replace (repeat None (S n)) with (repeat (@None bool) n ++ (None :: nil)).
 rewrite <- (app_assoc _ _ l1).
 apply (IHn (None :: l1)).
clear - n.
induction n.
 reflexivity.
simpl.
f_equal.
assumption.
Qed.

Lemma copy_correct (l : list Cell) (ctx : Context) :
  copy (length l) (fillContext ctx {| readHole := l; writeHole := newWriteFrame (length l) |})
= Some (fillContext ctx {| readHole := l; writeHole := fullWriteFrame l |}).
Proof.
destruct ctx.
unfold copy.
unfold fillContext.
unfold oModActive.
simpl.
rewrite sliceFrame_correct.
unfold option_bind; simpl.
set (rf := (Build_ReadFrame _ _)).
generalize rf; clear rf; intros rf. (* TODO there is probably a tactic for this *)
unfold oModWriteFrame; simpl.
destruct activeFrames0. clear activeSize0 stateSize0.
destruct writeFrame0 as [wd we _].
simpl in *.
revert wd;induction l;[reflexivity|];intros wd.
simpl.
unfold writeToFrame; simpl.
unfold option_bind; simpl.
rewrite IHl.
rewrite <- app_assoc.
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
  (readFromFrame (readFrame (activeFrames s)))
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
  ; activeFrames :=
         {| readFrame :=
            {| prevData := rev l ++ prevData (readFrame (activeFrames ctx))
             ; nextData := nextData (readFrame (activeFrames ctx))
             |}
          ; writeFrame := writeFrame (activeFrames ctx)
          |}
  ; inactiveWriteFrames := inactiveWriteFrames ctx
  |}.

Definition bumpHole l : Hole := {| readHole := l; writeHole := newWriteFrame 0 |}.

Lemma runMachine_bump ctx l h1 h2 p :
    runMachine p (fillContext (bumpContext ctx l) h1) = Some (fillContext (bumpContext ctx l) h2)
 -> runMachine (bump (length l) p) (fillContext ctx (appendHole h1 (bumpHole l)))
    = Some (fillContext ctx (appendHole h2 (bumpHole l))).
Proof.
intros Hp.
unfold bump.
repeat rewrite runMachine_append.
unfold fillContext.
simpl (runMachine (fwd _) _).
unfold State.fwd, oModActive, oModReadFrame.
simpl (option_map _ _).
rewrite <- app_assoc, fwdFrame_correct.
unfold option_bind at 2; simpl (option_join _).
change (runMachine p _) with (runMachine p (fillContext (bumpContext ctx l) h1)).
rewrite Hp.
unfold option_bind; simpl.
unfold State.bwd, oModActive, oModReadFrame.
simpl.
rewrite <- rev_length, bwdFrame_correct, rev_involutive, <- app_assoc.
reflexivity.
Qed.