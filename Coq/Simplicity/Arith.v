Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.
Require Import ZArith.

Local Set Keyed Unification.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope core_alg_scope.

Fixpoint Word (n : nat) :=
match n with
| 0 => Bit
| S n => let rec := Word n in Prod rec rec
end.

Module ToZ.

Module Class.
Record class T := Class { toZ : T -> Z; bitSize : nat }.
End Class.
Structure type := Pack { obj : Ty; class_of : Class.class obj }.

Module Ops.
Definition toZ {T : type} : obj T -> Z :=
 let '(Pack _ (Class.Class _ f _)) := T in f.
Definition bitSize (T : type) : nat :=
 let '(Pack _ (Class.Class _ _ n)) := T in n.
Coercion obj : type >-> Ty.
Coercion class_of : type >-> Class.class.
End Ops.

End ToZ.
Import ToZ.Ops.

Definition BitToZ_Class := ToZ.Class.Class (Word 0) (fun bit => match bit with | inl _ => 0%Z | inr _ => 1%Z end) 1.
Canonical Structure BitToZ : ToZ.type := Eval compute in ToZ.Pack Bit BitToZ_Class.

Definition PairToZ_Class {a b : Ty} (a_class : ToZ.Class.class a) (b_class : ToZ.Class.class b) :
  ToZ.Class.class (a * b) :=
ToZ.Class.Class (a * b) (fun p =>
  let (a, b) := p in
  ToZ.Class.toZ _ a_class a * (two_power_nat (ToZ.Class.bitSize _ b_class)) + ToZ.Class.toZ _ b_class b)%Z
  (ToZ.Class.bitSize _ a_class + ToZ.Class.bitSize _ b_class).
Canonical Structure PairToZ (a b : ToZ.type) : ToZ.type := ToZ.Pack (a * b) (PairToZ_Class a b).

Fixpoint WordToZ_Class {n : nat} : ToZ.Class.class (Word n) :=
match n with
| 0 => BitToZ_Class
| (S m) => PairToZ_Class WordToZ_Class WordToZ_Class
end.
Canonical Structure WordToZ (n : nat) : ToZ.type := ToZ.Pack (Word n) WordToZ_Class.

Lemma toZ_Pair {A B : ToZ.type} (a : A) (b : B) :
  @toZ (PairToZ A B) (a, b) = (toZ a * two_power_nat (bitSize B) + toZ b)%Z.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Lemma bitSize_Pair (A B : ToZ.type) :
  bitSize (PairToZ A B) = (bitSize A + bitSize B)%nat.
Proof.
destruct A; destruct B; reflexivity.
Qed.


Section Definitions.

Definition adderBit {term : Core.type} : term (Bit * Bit) (Bit * Bit) :=
  cond (iden &&& not iden) (false &&& iden).

Definition fullAdderBit {term : Core.type} : term ((Bit * Bit) * Bit) (Bit * Bit) :=
  let add := adderBit in
    take add &&& I H
>>> O O H &&& (O I H &&& I H >>> add)
>>> cond true O H &&& I I H.

Definition buildFullAdder {W} {term : Core.type} (rec : term ((W * W) * Bit) (Bit * W)) :
  term (((W * W) * (W * W)) * Bit) (Bit * (W * W)) :=
    take (O O H &&& I O H) &&& (take (O I H &&& I I H) &&& I H >>> rec)
>>> I I H &&& (O H &&& I O H >>> rec)
>>> I O H &&& (I I H &&& O H).

Fixpoint fullAdder {n : nat} {term : Core.type} : term ((Word n * Word n) * Bit) (Bit * Word n) :=
match n with
| 0 => fullAdderBit
| S n => buildFullAdder fullAdder
end.

Definition buildAdder {W} {term : Core.type} (fa : term ((W * W) * Bit) (Bit * W)) (rec : term (W * W) (Bit * W)) :
  term ((W * W) * (W * W)) (Bit * (W * W)) :=
    (O O H &&& I O H)
&&& (O I H &&& I I H >>> rec)
>>> I I H &&& (O H &&& I O H >>> fa)
>>> I O H &&& (I I H &&& O H).

Fixpoint adder {n : nat} {term : Core.type} : term (Word n * Word n) (Bit * Word n) :=
match n with
| 0 => adderBit
| S n => buildAdder fullAdder adder
end.

Definition fullMultiplierBit {term : Core.type} : term ((Bit * Bit) * (Bit * Bit)) (Bit * Bit) :=
    drop iden &&& take (cond iden false)
>>> fullAdderBit.

Definition buildFullMultiplier {W} {term : Core.type} (rec : term ((W * W) * (W * W)) (W * W)) :
  term (((W * W) * (W * W)) * ((W * W) * (W * W))) (((W * W) * (W * W))) :=
    take (O O H &&& (I O H &&& O I H))
&&& ((take (O O H &&& I I H) &&& drop (O O H &&& I O H) >>> rec)
&&& (take (O I H &&& I I H) &&& drop (O I H &&& I I H) >>> rec))
>>> take (O H &&& I O H)
&&& (drop (O O H &&& I I H) &&& (O I H &&& drop (O I H &&& I O H) >>> rec))
>>> (O H &&& drop (I O H &&& O O H) >>> rec) &&& drop (I I H &&& O I H).

Fixpoint fullMultiplier {n : nat} {term : Core.type} : term ((Word n * Word n) * (Word n * Word n)) (Word n * Word n) :=
match n with
| 0 => fullMultiplierBit
| S n => buildFullMultiplier fullMultiplier
end.

Definition multiplierBit {term : Core.type} : term (Bit * Bit) (Bit * Bit) :=
    false &&& cond iden false.

Definition buildMultiplier {W} {term : Core.type} (fm : term ((W * W) * (W * W)) (W * W)) (rec : term (W * W) (W * W)) :
  term ((W * W) * (W * W)) ((W * W) * (W * W)) :=
    (O O H &&& (I O H &&& O I H))
&&& ((O O H &&& I I H >>> rec) &&& (O I H &&& I I H >>> rec))
>>> take (O H &&& I O H)
&&& (drop (O O H &&& I I H) &&& (O I H &&& drop (O I H &&& I O H) >>> fm))
>>> (O H &&& drop (I O H &&& O O H) >>> fm) &&& drop (I I H &&& O I H).

Fixpoint multiplier {n : nat} {term : Core.type} : term (Word n * Word n) (Word n * Word n) :=
match n with
| 0 => multiplierBit
| S n => buildMultiplier fullMultiplier multiplier
end.

End Definitions.

Lemma fullAdder_correct n : forall (a b : Word n) (c : Bit),
  (toZ (|[fullAdder]| ((a, b), c)) = toZ a + toZ b  + toZ c)%Z.
Proof.
induction n.
 intros [[] | []] [[] | []] [[] | []]; reflexivity.
intros [ahi alo] [bhi blo] c.
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo).
set (C := two_power_nat _).
transitivity ((toZ ahi + toZ bhi) * C + (toZ alo + toZ blo + toZ c))%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (alo, blo, c)) as [c0 rlo]; clear alo blo c.
cbn [fst snd].
rewrite (toZ_Pair c0 rlo).
fold C.
transitivity ((toZ ahi + toZ bhi + toZ c0) * C + toZ rlo)%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (ahi, bhi, c0)) as [c1 rhi]; clear ahi bhi c0.
cbn [fst snd].
rewrite (toZ_Pair c1 rhi); fold C.
rewrite (toZ_Pair c1 _).
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
rewrite (toZ_Pair rhi rlo); fold C.
ring.
Qed.

Lemma adder_correct n : forall (a b : Word n),
  (toZ (|[adder]| (a, b)) = toZ a + toZ b)%Z.
induction n.
 intros [[] | []] [[] | []]; reflexivity.
intros [ahi alo] [bhi blo].
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo).
set (C := two_power_nat _).
transitivity ((toZ ahi + toZ bhi) * C + (toZ alo + toZ blo))%Z;[|ring].
rewrite <- (IHn alo).
destruct (|[adder]| (alo, blo)) as [c0 rlo]; clear alo blo.
cbn [fst snd].
rewrite (toZ_Pair c0 rlo).
fold C.
transitivity ((toZ ahi + toZ bhi + toZ c0) * C + toZ rlo)%Z;[|ring].
rewrite <- fullAdder_correct.
destruct (|[fullAdder]| (ahi, bhi, c0)) as [c1 rhi]; clear ahi bhi c0.
cbn [fst snd].
rewrite (toZ_Pair c1 rhi); fold C.
rewrite (toZ_Pair c1 _).
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
rewrite (toZ_Pair rhi rlo); fold C.
ring.
Qed.

Lemma fullMultiplier_correct n : forall (a b c d : Word n),
  (toZ (|[fullMultiplier]| ((a, b), (c, d))) = toZ a * toZ b + toZ c + toZ d)%Z.
Proof.
induction n.
 intros [[] | []] [[] | []] [[] | []] [[] | []]; reflexivity.
intros [ahi alo] [bhi blo] [chi clo] [dhi dlo].
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo), (toZ_Pair chi clo), (toZ_Pair dhi dlo).
set (C := two_power_nat _).
transitivity ((toZ ahi * C + toZ alo) * toZ bhi * C +
 ((toZ ahi * toZ blo + toZ chi + toZ dhi) * C) + (toZ alo * toZ blo + toZ clo + toZ dlo))%Z;
 [|ring].
rewrite <- 2!IHn.
destruct (|[fullMultiplier]| ((alo, blo), (clo, dlo))) as [c0 rOO]; clear clo dlo.
destruct (|[fullMultiplier]| ((ahi, blo), (chi, dhi))) as [c1 c2]; clear chi dhi blo.
cbn [fst snd].
rewrite (toZ_Pair c1 c2), (toZ_Pair c0 rOO); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c1) * C * C +
 (toZ bhi * toZ alo + toZ c2 + toZ c0) * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((bhi, alo), (c2, c0))) as [c3 rOI]; clear c2 c0 alo.
cbn [fst snd].
rewrite (toZ_Pair c3 rOI); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c3 + toZ c1) * C * C + toZ rOI * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((ahi, bhi), (c3, c1))) as [rII rIO]; clear c3 c1 ahi bhi.
rewrite toZ_Pair, (toZ_Pair rOI rOO); fold C.
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
set (X := toZ _); ring.
Qed.

Lemma multiplier_correct n : forall (a b : Word n),
  (toZ (|[multiplier]| (a, b)) = toZ a * toZ b)%Z.
Proof.
induction n.
 intros [[] | []] [[] | []]; reflexivity.
intros [ahi alo] [bhi blo].
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo).
set (C := two_power_nat _).
transitivity ((toZ ahi * C + toZ alo) * toZ bhi * C +
 ((toZ ahi * toZ blo) * C) + (toZ alo * toZ blo))%Z;
 [|ring].
rewrite <- 2!IHn.
destruct (|[multiplier]| (alo, blo)) as [c0 rOO].
destruct (|[multiplier]| (ahi, blo)) as [c1 c2]; clear blo.
cbn [fst snd].
rewrite (toZ_Pair c1 c2), (toZ_Pair c0 rOO); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c1) * C * C +
 (toZ bhi * toZ alo + toZ c2 + toZ c0) * C + toZ rOO)%Z;
 [|ring].
rewrite <- fullMultiplier_correct.
destruct (|[fullMultiplier]| ((bhi, alo), (c2, c0))) as [c3 rOI]; clear c2 c0 alo.
cbn [fst snd].
rewrite (toZ_Pair c3 rOI); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c3 + toZ c1) * C * C + toZ rOI * C + toZ rOO)%Z;
 [|ring].
rewrite <- fullMultiplier_correct.
destruct (|[fullMultiplier]| ((ahi, bhi), (c3, c1))) as [rII rIO]; clear c3 c1 ahi bhi.
rewrite toZ_Pair, (toZ_Pair rOI rOO); fold C.
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
set (X := toZ _); ring.
Qed.

Lemma adderBit_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2) : R _ _ adderBit adderBit.
Proof.
unfold adderBit.
auto with parametricity.
Qed.
Hint Resolve adderBit_Parametric : parametricity.

Lemma fullAdderBit_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2) : R _ _ fullAdderBit fullAdderBit.
Proof.
unfold fullAdderBit.
auto 10 with parametricity.
Qed.
Hint Resolve fullAdderBit_Parametric : parametricity.

Lemma buildFullAdder_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {W} t1 t2 : R _ (Bit * W) t1 t2 -> R _ _ (buildFullAdder t1) (buildFullAdder t2).
Proof.
unfold buildFullAdder.
auto 10 with parametricity.
Qed.
Hint Resolve buildFullAdder_Parametric : parametricity.

Lemma fullAdder_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {n} : R _ _ fullAdder (@fullAdder n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve fullAdder_Parametric : parametricity.

Lemma buildAdder_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {W} s1 s2 t1 t2 : R _ (Bit * W) s1 s2 -> R _ (Bit * W) t1 t2 -> R _ _ (buildAdder s1 t1) (buildAdder s2 t2).
Proof.
unfold buildAdder.
auto 10 with parametricity.
Qed.
Hint Resolve buildAdder_Parametric : parametricity.

Lemma adder_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {n} : R _ _ adder (@adder n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve adder_Parametric : parametricity.

Lemma fullMultiplierBit_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2) : R _ _ fullMultiplierBit fullMultiplierBit.
Proof.
unfold fullMultiplierBit.
auto with parametricity.
Qed.
Hint Resolve fullMultiplierBit_Parametric : parametricity.

Lemma buildFullMultiplier_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {W} t1 t2 : R _ (W * W) t1 t2 -> R _ _ (buildFullMultiplier t1) (buildFullMultiplier t2).
Proof.
unfold buildFullMultiplier.
auto 15 with parametricity.
Qed.
Hint Resolve buildFullMultiplier_Parametric : parametricity.

Lemma fullMultiplier_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {n} : R _ _ fullMultiplier (@fullMultiplier n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve fullMultiplier_Parametric : parametricity.

Lemma multiplierBit_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2) : R _ _ multiplierBit multiplierBit.
Proof.
unfold multiplierBit.
auto with parametricity.
Qed.
Hint Resolve multiplierBit_Parametric : parametricity.

Lemma buildMultiplier_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {W} s1 s2 t1 t2 : R _ (W * W) s1 s2 -> R _ (W * W) t1 t2 -> R _ _ (buildMultiplier s1 t1) (buildMultiplier s2 t2).
Proof.
unfold buildMultiplier.
auto 15 with parametricity.
Qed.
Hint Resolve buildMultiplier_Parametric : parametricity.

Lemma multiplier_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {n} : R _ _ multiplier (@multiplier n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve multiplier_Parametric : parametricity.
