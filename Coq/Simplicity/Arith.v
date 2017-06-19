Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.

Local Open Scope ty_scope.
Local Open Scope term_scope.

Fixpoint Word (n : nat) :=
match n with
| 0 => Bit
| S n => let rec := Word n in Prod rec rec
end.

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
