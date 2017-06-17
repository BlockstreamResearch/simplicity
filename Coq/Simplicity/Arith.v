Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.

Local Open Scope ty_scope.
Local Open Scope term_scope.

Fixpoint Word (n : nat) :=
match n with
| O => Bit
| S n => let rec := Word n in Prod rec rec
end.

Section Definitions.

Definition adderBit {term : Core.type} : term (Bit * Bit) (Bit * Bit) :=
  cond (iden &&& not iden) (false &&& iden).

Definition fullAdderBit {term : Core.type} : term ((Bit * Bit) * Bit) (Bit * Bit) :=
  let add := adderBit in
    take add &&& drop iden
>>> take (take iden) &&& (take (drop iden) &&& drop iden >>> add)
>>> cond true (take iden) &&& drop (drop iden).

Definition buildFullAdder {W} {term : Core.type} (rec : term ((W * W) * Bit) (Bit * W)) :
  term (((W * W) * (W * W)) * Bit) (Bit * (W * W)) :=
    take (take (take iden) &&& drop (take iden))
&&& (take (take (drop iden) &&& drop (drop iden)) &&& drop iden >>> rec)
>>> (take iden &&& drop (take iden) >>> rec) &&& drop (drop iden)
>>> take (take iden) &&& (take (drop iden) &&& drop iden).

Fixpoint fullAdder {n : nat} {term : Core.type} : term ((Word n * Word n) * Bit) (Bit * Word n) :=
match n with
| O => fullAdderBit
| S n => buildFullAdder fullAdder
end.

Definition buildAdder {W} {term : Core.type} (fa : term ((W * W) * Bit) (Bit * W)) (rec : term (W * W) (Bit * W)) :
  term ((W * W) * (W * W)) (Bit * (W * W)) :=
    (take (take iden) &&& drop (take iden))
&&& (take (drop iden) &&& drop (drop iden) >>> rec)
>>> (take iden &&& drop (take iden) >>> fa) &&& drop (drop iden)
>>> take (take iden) &&& (take (drop iden) &&& drop iden).

Fixpoint adder {n : nat} {term : Core.type} : term (Word n * Word n) (Bit * Word n) :=
match n with
| O => adderBit
| S n => buildAdder fullAdder adder
end.

Definition fullMultiplierBit {term : Core.type} : term ((Bit * Bit) * (Bit * Bit)) (Bit * Bit) :=
    drop iden &&& take (cond iden false)
>>> fullAdderBit.

Definition buildFullMultiplier {W} {term : Core.type} (rec : term ((W * W) * (W * W)) (W * W)) :
  term (((W * W) * (W * W)) * ((W * W) * (W * W))) (((W * W) * (W * W))) :=
    take ((take (take iden) &&& drop (take iden)) &&& take (drop iden))
&&& ((take (take (take iden) &&& drop (drop iden)) &&& drop (take (take iden) &&& drop (take iden)) >>> rec)
&&& (take (take (drop iden) &&& drop (drop iden)) &&& drop (take (drop iden) &&& drop (drop iden)) >>> rec))
>>> (take (take iden) &&& (take (take (drop iden) &&& drop iden) &&& drop (take (drop iden) &&& drop (take iden)) >>> rec))
&&& (drop (take (take iden) &&& drop (drop iden)))
>>> (take (take iden) &&& (take (drop (take iden)) &&& drop (take iden)) >>> rec) &&& (take (drop (drop iden)) &&& drop (drop iden)).

Fixpoint fullMultiplier {n : nat} {term : Core.type} : term ((Word n * Word n) * (Word n * Word n)) (Word n * Word n) :=
match n with
| O => fullMultiplierBit
| S n => buildFullMultiplier fullMultiplier
end.

Definition multiplierBit {term : Core.type} : term (Bit * Bit) (Bit * Bit) :=
    false &&& cond iden false.

Definition buildMultiplier {W} {term : Core.type} (fm : term ((W * W) * (W * W)) (W * W)) (rec : term (W * W) (W * W)) :
  term ((W * W) * (W * W)) ((W * W) * (W * W)) :=
    ((take (take iden) &&& drop (take iden)) &&& take (drop iden))
&&& ((take (take iden) &&& drop (drop iden) >>> rec)
&&& (take (drop iden) &&& drop (drop iden) >>> rec))
>>> (take (take iden) &&& (take (take (drop iden) &&& drop iden) &&& drop (take (drop iden) &&& drop (take iden)) >>> fm))
&&& (drop (take (take iden) &&& drop (drop iden)))
>>> (take (take iden) &&& (take (drop (take iden)) &&& drop (take iden)) >>> fm) &&& (take (drop (drop iden)) &&& drop (drop iden)).

Fixpoint multiplier {n : nat} {term : Core.type} : term (Word n * Word n) (Word n * Word n) :=
match n with
| O => multiplierBit
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
