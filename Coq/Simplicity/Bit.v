Require Import Simplicity.Ty.
Require Import Simplicity.Alg.

Local Open Scope ty_scope.
Local Open Scope term_scope.

Notation Bit := (Unit + Unit).
Notation "'Bit.zero'" := (inl tt).
Notation "'Bit.one'" := (inr tt).

Section Definitions.

Definition false {A} {term : Core.type} : term A Bit := injl unit.
Definition true {A} {term : Core.type} : term A Bit := injr unit.

Definition cond {A B} {term : Core.type} (thn els : term A B) : term (Bit * A) B :=
  case (drop els) (drop thn).

Definition not {A} {term : Core.type} (t : term A Bit) : term A Bit :=
  t &&& unit >>> cond false true.

End Definitions.

Lemma false_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {A} : R A Bit false false.
Proof.
unfold false.
auto with parametricity.
Qed.
Hint Immediate false_Parametric : parametricity.

Lemma true_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {A} : R A Bit true true.
Proof.
unfold true.
auto with parametricity.
Qed.
Hint Immediate true_Parametric : parametricity.

Lemma cond_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {A B} s1 s2 t1 t2 : R A B s1 s2 -> R A B t1 t2 -> R (Bit * A) B (cond s1 t1) (cond s2 t2).
Proof.
unfold cond.
auto with parametricity.
Qed.
Hint Resolve cond_Parametric : parametricity.

Lemma not_Parametric {term1 term2 : Core.type} (R : Core.ReynoldsRel term1 term2)
  {A} t1 t2 : R A Bit t1 t2 -> R A Bit (not t1) (not t2).
Proof.
unfold not.
auto with parametricity.
Qed.
Hint Resolve not_Parametric : parametricity.
