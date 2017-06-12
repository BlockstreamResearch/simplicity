Require Import Simplicity.Ty.
Require Import Simplicity.Alg.

Open Scope term_scope.

Definition Bit := Sum Unit Unit.

Definition false {term : Core.type} {a : Ty} : term a Bit := injl unit.
Definition true {term : Core.type} {a : Ty} : term a Bit := injr unit.

Definition cond {term : Core.type} {a b : Ty} (thn els : term a b) : term (Prod Bit a) b :=
  case (drop els) (drop thn).

Definition not {term : Core.type} {a : Ty} (t : term a Bit) : term a Bit :=
  t &&& unit >>> cond false true.