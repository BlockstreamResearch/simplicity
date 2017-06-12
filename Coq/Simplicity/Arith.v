Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.

Fixpoint Word (n : nat) :=
match n with
| O => Bit
| (S n) => let rec := Word n in Prod rec rec
end.

Definition adderBit {term : Core.type} : term (Prod Bit Bit) (Prod Bit Bit) :=
  cond (iden &&& not iden) (false &&& iden).