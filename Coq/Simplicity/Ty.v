Inductive Ty : Set :=
| Unit : Ty
| Sum  : Ty -> Ty -> Ty
| Prod : Ty -> Ty -> Ty.

Fixpoint tySem (X : Ty) : Set :=
match X with
| Unit => Datatypes.unit
| Sum A B => tySem A + tySem B
| Prod A B => tySem A * tySem B
end.
