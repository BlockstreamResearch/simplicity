Require Import Simplicity.Ty.
Require Simplicity.Core.

Set Implicit Arguments.

Module Core.

Module Class.
Record class (term : Ty -> Ty -> Type) := Class {
  iden : forall {a:Ty}, term a a;
  comp : forall {a b c:Ty}, term a b -> term b c -> term a c;
  unit : forall {a:Ty}, term a Unit;
  injl : forall {a b c:Ty}, term a b -> term a (Sum b c);
  injr : forall {a b c:Ty}, term a c -> term a (Sum b c);
  case : forall {a b c d:Ty}, term (Prod a c) d -> term (Prod b c) d -> term (Prod (Sum a b) c) d;
  pair : forall {a b c:Ty}, term a b -> term a c -> term a (Prod b c);
  take : forall {a b c:Ty}, term a c -> term (Prod a b) c;
  drop : forall {a b c: Ty}, term b c -> term (Prod a b) c
}.
End Class.

Structure type := Pack { alg :> Ty -> Ty -> Type; class_of :> Class.class alg }.

Definition TermAlg : type := Pack (Class.Class
  Simplicity.Core.Term
  (@Simplicity.Core.iden)
  (@Simplicity.Core.comp)
  (@Simplicity.Core.unit)
  (@Simplicity.Core.injl)
  (@Simplicity.Core.injr)
  (@Simplicity.Core.case)
  (@Simplicity.Core.pair)
  (@Simplicity.Core.take)
  (@Simplicity.Core.drop)
).

End Core.

Coercion Core.alg : Core.type >-> Funclass.

Definition iden {term : Core.type} {a : Ty} : term a a := Core.Class.iden (Core.class_of term).
Definition comp {term : Core.type} {a b c : Ty} : term a b -> term b c -> term a c := Core.Class.comp (Core.class_of term).
Definition unit {term : Core.type} {a : Ty} : term a Unit := Core.Class.unit (Core.class_of term).
Definition injl {term : Core.type} {a b c : Ty} : term a b -> term a (Sum b c) := Core.Class.injl (Core.class_of term).
Definition injr {term : Core.type} {a b c : Ty} : term a c -> term a (Sum b c) := Core.Class.injr (Core.class_of term).
Definition case {term : Core.type} {a b c d : Ty} : term (Prod a c) d -> term (Prod b c) d -> term (Prod (Sum a b) c) d := Core.Class.case (Core.class_of term).
Definition pair {term : Core.type} {a b c : Ty} : term a b -> term a c -> term a (Prod b c) := Core.Class.pair (Core.class_of term).
Definition take {term : Core.type} {a b c : Ty} : term a c -> term (Prod a b) c := Core.Class.take (Core.class_of term).
Definition drop {term : Core.type} {a b c : Ty} : term b c -> term (Prod a b) c := Core.Class.drop (Core.class_of term).

Notation "s &&& t" := (pair s t) (at level 70, right associativity) : term_scope.
Notation "s >>> t" := (comp s t) (at level 90, right associativity) : term_scope.