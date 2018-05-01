Require Import Util.List.
Require Import Strings.String.
Require Import Util.PackedClass.
Require Import Util.Monad.
Require Import Util.Monad.Reader.
Require Import Util.Option.

Require Import Simplicity.Alg.
Require Import Simplicity.MerkleRoot.
Require Import Simplicity.Ty.

Set Implicit Arguments.
Import ListNotations.

Definition primitivePrefix primName := (MerkleRoot.prefix ++ ["Primitive"%string; primName])%list.

Module Type PrimitiveSig.

Parameter t : Ty -> Ty -> Set.
Parameter tag : forall {A B}, t A B -> hash256.

Parameter env : Set.
Parameter sem : env -> forall {A B}, t A B -> A -> option B.

End PrimitiveSig.

Module Primitive (Prim : PrimitiveSig).

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ prim : forall {A B}, Prim.t A B -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Assertion.class term
; ext  :> mixin term
}.

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (p0 : mixin dom) :=
 [find a  | Assertion.domain a ~ dom | "is not a Assertion algebra" ]
 [find ac | Assertion.class_of a ~ ac ]
 [find p  | p ~ p0 | "is not the right mixin" ]
 @_Pack dom (@Class dom ac p).

Notation Pack dom p := (@packager dom p _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra :=
  Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra :=
  Assertion.Pack alg (class_of alg).

Module Combinators.

Definition prim {A B} {alg : Algebra} : Prim.t A B -> alg A B := prim (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B (p : Prim.t A B), rel (prim p) (prim p)
 }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Assertion.Parametric.class (@rel)
 ; ext :> mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

Module Theory.
Export Combinators.
Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Lemma prim_Parametric {alg1 alg2 : Algebra} (R : Parametric.Rel alg1 alg2)
  {A B} (p : Prim.t A B) : R A B (prim p) (prim p).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.
Hint Immediate prim_Parametric : parametricity.

Definition primSem M A B := Kleisli (ReaderT Prim.env M) A B.

Definition PrimSem_mixin (M : CIMonadZero) : Primitive.mixin (primSem M) :=
  {| Primitive.prim A B p := fun a e => optionZero (Prim.sem e p a)
   |}.

Canonical Structure CorePrimSem (M : CIMonad) : Core.Algebra :=
  Core.Pack (primSem M) (CoreSem_mixin (ReaderT_CIMonad Prim.env M)).
Canonical Structure AssertionPrimSem (M : CIMonadZero) : Assertion.Algebra :=
  Assertion.Pack (primSem M) (AssertionSem_mixin (ReaderT_CIMonadZero Prim.env M)).
Canonical Structure AssertionSem (M : CIMonadZero) : Primitive.Algebra :=
  Primitive.Pack (primSem M) (PrimSem_mixin M).

Definition CommitmentRoot_Primitive_mixin : Primitive.mixin CommitmentRoot :=
 {| Primitive.prim A B p := Prim.tag p
  |}.

Canonical Structure CommitmentRoot_Primitive_alg : Primitive.Algebra :=
  Primitive.Pack CommitmentRoot CommitmentRoot_Primitive_mixin.

End Theory.

End Primitive.