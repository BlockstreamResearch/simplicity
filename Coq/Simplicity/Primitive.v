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
Definition jetTag := Eval vm_compute in tag (MerkleRoot.prefix ++ ["Jet"%string]) refl_equal.

Module Type PrimitiveSig.

Parameter t : Ty -> Ty -> Set.
Parameter tag : forall {A B}, t A B -> hash256.

Parameter env : Set.
Parameter sem : env -> forall {A B}, t A B -> A -> option B.

End PrimitiveSig.

Module PrimitiveModule (Prim : PrimitiveSig).

Module Primitive.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ prim : forall {A B}, Prim.t A B -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base : Assertion.class term
; ext  : mixin term
}.

Structure Algebra := _Pack { domain : Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (p0 : mixin dom) :=
 [find a  | Assertion.domain a ~ dom | "is not a Assertion algebra" ]
 [find ac | Assertion.class_of a ~ ac ]
 [find p  | p ~ p0 | "is not the right mixin" ]
 @_Pack dom (@Class dom ac p).

Notation Pack dom p := (@packager dom p _ id _ id _ id).

Module Coercions.
Coercion domain : Algebra >-> Funclass.
Coercion base : class >-> Assertion.class.
Coercion ext : class >-> mixin.
End Coercions.

Module CanonicalStructures.
Export Coercions.
Canonical Structure toCore (alg : Algebra) : Core.Algebra :=
  Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra :=
  Assertion.Pack alg (class_of alg).
End CanonicalStructures.

Module Combinators.
Export CanonicalStructures.

Definition prim {A B} {alg : Algebra} : Prim.t A B -> alg A B := prim (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B (p : Prim.t A B), rel (prim p) (prim p)
 }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base : Assertion.Parametric.class (@rel)
 ; ext : mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Import Combinators.
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

Definition PrimSem_mixin (M : CIMonadZero) : mixin (primSem M) :=
  {| Primitive.prim A B p := fun a e => optionZero (Prim.sem e p a)
   |}.

Canonical Structure CorePrimSem (M : CIMonad) : Core.Algebra :=
  Core.Pack (primSem M) (CoreSem_mixin (ReaderT_CIMonad Prim.env M)).
Canonical Structure AssertionPrimSem (M : CIMonadZero) : Assertion.Algebra :=
  Assertion.Pack (primSem M) (AssertionSem_mixin (ReaderT_CIMonadZero Prim.env M)).
Canonical Structure PrimitivePrimSem (M : CIMonadZero) : Algebra :=
  Pack (primSem M) (PrimSem_mixin M).
Canonical Structure WitnessPrimSem (M : CIMonad) : Witness.Algebra :=
  Witness.Pack (primSem M) (WitnessSem_mixin (ReaderT_CIMonad Prim.env M)).
Canonical Structure AssertionWitnessPrimSem (M : CIMonadZero) : AssertionWitness.Algebra :=
  AssertionWitness.Pack (primSem M).

Definition CommitmentRoot_Primitive_mixin : Primitive.mixin CommitmentRoot :=
 {| Primitive.prim A B p := Prim.tag p
  |}.

Canonical Structure CommitmentRoot_Primitive_alg : Algebra :=
  Pack CommitmentRoot CommitmentRoot_Primitive_mixin.

Definition WitnessRoot_Primitive_mixin : Primitive.mixin WitnessRoot :=
 {| Primitive.prim A B p := Prim.tag p
  |}.

Canonical Structure WitnessRoot_Primitive_alg : Algebra :=
  Pack WitnessRoot WitnessRoot_Primitive_mixin.

End Theory.

End Primitive.
Export Primitive.Theory.

Module Jet.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ jet : forall {A B} (t : forall (term : Primitive.Algebra), term A B),
          Primitive.Parametric t -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base : Primitive.class term
; ext  : mixin term
}.

Structure Algebra := _Pack { domain : Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (p0 : mixin dom) :=
 [find a  | Primitive.domain a ~ dom | "is not a Primitive algebra" ]
 [find ac | Primitive.class_of a ~ ac ]
 [find p  | p ~ p0 | "is not the right mixin" ]
 @_Pack dom (@Class dom ac p).

Notation Pack dom p := (@packager dom p _ id _ id _ id).

Module Coercions.
Coercion domain : Algebra >-> Funclass.
Coercion base : class >-> Primitive.class.
Coercion ext : class >-> mixin.
End Coercions.

Module CanonicalStructures.
Export Coercions.
Canonical Structure toCore (alg : Algebra) : Core.Algebra :=
  Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra :=
  Assertion.Pack alg (class_of alg).
Canonical Structure toPrimitive (alg : Algebra) : Primitive.Algebra :=
  Primitive.Pack alg (class_of alg).
End CanonicalStructures.

Module Combinators.
Export CanonicalStructures.

Definition jet {A B} {alg : Algebra} : forall (t : _), Primitive.Parametric t -> alg A B :=
  jet (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B (t : _) (p : Primitive.Parametric t), @rel A B (jet p) (jet p)
 }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base : Assertion.Parametric.class (@rel)
 ; ext : mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Import Combinators.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

Module Theory.
Export Primitive.Theory.
Export Combinators.

Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Lemma jet_Parametric {alg1 alg2 : Algebra} (R : Parametric.Rel alg1 alg2)
  {A B} {t : _} (p : Primitive.Parametric t) : R A B (jet p) (jet p).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.
Hint Resolve jet_Parametric : parametricity.

Definition PrimSem_jet_mixin (M : CIMonadZero) : mixin (primSem M) :=
  {| Jet.jet A B t p := t (PrimitivePrimSem M) |}.

Canonical Structure JetPrimSem (M : CIMonadZero) : Algebra :=
  Pack (primSem M) (PrimSem_jet_mixin M).

Definition CommitmentRoot_Jet_mixin : Jet.mixin CommitmentRoot :=
 {| Jet.jet A B t p := compress_half jetTag (witnessRoot (t _))
  |}.

Canonical Structure CommitmentRoot_Jet_alg : Algebra :=
  Pack CommitmentRoot CommitmentRoot_Jet_mixin.

Definition WitnessRoot_Jet_mixin : Jet.mixin WitnessRoot :=
 {| Jet.jet A B t p := compress_half jetTag (witnessRoot (t _))
  |}.

Canonical Structure WitenssRoot_Jet_alg : Algebra :=
  Pack WitnessRoot WitnessRoot_Jet_mixin.

End Theory.
End Jet.
Export Jet.Theory.

Module FullSimplicity.

Record class (term : Ty -> Ty -> Type) := Class
{ base : Jet.class term
; ext  : Witness.mixin term
}.
Definition base2 term (c : class term) : AssertionWitness.class term :=
  AssertionWitness.Class (base c) (ext c).

Structure Algebra := _Pack { domain : Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom :=
 [find j  | Jet.domain j ~ dom | "is not a Jet algebra" ]
 [find jc | Jet.class_of j ~ jc ]
 [find aw  | AssertionWitness.domain aw ~ dom | "is not a AssertionWitness algebra" ]
 [find awm | AssertionWitness.ext (AssertionWitness.class_of aw) ~ awm ]
 @_Pack dom (@Class dom jc awm).

Notation Pack dom := (@packager dom _ id _ id _ id _ id).

Module Coercions.
Coercion domain : Algebra >-> Funclass.
Coercion base : class >-> Jet.class.
Coercion base2 : class >-> AssertionWitness.class.
End Coercions.

Module CanonicalStructures.
Export Coercions.

Canonical Structure toCore (alg : Algebra) : Core.Algebra :=
  Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra :=
  Assertion.Pack alg (class_of alg).
Canonical Structure toPrimitive (alg : Algebra) : Primitive.Algebra :=
  Primitive.Pack alg (class_of alg).
Canonical Structure toJet (alg : Algebra) : Jet.Algebra :=
  Jet.Pack alg (class_of alg).
Canonical Structure toWitiness (alg : Algebra) : Witness.Algebra :=
  Witness.Pack alg (class_of alg).
Canonical Structure toAssertionWitiness (alg : Algebra) : AssertionWitness.Algebra :=
  AssertionWitness.Pack alg.

End CanonicalStructures.

Module Parametric.
Import CanonicalStructures.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Jet.Parametric.class (@rel)
 ; ext :> Witness.Parametric.mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Import CanonicalStructures.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

Module Theory.
Export Jet.Theory.
Export CanonicalStructures.

Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Canonical Structure SimplicityPrimSem (M : CIMonadZero) : Algebra :=
  Pack (primSem M).

Canonical Structure CommitmentRoot_Simplicity_alg : Algebra :=
  Pack CommitmentRoot.

End Theory.

End FullSimplicity.
Export FullSimplicity.Theory.

End PrimitiveModule.