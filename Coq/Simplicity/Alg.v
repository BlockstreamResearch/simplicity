Require Import Simplicity.Ty.
Require Simplicity.Core.

Set Implicit Arguments.
Local Open Scope ty_scope.

Module Core.

Module Class.
Record class (term : Ty -> Ty -> Type) := Class
{ iden : forall {A}, term A A
; comp : forall {A B C}, term A B -> term B C -> term A C
; unit : forall {A}, term A Unit
; injl : forall {A B C}, term A B -> term A (B + C)
; injr : forall {A B C}, term A C -> term A (B + C)
; case : forall {A B C D}, term (A * C) D -> term (B * C) D -> term ((A + B) * C) D
; pair : forall {A B C}, term A B -> term A C -> term A (B * C)
; take : forall {A B C}, term A C -> term (A * B) C
; drop : forall {A B C}, term B C -> term (A * B) C
}.
End Class.

Structure Algebra := Pack { domain :> Ty -> Ty -> Type; class_of :> Class.class domain }.

Record ReynoldsRel (alg1 alg2 : Algebra) :=
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; _ : forall A, rel (Class.iden alg1) (@Class.iden _ alg2 A)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.comp alg1 s1 t1) (@Class.comp _ alg2 A B C s2 t2)
 ; _ : forall A, rel (Class.unit alg1) (@Class.unit _ alg2 A)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.injl alg1 t1) (@Class.injl _ alg2 A B C t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.injr alg1 t1) (@Class.injr _ alg2 A B C t2)
 ; _ : forall A B C D s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.case alg1 s1 t1) (@Class.case _ alg2 A B C D s2 t2)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.pair alg1 s1 t1) (@Class.pair _ alg2 A B C s2 t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.take alg1 t1) (@Class.take _ alg2 A B C t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.drop alg1 t1) (@Class.drop _ alg2 A B C t2)
 }.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : ReynoldsRel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.

Section Term.

Fixpoint eval {A B} (x : Simplicity.Core.Term A B) {alg : Algebra} : alg A B :=
match x in Simplicity.Core.Term A B return alg A B with
| Simplicity.Core.iden => Class.iden alg
| Simplicity.Core.comp s t => Class.comp alg (eval s) (eval t)
| Simplicity.Core.unit => Class.unit alg
| Simplicity.Core.injl t => Class.injl alg (eval t)
| Simplicity.Core.injr t => Class.injr alg (eval t)
| Simplicity.Core.case s t => Class.case alg (eval s) (eval t)
| Simplicity.Core.pair s t => Class.pair alg (eval s) (eval t)
| Simplicity.Core.take t => Class.take alg (eval t)
| Simplicity.Core.drop t => Class.drop alg (eval t)
end.

Lemma eval_Parametric {A B} (x : Simplicity.Core.Term A B) : Parametric (@eval A B x).
Proof.
intros alg1 alg2 [R].
induction x; simpl; auto.
Qed.

Canonical Structure Term : Algebra := Pack (Class.Class
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

Lemma eval_Term {A B} (x : Simplicity.Core.Term A B) : eval x = x.
Proof.
induction x; simpl; congruence.
Qed.

Lemma term_eval {A B} (x : forall alg : Algebra, alg A B) (Hx : Parametric x) (alg : Algebra) :
  x alg = eval (x Term).
Proof.
refine (Hx _ _ (Build_ReynoldsRel Term alg (fun a b x y => y = eval x) _ _ _ _ _ _ _ _ _));
intros; simpl; congruence.
Qed.

End Term.

End Core.

Coercion Core.rel : Core.ReynoldsRel >-> Funclass.
Coercion Core.domain : Core.Algebra >-> Funclass.

Section Core_Combinators.

Definition iden {A} {alg : Core.Algebra} : alg A A := Core.Class.iden (Core.class_of alg).
Definition comp {A B C} {alg : Core.Algebra} : alg A B -> alg B C -> alg A C := Core.Class.comp (Core.class_of alg).
Definition unit {A} {alg : Core.Algebra} : alg A Unit := Core.Class.unit (Core.class_of alg).
Definition injl {A B C} {alg : Core.Algebra} : alg A B -> alg A (B + C) := Core.Class.injl (Core.class_of alg).
Definition injr {A B C} {alg : Core.Algebra} : alg A C -> alg A (B + C) := Core.Class.injr (Core.class_of alg).
Definition case {A B C D} {alg : Core.Algebra} : alg (A * C) D -> alg (B * C) D -> alg ((A + B) * C) D := Core.Class.case (Core.class_of alg).
Definition pair {A B C} {alg : Core.Algebra} : alg A B -> alg A C -> alg A (B * C) := Core.Class.pair (Core.class_of alg).
Definition take {A B C} {alg : Core.Algebra} : alg A C -> alg (A * B) C := Core.Class.take (Core.class_of alg).
Definition drop {A B C} {alg : Core.Algebra} : alg B C -> alg (A * B) C := Core.Class.drop (Core.class_of alg).

Lemma iden_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A} : R A A iden iden.
Proof.
unfold iden.
destruct R as [R].
simpl; auto.
Qed.

Lemma comp_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R B C t1 t2 -> R A C (comp s1 t1) (comp s2 t2).
Proof.
unfold comp.
destruct R as [R].
simpl; auto.
Qed.

Lemma unit_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A} : R A Unit unit unit.
Proof.
unfold unit.
destruct R as [R].
simpl; auto.
Qed.

Lemma injl_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A B t1 t2 -> R A (B + C) (injl t1) (injl t2).
Proof.
unfold injl.
destruct R as [R].
simpl; auto.
Qed.

Lemma injr_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R A (B + C) (injr t1) (injr t2).
Proof.
unfold injr.
destruct R as [R].
simpl; auto.
Qed.

Lemma case_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C D} s1 s2 t1 t2 : R (A * C) D s1 s2 -> R (B * C) D t1 t2 -> R ((A + B) * C) D (case s1 t1) (case s2 t2).
Proof.
unfold case.
destruct R as [R].
simpl; auto.
Qed.

Lemma pair_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R A C t1 t2 -> R A (B * C) (pair s1 t1) (pair s2 t2).
Proof.
unfold pair.
destruct R as [R].
simpl; auto.
Qed.

Lemma take_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R (A * B) C (take t1) (take t2).
Proof.
unfold take.
destruct R as [R].
simpl; auto.
Qed.

Lemma drop_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R B C t1 t2 -> R (A * B) C (drop t1) (drop t2).
Proof.
unfold drop.
destruct R as [R].
simpl; auto.
Qed.

End Core_Combinators.

Create HintDb parametricity.
Hint Immediate iden_Parametric : parametricity.
Hint Resolve comp_Parametric : parametricity.
Hint Immediate unit_Parametric : parametricity.
Hint Resolve injl_Parametric : parametricity.
Hint Resolve injr_Parametric : parametricity.
Hint Resolve case_Parametric : parametricity.
Hint Resolve pair_Parametric : parametricity.
Hint Resolve take_Parametric : parametricity.
Hint Resolve drop_Parametric : parametricity.

Notation "s &&& t" := (pair s t) (at level 70, right associativity) : term_scope.
Notation "s >>> t" := (comp s t) (at level 90, right associativity) : term_scope.

Notation "'H'" := iden : term_scope.
Notation "'O' x" := (take x) (at level 0, right associativity) : term_scope.
Notation "'I' x" := (drop x) (at level 0, right associativity) : term_scope.

Section CoreSem.

Definition CoreSem : Core.Algebra := Core.Pack (Core.Class.Class (fun A B => A -> B)
  (fun A a => a)
  (fun A B C s t a => t (s a))
  (fun A _ => tt)
  (fun A B C t a => inl (t a))
  (fun A B C t a => inr (t a))
  (fun A B C D s t p => let (ab, c) := p in
    match ab with
    | inl a => s (a, c)
    | inr b => t (b, c)
    end)
  (fun A B C s t a => (s a, t a))
  (fun A B C t ab => t (fst ab))
  (fun A B C t ab => t (snd ab))
).

Lemma CoreSem_correct {A B} (x : Simplicity.Core.Term A B) : Simplicity.Core.eval x = Core.eval x (alg := CoreSem).
Proof.
induction x; simpl; try first [rewrite IHx | rewrite IHx1, IHx2]; reflexivity.
Qed.

End CoreSem.

Notation "|[ x ]|" := (x : Core.domain CoreSem _ _) : core_alg_scope.
