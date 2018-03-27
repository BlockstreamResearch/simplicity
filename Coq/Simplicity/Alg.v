Require Import Simplicity.Ty.
Require Simplicity.Core.
Require Simplicity.Assertion.
Require Import Util.Monad.
Require Import Util.Option.
Let Hash256 := Simplicity.Assertion.Hash256.

Set Implicit Arguments.
Local Open Scope ty_scope.
Local Open Scope monad_scope.

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

Record ReynoldsClass {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A, rel (Class.iden alg1) (@Class.iden _ alg2 A)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.comp alg1 s1 t1) (@Class.comp _ alg2 A B C s2 t2)
 ; _ : forall A, rel (Class.unit alg1) (@Class.unit _ alg2 A)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.injl alg1 t1) (@Class.injl _ alg2 A B C t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.injr alg1 t1) (@Class.injr _ alg2 A B C t2)
 ; _ : forall A B C D s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.case alg1 s1 t1) (@Class.case _ alg2 A B C D s2 t2)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (Class.pair alg1 s1 t1) (@Class.pair _ alg2 A B C s2 t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.take alg1 t1) (@Class.take _ alg2 A B C t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (Class.drop alg1 t1) (@Class.drop _ alg2 A B C t2)
 }.

Record ReynoldsRel (alg1 alg2 : Algebra) :=
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; reynoldsClass_of :> ReynoldsClass (@rel)
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
intros alg1 alg2 [R []].
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
refine (Hx _ _ (@Build_ReynoldsRel Term alg (fun a b x y => y = eval x) _)); constructor;
intros; simpl; congruence.
Qed.

End Term.

End Core.
Coercion Core.domain : Core.Algebra >-> Funclass.
Coercion Core.rel : Core.ReynoldsRel >-> Funclass.

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
destruct R as [R []].
simpl; auto.
Qed.

Lemma comp_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R B C t1 t2 -> R A C (comp s1 t1) (comp s2 t2).
Proof.
unfold comp.
destruct R as [R []].
simpl; auto.
Qed.

Lemma unit_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A} : R A Unit unit unit.
Proof.
unfold unit.
destruct R as [R []].
simpl; auto.
Qed.

Lemma injl_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A B t1 t2 -> R A (B + C) (injl t1) (injl t2).
Proof.
unfold injl.
destruct R as [R []].
simpl; auto.
Qed.

Lemma injr_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R A (B + C) (injr t1) (injr t2).
Proof.
unfold injr.
destruct R as [R []].
simpl; auto.
Qed.

Lemma case_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C D} s1 s2 t1 t2 : R (A * C) D s1 s2 -> R (B * C) D t1 t2 -> R ((A + B) * C) D (case s1 t1) (case s2 t2).
Proof.
unfold case.
destruct R as [R []].
simpl; auto.
Qed.

Lemma pair_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R A C t1 t2 -> R A (B * C) (pair s1 t1) (pair s2 t2).
Proof.
unfold pair.
destruct R as [R []].
simpl; auto.
Qed.

Lemma take_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R (A * B) C (take t1) (take t2).
Proof.
unfold take.
destruct R as [R []].
simpl; auto.
Qed.

Lemma drop_Parametric {alg1 alg2 : Core.Algebra} (R : Core.ReynoldsRel alg1 alg2)
  {A B C} t1 t2 : R B C t1 t2 -> R (A * B) C (drop t1) (drop t2).
Proof.
unfold drop.
destruct R as [R []].
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

Definition CoreFunSem : Core.Algebra := Core.Pack (Core.Class.Class (fun A B => A -> B)
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

Lemma CoreFunSem_correct {A B} (x : Simplicity.Core.Term A B) : Simplicity.Core.eval x = Core.eval x (alg := CoreFunSem).
Proof.
induction x; simpl; try first [rewrite IHx | rewrite IHx1, IHx2]; reflexivity.
Qed.

Definition CoreSem (M : CIMonad) : Core.Algebra := Core.Pack (Core.Class.Class (Kleisli M)
  (fun A a => eta a)
  (fun A B C s t a => (t <-< s) a)
  (fun A _ => eta tt)
  (fun A B C t a => map inl (t a))
  (fun A B C t a => map inr (t a))
  (fun A B C D s t p => let (ab, c) := p in
    match ab with
    | inl a => s (a, c)
    | inr b => t (b, c)
    end)
  (fun A B C s t a => phi (s a) (t a))
  (fun A B C t ab => t (fst ab))
  (fun A B C t ab => t (snd ab))
).

End CoreSem.

Notation "|[ x ]|^ M" := (x : Core.domain (CoreSem M) _ _) (at level 0, M at level 0) : core_alg_scope.
Notation "|[ x ]|" := (x : Core.domain CoreFunSem _ _) : core_alg_scope.

Local Open Scope core_alg_scope.
Local Open Scope monad_scope.

Lemma CoreSem_initial {M A B} {x : forall {alg : Core.Algebra}, alg A B} (Hx : Core.Parametric (@x)) (a : A) :
  |[ x ]|^M a = eta (|[ x ]| a).
Proof.
rewrite (Core.term_eval Hx (CoreSem M)).
rewrite (Core.term_eval Hx CoreFunSem).
clear Hx.
generalize (x Core.Term); clear x; intros t.
induction t; cbn.
- reflexivity.
- rewrite kleisli_comp_def, IHt1, <- kleisli_comp_def.
  rewrite kleisli_compr; apply IHt2.
- reflexivity.
- rewrite IHt; apply eta_natural.
- rewrite IHt; apply eta_natural.
- destruct a as [[a|b] c]; [apply IHt1|apply IHt2].
- rewrite IHt1, IHt2.
  apply phi_eta.
- apply IHt.
- apply IHt.
Qed.

Module Assertion.

Module Class.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ assertl : forall {A B C D}, term (A * C) D -> Hash256 -> term ((A + B) * C) D
; assertr : forall {A B C D}, Hash256 -> term (B * C) D -> term ((A + B) * C) D
; fail : forall {A B}, (Hash256 * Hash256) -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base : Core.Class.class term
; ext  : mixin term
}.

End Class.
Coercion Class.base : Class.class >-> Core.Class.class.
Coercion Class.ext : Class.class >-> Class.mixin.

Structure Algebra := Pack { domain :> Ty -> Ty -> Type; class_of :> Class.class domain }.

Canonical Structure to_Core (alg : Algebra) : Core.Algebra := Core.Pack (class_of alg).

Record ReynoldsMixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B C D s1 s2 th, rel s1 s2 -> rel (Class.assertl alg1 s1 th) (@Class.assertl _ alg2 A B C D s2 th)
 ; _ : forall A B C D sh t1 t2, rel t1 t2 -> rel (Class.assertr alg1 sh t1) (@Class.assertr _ alg2 A B C D sh t2)
 ; _ : forall A B hh, rel (Class.fail alg1 hh) (@Class.fail _ alg2 A B hh)
 }.

Record ReynoldsClass {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { reynoldsBase :> Core.ReynoldsClass (@rel)
 ; reynoldsExt :> ReynoldsMixin (@rel)
 }.

Record ReynoldsRel (alg1 alg2 : Algebra) :=
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; reynoldsClass_of :> ReynoldsClass (@rel)
 }.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : ReynoldsRel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.

Section Term.

Fixpoint eval {A B} (x : Simplicity.Assertion.Term A B) {alg : Algebra} : alg A B :=
match x in Simplicity.Assertion.Term A B return alg A B with
| Simplicity.Assertion.iden => iden
| Simplicity.Assertion.comp s t => comp (eval s) (eval t)
| Simplicity.Assertion.unit => unit
| Simplicity.Assertion.injl t => injl (eval t)
| Simplicity.Assertion.injr t => injr (eval t)
| Simplicity.Assertion.case s t => case (eval s) (eval t)
| Simplicity.Assertion.pair s t => pair (eval s) (eval t)
| Simplicity.Assertion.take t => take (eval t)
| Simplicity.Assertion.drop t => drop (eval t)
| Simplicity.Assertion.assertl s t => Class.assertl alg (eval s) t
| Simplicity.Assertion.assertr s t => Class.assertr alg s (eval t)
| Simplicity.Assertion.fail hh => Class.fail alg hh
end.

Lemma eval_Parametric {A B} (x : Simplicity.Assertion.Term A B) : Parametric (@eval A B x).
Proof.
intros alg1 alg2 [R [[] []]].
induction x; simpl;
unfold iden, comp, unit, injl, injr, case, pair, take, drop; auto.
Qed.

Canonical Structure Term_Core : Core.Algebra := Core.Pack (Core.Class.Class
   Simplicity.Assertion.Term
   (@Simplicity.Assertion.iden)
   (@Simplicity.Assertion.comp)
   (@Simplicity.Assertion.unit)
   (@Simplicity.Assertion.injl)
   (@Simplicity.Assertion.injr)
   (@Simplicity.Assertion.case)
   (@Simplicity.Assertion.pair)
   (@Simplicity.Assertion.take)
   (@Simplicity.Assertion.drop)).

Canonical Structure Term : Algebra := @Pack Simplicity.Assertion.Term (Class.Class (Core.class_of Term_Core)
  (Class.Mixin
   Simplicity.Assertion.Term
   (@Simplicity.Assertion.assertl)
   (@Simplicity.Assertion.assertr)
   (@Simplicity.Assertion.fail))
  ).

Lemma eval_Term {A B} (x : Simplicity.Assertion.Term A B) : eval x = x.
Proof.
induction x; unfold iden, comp, unit, injl, injr, case, pair, take, drop;
cbn; congruence.
Qed.

Lemma term_eval {A B} (x : forall alg : Algebra, alg A B) (Hx : Parametric x) (alg : Algebra) :
  x alg = eval (x Term).
Proof.
refine (Hx _ _ (@Build_ReynoldsRel Term alg (fun a b x y => y = eval x) _)); repeat constructor;
intros; simpl; unfold iden, comp, unit, injl, injr, case, pair, take, drop;
cbn; congruence.
Qed.

End Term.

End Assertion.
Coercion Assertion.domain : Assertion.Algebra >-> Funclass.
Coercion Assertion.rel : Assertion.ReynoldsRel >-> Funclass.
Coercion Assertion.Class.base : Assertion.Class.class >-> Core.Class.class.
Coercion Assertion.Class.ext : Assertion.Class.class >-> Assertion.Class.mixin.
Canonical Structure Assertion.to_Core.

Section Assertion_Combinators.

Definition assertl {A B C D} {alg : Assertion.Algebra} : alg (A * C) D -> Hash256 -> alg ((A + B) * C) D := Assertion.Class.assertl (Assertion.class_of alg).
Definition assertr {A B C D} {alg : Assertion.Algebra} : Hash256 -> alg (B * C) D -> alg ((A + B) * C) D := Assertion.Class.assertr (Assertion.class_of alg).
Definition fail {A B} {alg : Assertion.Algebra} : (Hash256 * Hash256) -> alg A B := Assertion.Class.fail (Assertion.class_of alg).

Lemma assertl_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.ReynoldsRel alg1 alg2)
  {A B C D} s1 s2 th : R (A * C) D s1 s2 -> R ((A + B) * C) D (assertl s1 th) (assertl s2 th).
Proof.
unfold assertl.
destruct R as [R [Rb []]].
simpl; auto.
Qed.

Lemma assertr_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.ReynoldsRel alg1 alg2)
  {A B C D} sh t1 t2 : R (B * C) D t1 t2 -> R ((A + B) * C) D (assertr sh t1) (assertr sh t2).
Proof.
unfold assertr.
destruct R as [R [Rb []]].
simpl; auto.
Qed.

Lemma fail_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.ReynoldsRel alg1 alg2)
  {A B} hh : R A B (fail hh) (fail hh).
Proof.
unfold assertr.
destruct R as [R [Rb []]].
simpl; firstorder.
Qed.

End Assertion_Combinators.

Hint Resolve assertl_Parametric : parametricity.
Hint Resolve assertr_Parametric : parametricity.
Hint Immediate fail_Parametric : parametricity.

Section AssertionSem.

Definition AssertionSem_Mixin (M : CIMonadZero) := Assertion.Class.Mixin (Kleisli M)
 (fun A B C D s _ p => let (ab, c) := p in
    match ab with
    | inl a => s (a, c)
    | inr b => mzero
    end)
 (fun A B C D _ t p => let (ab, c) := p in
    match ab with
    | inl a => mzero
    | inr b => t (b, c)
    end)
 (fun A B _ => kzero).

Definition AssertionSem (M : CIMonadZero) : Assertion.Algebra :=
  Assertion.Pack (Assertion.Class.Class (Core.class_of (CoreSem M)) (AssertionSem_Mixin M)).

End AssertionSem.

Notation "|[ x ]|^ M" := (x : Assertion.domain (AssertionSem M) _ _) (at level 0, M at level 0) : assertion_alg_scope.

Local Open Scope assertion_alg_scope.

(* TODO, try to replace option_Monad_Zero with just option *)
Lemma AssertionSem_initial {M A B} {x : forall {alg : Assertion.Algebra}, alg A B} (Hx : Assertion.Parametric (@x)) (a : A) :
  |[ x ]|^M a = optionZero (|[ x ]|^option_Monad_Zero a).
Proof.
repeat  rewrite (Assertion.term_eval Hx (AssertionSem _)).
clear Hx.
generalize (x Assertion.Term); clear x; intros t.
induction t; cbn; try reflexivity.
- symmetry; rewrite kleisli_comp_def.
  rewrite optionZero_mu, optionZero_natural, map_comp, <- optionZero_natural, <- IHt1.
  erewrite map_ext;[|intros;symmetry;apply IHt2].
  rewrite <- kleisli_comp_def.
  reflexivity.
- rewrite IHt. apply optionZero_natural.
- rewrite IHt; apply optionZero_natural.
- destruct a as [[a|b] c]; [apply IHt1|apply IHt2].
- rewrite IHt1, IHt2.
  symmetry; apply optionZero_phi.
- apply IHt.
- apply IHt.
- destruct a as [[a|b] c]; [apply IHt|reflexivity].
- destruct a as [[a|b] c]; [reflexivity|apply IHt].
Qed.
