Require Import Util.Monad.
Require Import Util.Option.
Require Import Util.PackedClass.

Require Import Simplicity.Ty.
Require Simplicity.Core.
Variable Hash256 : Set.

Set Implicit Arguments.
Local Open Scope ty_scope.
Local Open Scope monad_scope.

Module Core.

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

Structure Algebra := Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.
Arguments Pack : clear implicits.

Module Combinators.

Definition iden {A} {alg : Algebra} : alg A A := iden (class_of alg).
Definition comp {A B C} {alg : Algebra} : alg A B -> alg B C -> alg A C := comp (class_of alg).
Definition unit {A} {alg : Algebra} : alg A Unit := unit (class_of alg).
Definition injl {A B C} {alg : Algebra} : alg A B -> alg A (B + C) := injl (class_of alg).
Definition injr {A B C} {alg : Algebra} : alg A C -> alg A (B + C) := injr (class_of alg).
Definition case {A B C D} {alg : Algebra} : alg (A * C) D -> alg (B * C) D -> alg ((A + B) * C) D := case (class_of alg).
Definition pair {A B C} {alg : Algebra} : alg A B -> alg A C -> alg A (B * C) := pair (class_of alg).
Definition take {A B C} {alg : Algebra} : alg A C -> alg (A * B) C := take (class_of alg).
Definition drop {A B C} {alg : Algebra} : alg B C -> alg (A * B) C := drop (class_of alg).

Notation "s &&& t" := (pair s t) (at level 70, right associativity) : term_scope.
Notation "s >>> t" := (comp s t) (at level 90, right associativity) : term_scope.

Notation "'H'" := iden : term_scope.
Notation "'O' x" := (take x) (at level 0, right associativity) : term_scope.
Notation "'I' x" := (drop x) (at level 0, right associativity) : term_scope.

End Combinators.

Module Parametric.
Import Combinators.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A, rel iden (@iden A _)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (comp s1 t1) (@comp A B C _ s2 t2)
 ; _ : forall A, rel unit (@unit A _)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (injl t1) (@injl A B C _ t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (injr t1) (@injr A B C _ t2)
 ; _ : forall A B C D s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (case s1 t1) (@case A B C D _ s2 t2)
 ; _ : forall A B C s1 s2 t1 t2, rel s1 s2 -> rel t1 t2 -> rel (pair s1 t1) (@pair A B C _ s2 t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (take t1) (@take A B C _ t2)
 ; _ : forall A B C t1 t2, rel t1 t2 -> rel (drop t1) (@drop A B C _ t2)
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

Section CoreTerm.
Import Combinators.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Fixpoint eval {A B} (x : Simplicity.Core.Term A B) {alg : Algebra} : alg A B :=
match x in Simplicity.Core.Term A B return alg A B with
| Simplicity.Core.iden => iden
| Simplicity.Core.comp s t => comp (eval s) (eval t)
| Simplicity.Core.unit => unit
| Simplicity.Core.injl t => injl (eval t)
| Simplicity.Core.injr t => injr (eval t)
| Simplicity.Core.case s t => case (eval s) (eval t)
| Simplicity.Core.pair s t => pair (eval s) (eval t)
| Simplicity.Core.take t => take (eval t)
| Simplicity.Core.drop t => drop (eval t)
end.

Lemma eval_Parametric {A B} (x : Simplicity.Core.Term A B) : Parametric (@eval A B x).
Proof.
intros alg1 alg2 [R []].
induction x; simpl; auto.
Qed.

Definition Term_mixin : class Simplicity.Core.Term := Class _
  (@Simplicity.Core.iden)
  (@Simplicity.Core.comp)
  (@Simplicity.Core.unit)
  (@Simplicity.Core.injl)
  (@Simplicity.Core.injr)
  (@Simplicity.Core.case)
  (@Simplicity.Core.pair)
  (@Simplicity.Core.take)
  (@Simplicity.Core.drop).

Canonical Structure Term : Algebra := Pack Simplicity.Core.Term Term_mixin.

Lemma eval_Term {A B} (x : Simplicity.Core.Term A B) : eval x = x.
Proof.
induction x; cbn; congruence.
Qed.

Lemma term_eval {A B} (x : forall alg : Algebra, alg A B) (Hx : Parametric x) (alg : Algebra) :
  x alg = eval (x Term).
Proof.
refine (Hx _ _ (@Parametric.Pack Term alg (fun a b x y => y = eval x) _)); constructor;
intros; simpl; congruence.
Qed.

End CoreTerm.

End Core.
Export Core.Combinators.
Coercion Core.domain : Core.Algebra >-> Funclass.
Coercion Core.Parametric.rel : Core.Parametric.Rel >-> Funclass.

Lemma iden_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A} : R A A iden iden.
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma comp_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R B C t1 t2 -> R A C (comp s1 t1) (comp s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma unit_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A} : R A Unit unit unit.
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma injl_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A B t1 t2 -> R A (B + C) (injl t1) (injl t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma injr_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R A (B + C) (injr t1) (injr t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma case_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C D} s1 s2 t1 t2 : R (A * C) D s1 s2 -> R (B * C) D t1 t2 -> R ((A + B) * C) D (case s1 t1) (case s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma pair_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R A C t1 t2 -> R A (B * C) (pair s1 t1) (pair s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma take_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R (A * B) C (take t1) (take t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma drop_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R B C t1 t2 -> R (A * B) C (drop t1) (drop t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

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

Section CoreSem.

Definition FunSem_mixin : Core.class Arrow := Core.Class Arrow
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
  (fun A B C t ab => t (snd ab)).

Definition CoreFunSem : Core.Algebra := Core.Pack Arrow FunSem_mixin.

Lemma CoreFunSem_correct {A B} (x : Simplicity.Core.Term A B) : Simplicity.Core.eval x = Core.eval x (alg:=CoreFunSem).
Proof.
induction x; simpl; try first [rewrite IHx | rewrite IHx1, IHx2]; reflexivity.
Qed.

Definition CoreSem_mixin (M : CIMonad) := Core.Class (Kleisli M)
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
  (fun A B C t ab => t (snd ab)).

Canonical Structure CoreSem (M : CIMonad) : Core.Algebra :=
  Core.Pack (Kleisli M) (CoreSem_mixin M).

End CoreSem.

Notation "|[ x ]|^ M" := (x : Kleisli M _ _) (at level 0, M at level 0) : semantic_scope.
Notation "|[ x ]|" := (x : Core.domain CoreFunSem _ _) : semantic_scope.

Local Open Scope semantic_scope.
Local Open Scope monad_scope.

Lemma CoreSem_initial {M : CIMonad} {A B} {x : forall {alg : Core.Algebra}, alg A B} (Hx : Core.Parametric (@x)) (a : A) :
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

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ assertl : forall {A B C D}, term (A * C) D -> Hash256 -> term ((A + B) * C) D
; assertr : forall {A B C D}, Hash256 -> term (B * C) D -> term ((A + B) * C) D
; fail : forall {A B}, (Hash256 * Hash256) -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Core.class term
; ext  :> mixin term
}.

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (a0 : mixin dom) :=
 [find c  | Core.domain c ~ dom | "is not a Core algebra" ]
 [find cc | Core.class_of c ~ cc ]
 [find a  | a ~ a0 | "is not the right mixin" ]
 @_Pack dom (@Class dom cc a).

Notation Pack dom a := (@packager dom a _ id _ id _ id).  

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).

Module Combinators.

Definition assertl {A B C D} {alg : Algebra} : alg (A * C) D -> Hash256 -> alg ((A + B) * C) D := assertl (class_of alg).
Definition assertr {A B C D} {alg : Algebra} : Hash256 -> alg (B * C) D -> alg ((A + B) * C) D := assertr (class_of alg).
Definition fail {A B} {alg : Algebra} : (Hash256 * Hash256) -> alg A B := fail (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B C D s1 s2 th, rel s1 s2 -> rel (assertl s1 th) (@assertl A B C D _ s2 th)
 ; _ : forall A B C D sh t1 t2, rel t1 t2 -> rel (assertr sh t1) (@assertr A B C D _ sh t2)
 ; _ : forall A B hh, rel (fail hh) (@fail A B _ hh)
 }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Core.Parametric.class (@rel)
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

End Assertion.
Export Assertion.Combinators.
Coercion Assertion.domain : Assertion.Algebra >-> Funclass.
Coercion Assertion.toCore : Assertion.Algebra >-> Core.Algebra.
Coercion Assertion.base : Assertion.class >-> Core.class.
Coercion Assertion.ext : Assertion.class >-> Assertion.mixin.
Coercion Assertion.Parametric.rel : Assertion.Parametric.Rel >-> Funclass.
Canonical Structure Assertion.toCore.

Lemma assertl_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B C D} s1 s2 th : R (A * C) D s1 s2 -> R ((A + B) * C) D (assertl s1 th) (assertl s2 th).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Lemma assertr_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B C D} sh t1 t2 : R (B * C) D t1 t2 -> R ((A + B) * C) D (assertr sh t1) (assertr sh t2).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Lemma fail_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B} hh : R A B (fail hh) (fail hh).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Hint Resolve assertl_Parametric : parametricity.
Hint Resolve assertr_Parametric : parametricity.
Hint Immediate fail_Parametric : parametricity.

Section AssertionSem.

Definition AssertionSem_mixin (M : CIMonadZero) := Assertion.Mixin (Kleisli M)
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

Canonical Structure AssertionSem (M : CIMonadZero) : Assertion.Algebra :=
  Assertion.Pack (Kleisli M) (AssertionSem_mixin M).

End AssertionSem.

Lemma AssertionSem_initial {M : CIMonadZero} {A B} {x : forall {alg : Assertion.Algebra}, alg A B} (Hx : Assertion.Parametric (@x)) :
  forall (a : A), |[ x ]|^M a = optionZero (|[ x ]|^option a).
Proof.
set (R := fun A B (x : AssertionSem M A B) (y : AssertionSem option_Monad_Zero A B) =>
          forall a : A, x a = optionZero (y a)).
refine (Hx _ _ (Assertion.Parametric.Pack (_ : Assertion.Parametric.class R)));
repeat constructor; unfold R; clear; try reflexivity; cbn.
- intros A B C s1 s2 t1 t2 Hs Ht a.
  symmetry; rewrite kleisli_comp_def.
  rewrite optionZero_mu, optionZero_natural, map_comp, <- optionZero_natural, <- Hs.
  erewrite map_ext;[|intros;symmetry;apply Ht].
  rewrite <- kleisli_comp_def.
  reflexivity.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C D s1 s2 t1 t2 Hs Ht [[a|b] c]; [apply Hs|apply Ht].
- intros A B C s1 s2 t1 t2 Hs Ht a.
  rewrite Hs, Ht.
  symmetry; apply optionZero_phi.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C D s1 s2 h Hs [[a|b] c]; [apply Hs|reflexivity].
- intros A B C D h t1 t2 Ht [[a|b] c]; [reflexivity|apply Ht].
Qed.
