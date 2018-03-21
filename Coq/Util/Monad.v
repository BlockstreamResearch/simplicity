Local Open Scope type_scope.

(* Commutative and Idempotnent Monads *)
Module CIMonad.

Module Class.

(* Since monaic values themselve can be functions, we should really be using
 * a setoid here.  However, for this development, let us see how far we can go
 * taking advantage of eta equality
 *)
Record class (M : Type -> Type) := Class
{ eta : forall {A}, A -> M A
; bind : forall {A B}, (A -> M B) -> M A -> M B
; map := (fun A B f => bind (fun a => eta (f a))) : forall {A B}, (A -> B) -> M A -> M B
; kleisliComp := (fun A B C g f a => bind g (f a)) : forall {A B C}, (B -> M C) -> (A -> M B) -> A -> M C
; strength := (fun A B p => map (pair (fst p)) (snd p)) : forall {A B}, A * M B -> M (A * B)
; strength' := (fun A B p => map (fun a => pair a (snd p)) (fst p)) : forall {A B}, M A * B -> M (A * B)
; _ : forall {A B} (f0 f1: A -> M B), (forall a, f0 a = f1 a) -> forall a, bind f0 a = bind f1 a
; _ : forall {A} (x : M A), bind eta x = x
; _ : forall {A B} (f : A -> M B) (a : A), bind f (eta a) = f a
; _ : forall {A B C} (g : B -> M C) (f : A -> M B) (h : A -> M C) (x : M A),
      (forall a, bind g (f a) = h a) -> bind g (bind f x) = bind h x
; _ : forall {A B} (p : M A * M B), kleisliComp strength strength' p = kleisliComp strength' strength p
; _ : forall {A} (x : M A), kleisliComp strength strength' (pair x x) = map (fun a => pair a a) x
}.

End Class.

Structure type := Pack { domain :> Type -> Type; class_of :> Class.class domain }.

Module Theory.

Section Context.

Context {M : type}.

Definition eta {A} (a : A) := Class.eta _ (class_of M) a.
Definition bind {A B} (f : A -> M B) := Class.bind _ (class_of M) f.
Definition map {A B} (f : A -> B) := Class.map _ (class_of M) f.
Definition kleisliComp {A B C} (g : B -> M C) (f : A -> M B) :=
  Class.kleisliComp _ (class_of M) g f.
Definition strength {A B} (p : A * M B) := Class.strength _ (class_of M) p.
Definition strength' {A B} (p : M A * B) := Class.strength' _ (class_of M) p.
Definition mu {A} (x : M (M A)) : M A := bind (fun y => y) x.

Definition Kleisli (F : Type -> Type) A B := A -> F B.

Infix "<-<" := kleisliComp (at level 40, left associativity).

Definition phi {A B} (x : M A) (y : M B) : M (A * B) := (strength <-< strength') (pair x y).

Lemma bind_def {A B} (f : A -> M B) (x : M A) :
  bind f x = mu (map f x).
Proof.
unfold mu, map.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
erewrite bind_assoc;[reflexivity|].
intros a.
apply bind_right.
Qed.

Lemma kleisli_comp_def {A B C} (g : B -> M C) (f : A -> M B) (a : A) :
  (g <-< f) a = mu (map g (f a)).
Proof.
apply bind_def.
Qed.

Lemma kleisli_compl {A B} (f : A -> M B) (a : A) :
  (eta <-< f) a = f a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_left.
Qed.

Lemma kleisli_compr {A B} (f : A -> M B) (a : A) :
  (f <-< eta) a = f a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma kleisli_comp_assoc {A B C D}
  (h : C -> M D) (g : B -> M C) (f : A -> M B) (a : A) :
  ((h <-< g) <-< f) a = (h <-< (g <-< f)) a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
erewrite (bind_assoc _ _ _ h g);reflexivity.
Qed.

Lemma eta_natural {A B} (f : A -> B) (a : A) :
  map f (eta a) = eta (f a).
Proof.
unfold map, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma mu_natural {A B} (f : A -> B) (a : M (M A)) :
  map f (mu a) = mu (map (map f) a).
Proof.
unfold map, mu, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
erewrite bind_assoc;[|reflexivity].
erewrite bind_assoc;[reflexivity|].
intros a0.
apply bind_right.
Qed.

Lemma strength_eta {A B} (a : A) (b : B) : strength (a, eta b) = eta (a, b).
Proof.
unfold strength, eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma strength'_eta {A B} (a : A) (b : B) : strength' (eta a, b) = eta (a, b).
Proof.
unfold strength', eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma phi_eta {A B} (a : A) (b : B) : phi (eta a) (eta b) = eta (a, b).
Proof.
unfold phi.
rewrite kleisli_comp_def, strength'_eta, <- kleisli_comp_def.
rewrite kleisli_compr.
apply strength_eta.
Qed.

End Context.
End Theory.
End CIMonad.
Export CIMonad.Theory.
Notation CIMonad := CIMonad.type.
Coercion CIMonad.domain : CIMonad >-> Funclass.
Infix "<-<" := kleisliComp (at level 40, left associativity) : monad_scope.
