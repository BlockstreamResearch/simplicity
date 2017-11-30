Definition option_join {A} (x : option (option A)) : option A :=
match x with
| None => None
| Some x => x
end.

Definition option_bind {A B} (f : A -> option B) (x : option A) : option B :=
option_join (option_map f x).

Lemma option_bind_ext {A B} (f1 f2 : A -> option B) :
  (forall a, f1 a = f2 a) -> forall x, option_bind f1 x = option_bind f2 x.
Proof.
intros H [|];[apply H|reflexivity].
Qed.

Lemma option_bind_assoc {A B C} (g : B -> option C) (f : A -> option B) x :
  option_bind g (option_bind f x) = option_bind (fun a => option_bind g (f a)) x.
Proof.
destruct x as [|];reflexivity.
Qed.

Definition option_ap {A B} (f : option (A -> B)) : option A -> option B :=
option_bind (fun a => option_map (fun f => f a) f).

Definition option_map2 {A B C} (f : A -> B -> C) (x : option A) : option B ->  option C :=
option_ap (option_map f x).