Require Export Coq.Lists.List.

Lemma repeat_S_tail {A} : forall (a : A) n, repeat a n ++ (a :: nil) = repeat a (S n).
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma rev_repeat {A} : forall (a : A) n, rev (repeat a n) = repeat a n.
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn, repeat_S_tail.
reflexivity.
Qed.

