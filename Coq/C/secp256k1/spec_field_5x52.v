Require Import VST.floyd.proofauto.
Require Import jets_secp256k1.
Require Import extraVST.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition secp256k1_R : Z := 
Eval compute in 2^32 + 2^9 + 2^8 + 2^7 + 2^6 + 2^4 + 1.

Definition secp256k1_P : Z := 
Eval compute in 2^256 - secp256k1_R.

Opaque Z.shiftl Z.shiftr Z.pow.

Module secp256k1_fe_array.

Definition from_array (l : list Z) : Z :=
fold_right (fun x z => x + (Z.shiftl z 52)) 0 l.

Definition to_array (z : Z) : list Z :=
[Z.land z (Z.ones 52)
;Z.land (Z.shiftr z 52) (Z.ones 52)
;Z.land (Z.shiftr z (2*52)) (Z.ones 52)
;Z.land (Z.shiftr z (3*52)) (Z.ones 52)
;Z.shiftr z (4*52)
].

Lemma from_to_array z : from_array (to_array z) = z.
Proof.
cbn.
rewrite !Z.land_ones, !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
symmetry.
rewrite (Z_div_mod_eq_full z (2^52)) at 1.
rewrite (Z_div_mod_eq_full (z / 2^52) (2^52)) at 1.
rewrite Zdiv.Zdiv_Zdiv, <- Z.pow_add_r by lia. simpl (_ + 52).
rewrite (Z_div_mod_eq_full (z / 2^104) (2^52)) at 1.
rewrite Zdiv.Zdiv_Zdiv, <- Z.pow_add_r by lia. simpl (_ + 52).
rewrite (Z_div_mod_eq_full (z / 2^156) (2^52)) at 1.
rewrite Zdiv.Zdiv_Zdiv, <- Z.pow_add_r by lia. simpl (_ + 52).
ring.
Qed.

Definition boundBy (magnitude : Z) (l : list Z) :=
   Forall (fun x => 0 <= x <= 2 * magnitude * (Z.ones 52)) l
/\ nth 4 l 0 <= 2 * magnitude * (Z.ones 48).

Fixpoint add (a b : list Z) : list Z :=
match a with
| nil => b
| cons a0 atl =>
  match b with
  | nil => a
  | cons b0 btl => cons (a0 + b0) (add atl btl)
  end
end.

Lemma add_spec a b : from_array (add a b) = from_array a + from_array b.
Proof.
revert b.
induction a;[reflexivity|].
intros [|b b0];[cbn; ring|].
simpl.
rewrite IHa, !Z.shiftl_mul_pow2 by lia.
ring.
Qed.

Fixpoint mul (a b : list Z) : list Z :=
match a with
| nil => nil
| cons a0 atl => add (map (Z.mul a0) b) (cons 0 (mul atl b))
end.

Lemma scale_spec a b : from_array (map (Z.mul a) b) = a * from_array b.
Proof.
induction b;[cbn; ring|].
simpl.
rewrite IHb, !Z.shiftl_mul_pow2 by lia.
ring.
Qed.

Lemma mul_spec a b : from_array (mul a b) = from_array a * from_array b.
Proof.
revert b.
induction a;[reflexivity|].
intros b.
simpl.
rewrite add_spec.
simpl.
rewrite IHa, scale_spec, !Z.shiftl_mul_pow2 by lia.
ring.
Qed.

End secp256k1_fe_array.

Definition withOption {A B} (def : B) (f : A -> B) (ox : option A) : B :=
match ox with
| None => def
| Some x => f x
end.

Definition secp256k1_fe_mul_inner_spec : ident * funspec :=
DECLARE _secp256k1_fe_mul_inner
  WITH r : option (val * share),
       a : val, sha : share, arra : list Z,
       b : val, shb : share, arrb : list Z
    PRE [ tptr tulong, tptr tulong, tptr tulong ]
    PROP(writable_share (withOption sha snd r);
         readable_share sha;
         readable_share shb;
         nonempty_share (Share.glb sha shb); (* Needed to prevent a and b from aliasing. Note: writable shares always intersect. *)
         length arra = 5%nat;
         length arrb = 5%nat;
         secp256k1_fe_array.boundBy 8 arra;
         secp256k1_fe_array.boundBy 8 arrb)
    PARAMS(withOption a fst r; a; b)
  SEP(withOption emp (fun '(v, sh) => data_at_ sh (tarray tulong 5) v) r;
      data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b)
POST [ tvoid ]
  EX arrr : list Z,
  PROP(length arrr = 5%nat;
       secp256k1_fe_array.boundBy 1 arrr;
       eqm secp256k1_P (secp256k1_fe_array.from_array arra * secp256k1_fe_array.from_array arrb) (secp256k1_fe_array.from_array arrr))
  RETURN()
  SEP(data_at (withOption sha snd r) (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrr) (withOption a fst r);
      withOption emp (fun _ => (data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a)) r;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b).

(* An easier to use specification to secp256k1_fe_mul_inner for when the pointers are statically known to not be aliased. *)
Definition secp256k1_fe_mul_inner_spec_restrict : ident * funspec :=
DECLARE _secp256k1_fe_mul_inner
  WITH r : val, shr : share,
       a : val, sha : share, arra : list Z,
       b : val, shb : share, arrb : list Z
  PRE [ tptr tulong, tptr tulong, tptr tulong ]
    PROP(writable_share shr;
         readable_share sha;
         readable_share shb;
         nonempty_share (Share.glb sha shb); (* Needed to prevent a and b from aliasing. Note: writable shares always intersect. *)
         length arra = 5%nat;
         length arrb = 5%nat;
         secp256k1_fe_array.boundBy 8 arra;
         secp256k1_fe_array.boundBy 8 arrb)
    PARAMS(r; a; b)
  SEP(data_at_ shr (tarray tulong 5) r;
      data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b)
POST [ tvoid ]
  EX arrr : list Z,
  PROP(length arrr = 5%nat;
       secp256k1_fe_array.boundBy 1 arrr;
       eqm secp256k1_P (secp256k1_fe_array.from_array arra * secp256k1_fe_array.from_array arrb) (secp256k1_fe_array.from_array arrr))
  RETURN()
  SEP(data_at shr (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrr) r;
      data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b).

(* Use with
   forward_call secp256k1_fe_mul_inner_spec_restrict_sub (r, shr, arrr, a, sha, arra, b, shb, arrb)
*)
Lemma secp256k1_fe_mul_inner_spec_restrict_sub :
  funspec_sub (snd secp256k1_fe_mul_inner_spec) (snd secp256k1_fe_mul_inner_spec_restrict).
Proof.
do_funspec_sub.
destruct w as [[[[[[[r shr] a] sha] arra] b] shb] arrb].
entailer!.
Exists ((((((Some (r, shr), a), sha), arra), b), shb), arrb) emp.
simpl; entailer!.
intros.
Exists x0.
entailer!.
Qed.

(* An easier to use specification to secp256k1_fe_mul_inner for when the pointers r and a are statically known alias. *)
Definition secp256k1_fe_mul_inner_spec_alias : ident * funspec :=
DECLARE _secp256k1_fe_mul_inner
  WITH a : val, sha : share, arra : list Z,
       b : val, shb : share, arrb : list Z
  PRE [ tptr tulong, tptr tulong, tptr tulong ]
    PROP(writable_share sha;
         readable_share shb;
         length arra = 5%nat;
         length arrb = 5%nat;
         secp256k1_fe_array.boundBy 8 arra;
         secp256k1_fe_array.boundBy 8 arrb)
    PARAMS(a; a; b)
  SEP(data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b)
POST [ tvoid ]
  EX arrr : list Z,
  PROP(length arrr = 5%nat;
       secp256k1_fe_array.boundBy 1 arrr;
       eqm secp256k1_P (secp256k1_fe_array.from_array arra * secp256k1_fe_array.from_array arrb) (secp256k1_fe_array.from_array arrr))
  RETURN()
  SEP(data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrr) a;
      data_at shb (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrb) b).

(* Use with
   forward_call secp256k1_fe_mul_inner_spec_restrict_sub (a, sha, arra, b, shb, arrb)
*)
Lemma secp256k1_fe_mul_inner_spec_alias_sub :
  funspec_sub (snd secp256k1_fe_mul_inner_spec) (snd secp256k1_fe_mul_inner_spec_alias).
Proof.
do_funspec_sub.
destruct w as [[[[[a sha] arra] b] shb] arrb].
entailer!.
Exists ((((((@None (val * share), a), sha), arra), b), shb), arrb) emp.
simpl; entailer!.
intros.
split.
* entailer!.
  Exists x.
  entailer!.
* apply nonempty_writable_glb; assumption.
Qed.

Definition secp256k1_fe_sqr_inner_spec : ident * funspec :=
DECLARE _secp256k1_fe_sqr_inner
  WITH r : option (val * share),
       a : val, sha : share, arra : list Z
    PRE [ tptr tulong, tptr tulong ]
    PROP(writable_share (withOption sha snd r);
         readable_share sha;
         length arra = 5%nat;
         secp256k1_fe_array.boundBy 8 arra)
    PARAMS(withOption a fst r; a)
  SEP(withOption emp (fun '(v, sh) => data_at_ sh (tarray tulong 5) v) r;
      data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a)
POST [ tvoid ]
  EX arrr : list Z,
  PROP(length arrr = 5%nat;
       secp256k1_fe_array.boundBy 1 arrr;
       eqm secp256k1_P (secp256k1_fe_array.from_array arra ^ 2) (secp256k1_fe_array.from_array arrr))
  RETURN()
  SEP(data_at (withOption sha snd r) (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arrr) (withOption a fst r);
      withOption emp (fun _ => (data_at sha (tarray tulong 5) (map (fun x => Vlong (Int64.repr x)) arra) a)) r).

