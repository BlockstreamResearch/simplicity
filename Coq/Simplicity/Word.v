Require Import Logic.Eqdep_dec.
Require Import List.
Require Import ZArith.
Require Import Simplicity.Util.Arith.
Require Import Lia.
Require Coq.Vectors.Vector.
Require compcert.lib.Integers.

Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.
Require Import Simplicity.Digest.
Set Implicit Arguments.

Local Set Keyed Unification.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.

Fixpoint Vector X (n : nat) :=
match n with
| 0 => X
| S n => let rec := Vector X n in Prod rec rec
end.

Lemma VectorPromote {X n} : Vector X (S n) = Vector (X * X) n.
Proof.
induction n.
- reflexivity.
- cbn.
  rewrite <-!IHn.
  reflexivity.
Defined.

Definition Word := Vector Bit.

Module ToZ.

Record class T := Class
  { bitSize : nat
  ; toZ : T -> Z
  ; fromZ : Z -> T
  ; from_toZ : forall (v : T), fromZ (toZ v) = v
  ; to_fromZ : forall (z : Z), toZ (fromZ z) = Zmod z (two_power_nat bitSize)
  }.

Structure type := Pack { obj :> Ty; class_of : class obj }.
Arguments Pack : clear implicits.

Module Theory.

Section Context.

Context {T : type}.

Definition bitSize : nat := bitSize (class_of T).
Definition toZ : obj T -> Z := toZ (class_of T).
Definition fromZ : Z -> obj T := fromZ (class_of T).

Lemma from_toZ (v : T) : fromZ (toZ v) = v.
Proof.
unfold fromZ, toZ.
destruct (class_of T); auto.
Qed.

Lemma to_fromZ (z : Z) : toZ (fromZ z : T) = Zmod z (two_power_nat bitSize).
Proof.
unfold fromZ, toZ, bitSize.
destruct (class_of T); auto.
Qed.

Lemma toZ_mod (v : T) : toZ v = Zmod (toZ v) (two_power_nat bitSize).
Proof.
rewrite <- from_toZ at 1.
apply to_fromZ.
Qed.

Lemma galois (v : T) (z : Z) : v = fromZ z <-> eqm (two_power_nat bitSize) (toZ v) z.
Proof.
unfold eqm.
split.
- intros ->.
  rewrite to_fromZ.
  rewrite Z.mod_mod;[reflexivity|].
  rewrite two_power_nat_equiv.
  auto using  Z.pow_nonzero with zarith.
- unfold eqm.
  rewrite <- 2!to_fromZ, from_toZ.
  rewrite <- from_toZ at 2.
  intros ->.
  rewrite from_toZ.
  reflexivity.
Qed.

End Context.
Arguments bitSize : clear implicits.
End Theory.
End ToZ.
Export ToZ.Theory.
Coercion ToZ.obj : ToZ.type >-> Ty.

Section BitToZ.

Let BitToZ (v : Bit) : Z :=
match v with
| Bit.zero => 0%Z
| Bit.one => 1%Z
end.

Let BitFromZ (z : Z) : Bit :=
if Z.odd z then Bit.one else Bit.zero.

Lemma Bit_from_toZ (v : Bit) : BitFromZ (BitToZ v) = v.
Proof.
destruct v as [[] | []]; reflexivity.
Qed.

Lemma Bit_to_fromZ (z : Z) : BitToZ (BitFromZ z) = Zmod z (two_power_nat 1).
Proof.
unfold BitFromZ.
rewrite (Zmod_odd z).
destruct (Z.odd z); reflexivity.
Qed.

Definition BitToZ_Class := ToZ.Class 1 BitToZ BitFromZ Bit_from_toZ Bit_to_fromZ.
End BitToZ.
Canonical Structure BitToZ : ToZ.type := ToZ.Pack Bit BitToZ_Class.

Section PairToZ.
Context {a b : ToZ.type}.

Let PairBitSize : nat := bitSize a + bitSize b.

Let PairToZ (v : a * b) : Z :=
let (va, vb) := v in
 toZ va * two_power_nat (bitSize b) +
 toZ vb.

Let PairFromZ (z : Z) : a * b :=
( fromZ (z / two_power_nat (bitSize b))
, fromZ z
).

Lemma Pair_from_toZ (v : a * b) : PairFromZ (PairToZ v) = v.
Proof.
destruct v as [va vb].
cbn; unfold PairFromZ.
assert (Hb : two_power_nat (bitSize b) <> 0%Z).
 rewrite two_power_nat_equiv.
 apply Z.pow_nonzero; auto with zarith.
f_equal.
- rewrite Z_div_plus_full_l by auto.
  rewrite <- (from_toZ vb), to_fromZ.
  rewrite Zmod_div, Z.add_0_r.
  apply from_toZ.
- rewrite <- (from_toZ (fromZ _ )), to_fromZ.
  rewrite Zplus_comm, Z_mod_plus_full.
  rewrite <- toZ_mod.
  apply from_toZ.
Qed.

Lemma Pair_to_fromZ (z : Z) : PairToZ (PairFromZ z) = Zmod z (two_power_nat PairBitSize).
Proof.
assert (H2 : forall n, (0 < Zpower_nat 2 n)%Z).
 intros n.
 rewrite Zpower_nat_Z.
 auto using Z.pow_pos_nonneg with zarith.
assert (H2' : forall n, (Zpower_nat 2 n <> 0)%Z).
 intros n.
 generalize (H2 n).
 lia.
unfold PairBitSize.
rewrite two_power_nat_correct, Zpower_nat_is_exp.
rewrite Zmult_comm, Z.rem_mul_r by auto; cbn.
rewrite 2!to_fromZ; rewrite !two_power_nat_correct.
rewrite Zplus_comm, Zmult_comm; reflexivity.
Qed.

Definition PairToZ_Class :=
  ToZ.Class PairBitSize PairToZ PairFromZ Pair_from_toZ Pair_to_fromZ.

End PairToZ.
Canonical Structure PairToZ (a b : ToZ.type) : ToZ.type := ToZ.Pack (a * b) PairToZ_Class.

Lemma toZ_Pair {A B : ToZ.type} (a : A) (b : B) :
  @toZ (PairToZ A B) (a, b) = (toZ a * two_power_nat (bitSize B) + toZ b)%Z.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Lemma bitSize_Pair (A B : ToZ.type) :
  bitSize (PairToZ A B) = (bitSize A + bitSize B)%nat.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Fixpoint WordToZ_Class {n : nat} : ToZ.class (Word n) :=
match n with
| 0 => BitToZ_Class
| (S m) => @PairToZ_Class (ToZ.Pack _ WordToZ_Class) (ToZ.Pack _ WordToZ_Class)
end.

Canonical Structure WordToZ (n : nat) : ToZ.type := ToZ.Pack (Word n) WordToZ_Class.

Notation Word8 := (Word 3).
Notation Word16 := (Word 4).
Notation Word32 := (Word 5).
Notation Word64 := (Word 6).
Notation Word256 := (Word 8).
Notation Word512 := (Word 9).

Lemma bitSize_Word n :
  Z.of_nat (bitSize (WordToZ n)) = two_power_nat n.
Proof.
induction n.
 reflexivity.
cbn.
rewrite Nat2Z.inj_add, IHn, two_power_nat_S.
ring.
Qed.

Lemma testbitToZLo {n} (ahi alo : Word n) i (Hi : (i < two_power_nat n)%Z) :
  Z.testbit (toZ ((ahi, alo) : Word (S n))) i = Z.testbit (toZ alo) i.
Proof.
rewrite (toZ_Pair ahi alo), two_power_nat_equiv, <- (Z.mod_pow2_bits_low _ _ _ Hi),
        bitSize_Word, Zplus_comm, Z_mod_plus_full.
auto using Z.mod_pow2_bits_low.
Qed.

Lemma testbitToZHi {n} (ahi alo : Word n) i (Hi : (two_power_nat n <= i)%Z) :
  Z.testbit (toZ ((ahi, alo) : Word (S n))) i = Z.testbit (toZ ahi) (i - two_power_nat n).
Proof.
rewrite <- bitSize_Word in *.
replace i with (i - Z.of_nat (bitSize (WordToZ n)) + Z.of_nat (bitSize (WordToZ n)))%Z at 1 by ring.
rewrite (toZ_Pair ahi alo), two_power_nat_equiv, <- Z.div_pow2_bits,
        Zplus_comm, Z_div_plus, (toZ_mod alo), two_power_nat_equiv, Zmod_div, Z.add_0_l;
auto using Z.lt_gt, Z.pow_pos_nonneg with zarith.
Qed.

Definition to_hash256 (h : Word256) : hash256 :=
  let '(((h0,h1),(h2,h3)),((h4,h5),(h6,h7))) := h in
    Hash256 (List.map (fun x : Word32 => Integers.Int.repr (toZ x))
              [h0;h1;h2;h3;h4;h5;h6;h7])
            refl_equal.

Definition from_hash256 (l : hash256) : Word256 :=
match map (fun x => fromZ (Integers.Int.unsigned x) : Word32) (hash256_reg l) with
| [h0;h1;h2;h3;h4;h5;h6;h7] => (((h0,h1),(h2,h3)),((h4,h5),(h6,h7)))
| _ => fromZ 0%Z
end.

Lemma from_to_hash256 (h : Word256) : from_hash256 (to_hash256 h) = h.
Proof.
assert (H32 : forall x : Word32, (0 <= toZ x <= Integers.Int.max_unsigned)%Z).
 intros x.
 change Integers.Int.max_unsigned with (Z.pred Integers.Int.modulus).
 rewrite <- Z.lt_le_pred, toZ_mod.
 apply Z.mod_pos_bound.
 reflexivity.
destruct h as [[[h0 h1][h2 h3]][[h4 h5][h6 h7]]]; cbn -[Word toZ fromZ].
repeat rewrite Integers.Int.unsigned_repr by auto.
repeat rewrite from_toZ.
reflexivity.
Qed.

Lemma to_from_hash256 (h : hash256) : to_hash256 (from_hash256 h) = h.
Proof.
destruct h as [[|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|h8 h]]]]]]]]] Hh]; try discriminate.
simpl.
rewrite !to_fromZ.
change (two_power_nat (bitSize (WordToZ 5))) with Integers.Int.modulus.
rewrite <- !Integers.Int.unsigned_repr_eq, !Integers.Int.repr_unsigned.
elim Hh using K_dec_set;[decide equality|].
reflexivity.
Qed.

Section Definitions.

Section Arith.

Fixpoint zero {n : nat} {term : Core.Algebra} : term Unit (Word n) :=
match n with
| 0 => false
| S n => zero &&& zero
end.

Definition adderBit {term : Core.Algebra} : term (Bit * Bit) (Bit * Bit) :=
  cond (iden &&& not iden) (false &&& iden).

Definition fullAdderBit {term : Core.Algebra} : term (Bit * (Bit * Bit)) (Bit * Bit) :=
  maj &&& xor3.

Definition buildFullAdder {W} {term : Core.Algebra} (rec : term (Bit * (W * W)) (Bit * W)) :
  term (Bit * ((W * W) * (W * W))) (Bit * (W * W)) :=
    drop (O O H &&& I O H) &&& (O H &&& drop (O I H &&& I I H) >>> rec)
>>> I I H &&& (I O H &&& O H >>> rec)
>>> I O H &&& (I I H &&& O H).

Fixpoint fullAdder {n : nat} {term : Core.Algebra} : term (Bit * (Word n * Word n)) (Bit * Word n) :=
match n with
| 0 => fullAdderBit
| S n => buildFullAdder fullAdder
end.

Definition adder {n : nat} {term : Core.Algebra} : term (Word n * Word n) (Bit * Word n) :=
match n with
| 0 => adderBit
| S n => false &&& iden >>> fullAdder
end.

Definition fullMultiplierBit {term : Core.Algebra} : term ((Bit * Bit) * (Bit * Bit)) (Word 1) :=
    take (cond iden false) &&& drop iden
>>> fullAdderBit.

Definition buildFullMultiplier {W} {term : Core.Algebra} (rec : term ((W * W) * (W * W)) (W * W)) :
  term (((W * W) * (W * W)) * ((W * W) * (W * W))) (((W * W) * (W * W))) :=
    take (O O H &&& (I O H &&& O I H))
&&& ((take (O O H &&& I I H) &&& drop (O O H &&& I O H) >>> rec)
&&& (take (O I H &&& I I H) &&& drop (O I H &&& I I H) >>> rec))
>>> take (O H &&& I O H)
&&& (drop (O O H &&& I I H) &&& (O I H &&& drop (O I H &&& I O H) >>> rec))
>>> (O H &&& drop (I O H &&& O O H) >>> rec) &&& drop (I I H &&& O I H).

Fixpoint fullMultiplier {n : nat} {term : Core.Algebra} : term ((Word n * Word n) * (Word n * Word n)) (Word (S n)) :=
match n with
| 0 => fullMultiplierBit
| S n => buildFullMultiplier fullMultiplier
end.

Definition multiplier {n : nat} {term : Core.Algebra} : term (Word n * Word n) (Word (S n)) :=
   iden &&& (unit >>> zero &&& zero) >>> fullMultiplier.

End Arith.

Section Vector.

Definition build_fill {C X} {term : Core.Algebra} 
  (rec : term C X) : term C (X * X) := rec &&& rec.

Fixpoint fill {C X n} {term : Core.Algebra} (t : term C X) : term C (Vector X n) :=
match n with
| 0 => t
| (S n) => build_fill (fill t)
end.

Definition buildBitwiseTri {W} {term : Core.Algebra} (rec : term (W * (W * W)) W) :
  term ((W * W) * ((W * W) * (W * W))) (W * W) :=
    (O O H &&& (I O O H &&& I I O H) >>> rec)
&&& (O I H &&& (I O I H &&& I I I H) >>> rec).

Fixpoint bitwiseTri {X} {n : nat} {term : Core.Algebra} (op : term (X * (X * X)) X) :
  term (Vector X n * (Vector X n * Vector X n)) (Vector X n) :=
match n with
| 0 => op
| S n => buildBitwiseTri (bitwiseTri op)
end.

Definition build_leftmost {V X} {term : Core.Algebra} 
  (rec : term V X) : term (V * V) X := take rec.

Fixpoint leftmost {X n} {term : Core.Algebra} : term (Vector X n) X :=
match n with
| 0 => iden
| S n => build_leftmost leftmost
end.

Definition build_rightmost {V X} {term : Core.Algebra} 
  (rec : term V X) : term (V * V) X := drop rec.

Fixpoint rightmost {X n} {term : Core.Algebra} : term (Vector X n) X :=
match n with
| 0 => iden
| S n => build_rightmost rightmost
end.

Definition build_full_left_shift1 {X W} {term : Core.Algebra} 
  (rec : term (W * X) (X * W)) : term ((W * W) * X) (X * (W * W)) :=
   O O H &&& (O I H &&& I H >>> rec) >>> (O H &&& I O H >>> rec) &&& I I H >>> O O H &&& (O I H &&& I H).

Fixpoint full_left_shift1 {X n} {term : Core.Algebra} :
  term (Vector X n * X) (X * Vector X n) :=
match n with
| 0 => iden
| S n => build_full_left_shift1 full_left_shift1
end.

Definition build_full_right_shift1 {X W} {term : Core.Algebra} 
  (rec : term (X * W) (W * X)) : term (X * (W * W)) ((W * W) * X) :=
(O H &&& I O H >>> rec) &&& I I H >>> O O H &&& (O I H &&& I H >>> rec) >>> (O H &&& I O H) &&& I I H.

Fixpoint full_right_shift1 {X n} {term : Core.Algebra} :
  term (X * Vector X n) (Vector X n * X) :=
match n with
| 0 => iden
| S n => build_full_right_shift1 full_right_shift1
end.

Definition left_shift1 {X n} {term : Core.Algebra} (t : term Unit X) : term (Vector X n) (Vector X n) :=
iden &&& (unit >>> t) >>> full_left_shift1 >>> I H.

Fixpoint left_shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (p : positive) 
 : term (Vector X n) (Vector X n) :=
if (Zpower_nat 2 n <=? Zpos p)%Z then
 unit >>> fill t else
match n with 
| 0 => iden
| (S n0) => match p with
  | xH => left_shift1 t
  | xO p0 => eq_rect _ (fun x => term x x) (left_shift_const_by (t &&& t) p0) _ (eq_sym VectorPromote)
  | xI p0 => left_shift1 t >>> eq_rect _ (fun x => term x x) (left_shift_const_by (t &&& t) p0) _ (eq_sym VectorPromote)
  end
end.

Definition right_shift1 {X n} {term : Core.Algebra} (t : term Unit X) : term (Vector X n) (Vector X n) :=
(unit >>> t) &&& iden >>> full_right_shift1 >>> O H.

Fixpoint right_shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (p : positive) 
 : term (Vector X n) (Vector X n) :=
if (Zpower_nat 2 n <=? Zpos p)%Z then
 unit >>> fill t else
match n with 
| 0 => iden
| (S n0) => match p with
  | xH => right_shift1 t
  | xO p0 => eq_rect _ (fun x => term x x) (right_shift_const_by (t &&& t) p0) _ (eq_sym VectorPromote)
  | xI p0 => right_shift1 t >>> eq_rect _ (fun x => term x x) (right_shift_const_by (t &&& t) p0) _ (eq_sym VectorPromote)
  end
end.

Definition shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (c : Z) 
 : term (Vector X n) (Vector X n) :=
match c with
| Z0 => iden
| Zpos p => left_shift_const_by t p
| Zneg p => right_shift_const_by t p
end.

Definition shift_const {n} {term : Core.Algebra} : Z -> term (Vector Bit n) (Vector Bit n) :=
  shift_const_by false.

Definition left_rotate1 {X n} {term : Core.Algebra} : term (Vector X n) (Vector X n) :=
iden &&& leftmost >>> full_left_shift1 >>> I H.

Definition right_rotate1 {X n} {term : Core.Algebra} : term (Vector X n) (Vector X n) :=
rightmost &&& iden >>> full_right_shift1 >>> O H.

Fixpoint rotate_const_list {X n} {term : Core.Algebra} (z : Z) 
 : list (term (Vector X n) (Vector X n)) :=
match n with 
| 0 => []
| (S n0) =>
  if Z.even z
  then eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div z 2)%Z) _ (eq_sym VectorPromote)
  else if Z.even (Z.div z 2)
  then left_rotate1 :: eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div z 2)%Z) _ (eq_sym VectorPromote)
  else right_rotate1 :: eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div (z + 1) 2)%Z) _ (eq_sym VectorPromote)
end.

Fixpoint foldr_comp {X} {term : Core.Algebra} (l : list (term X X)) : term X X :=
match l with
| [] => iden
| i::[] => i
| i::l => i >>> foldr_comp l
end.

Definition rotate_const {X n} {term : Core.Algebra} (z : Z) : term (Vector X n) (Vector X n) :=
foldr_comp (rotate_const_list z).

End Vector.

End Definitions.

Section Specifications.

Lemma zero_correct n : toZ (|[zero (n:=n)]| tt) = 0%Z.
Proof.
induction n; cbn;[|rewrite IHn];reflexivity.
Qed.

Lemma fullAdder_correct n : forall (a b : Word n) (c : Bit),
  (toZ (|[fullAdder]| (c, (a, b))) = toZ a + toZ b  + toZ c)%Z.
Proof.
induction n. { intros [[] | []] [[] | []] [[] | []]; reflexivity. }
intros [ahi alo] [bhi blo] c.
fold Word in *.
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo).
set (C := two_power_nat _).
transitivity ((toZ ahi + toZ bhi) * C + (toZ alo + toZ blo + toZ c))%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (c, (alo, blo))) as [c0 rlo]; clear alo blo c.
cbn [fst snd].
rewrite (toZ_Pair c0 rlo).
fold C.
transitivity ((toZ ahi + toZ bhi + toZ c0) * C + toZ rlo)%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (c0, (ahi, bhi))) as [c1 rhi]; clear ahi bhi c0.
cbn [fst snd].
rewrite (toZ_Pair c1 rhi); fold C.
rewrite (toZ_Pair c1 _).
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
rewrite (toZ_Pair rhi rlo); fold C.
ring.
Qed.

Lemma adder_correct n : forall (a b : Word n),
  (toZ (|[adder]| (a, b)) = toZ a + toZ b)%Z.
destruct n. { intros [[] | []] [[] | []]; reflexivity. }
unfold adder.
generalize (S n); clear n; intros n a b.
cbn -[toZ].
rewrite fullAdder_correct.
cbn.
ring.
Qed.

Lemma fullMultiplier_correct n : forall (a b c d : Word n),
  (toZ (|[fullMultiplier]| ((a, b), (c, d))) = toZ a * toZ b + toZ c + toZ d)%Z.
Proof.
induction n. { intros [[] | []] [[] | []] [[] | []] [[] | []]; reflexivity. }
intros [ahi alo] [bhi blo] [chi clo] [dhi dlo].
cbn -[toZ]; fold tySem; fold (tySem Bit).
fold Word in *.
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo), (toZ_Pair chi clo), (toZ_Pair dhi dlo).
set (C := two_power_nat _).
transitivity ((toZ ahi * C + toZ alo) * toZ bhi * C +
 ((toZ ahi * toZ blo + toZ chi + toZ dhi) * C) + (toZ alo * toZ blo + toZ clo + toZ dlo))%Z;
 [|ring].
rewrite <- 2!IHn.
destruct (|[fullMultiplier]| ((alo, blo), (clo, dlo))) as [c0 rOO]; clear clo dlo.
destruct (|[fullMultiplier]| ((ahi, blo), (chi, dhi))) as [c1 c2]; clear chi dhi blo.
cbn [fst snd].
fold Word in *.
rewrite (toZ_Pair c1 c2), (toZ_Pair c0 rOO); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c1) * C * C +
 (toZ bhi * toZ alo + toZ c2 + toZ c0) * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((bhi, alo), (c2, c0))) as [c3 rOI]; clear c2 c0 alo.
cbn [fst snd].
fold Word in *.
rewrite (toZ_Pair c3 rOI); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c3 + toZ c1) * C * C + toZ rOI * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((ahi, bhi), (c3, c1))) as [rII rIO]; clear c3 c1 ahi bhi.
rewrite (@toZ_Pair (WordToZ (S n)) (WordToZ (S n))), (toZ_Pair rOI rOO); fold C.
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
set (X := toZ _); ring.
Qed.

Lemma multiplier_correct n : forall (a b : Word n),
  (toZ (|[multiplier]| (a, b)) = toZ a * toZ b)%Z.
Proof.
intros a b.
cbn -[toZ].
rewrite fullMultiplier_correct, zero_correct.
ring.
Qed.

Import Coq.Vectors.Vector.VectorNotations.

Fixpoint replicate {X} (x : X) n : Vector.t X n :=
match n return Vector.t X n with 
| 0 => []
| S m => (x :: replicate x m)
end.

Lemma replicate_append {X} (x : X) n m : replicate x n ++ replicate x m = replicate x (n + m).
Proof.
induction n.
- reflexivity.
- cbn.
  f_equal.
  assumption.
Qed.

Lemma nth_replicate {X n i} (x : X) (ix : i < n) : Vector.nth_order (replicate x n) ix = x.
Proof.
revert i ix.
induction n;[|intros [|i] Hi].
- lia.
- simpl.
  rewrite Vector.nth_order_hd.
  reflexivity.
- assert (Hin : i < n) by lia.
  rewrite <- (Vector.nth_order_tl _ _ _ _ Hin).
  apply IHn.
Qed.

Lemma mul_2_r n : (2 * n = n + n)%nat.
Proof.
cbn.
f_equal.
induction n.
- reflexivity.
- cbn.
  f_equal.
  assumption.
Defined.

Fixpoint flatten {X n} : Vector X n -> Vector.t X (2^n) :=
match n return Vector X n -> Vector.t X (2^n) with
| 0 => fun v => [v]
| S n => fun v => eq_rect _ (Vector.t X) (flatten (fst v) ++ flatten (snd v)) _ (eq_sym (mul_2_r (2^n)))
end.

Lemma fill_correct {C X n} (t : Arrow C X) (c : C) : flatten (|[ fill t ]| c) = replicate (|[ t ]| c) (2^n).
Proof.
induction n.
- reflexivity.
- cbn.
  rewrite IHn.
  generalize ( (mul_2_r (2 ^ n))).
  cbn; intros ->; cbn.
  apply replicate_append.
Qed.

Definition TrinarySpec {n} (f : bool -> bool -> bool -> bool) (term : Arrow (Word n * (Word n * Word n)) (Word n)) :=
  forall (x y z : Word n) i, (Z.testbit (toZ (term (x,(y,z)))) i = f (Z.testbit (toZ x) i) (Z.testbit (toZ y) i) (Z.testbit (toZ z) i))%Z.

Lemma bitwiseTri_correct {n} (f : bool -> bool -> bool -> bool) (op : Arrow (Bit * (Bit * Bit)) Bit)
    (Hf : f Datatypes.false Datatypes.false Datatypes.false = Datatypes.false)
    (Hop : (forall (a b c : Bit), toBool (op (a,(b,c))) = f (toBool a) (toBool b) (toBool c))) :
  TrinarySpec (n:=n) f (bitwiseTri op).
Proof.
induction n.
 intros a b c i.
 simpl (bitwiseTri op).
 assert (to01 : (forall (b : Bit), Z.testbit (toZ b) i = if toBool b then Z.testbit 1 i else Z.testbit 0 i)%Z) by
  (intros [[] | []]; reflexivity).
 repeat rewrite to01.
 rewrite Hop; clear - Hf.
 destruct (toBool a);
 destruct (toBool b);
 destruct (toBool c);
 destruct i; cbn; try rewrite Hf; try reflexivity;
 destruct (f _ _ _) in |- *; reflexivity.
intros [ahi alo] [bhi blo] [chi clo] i.
destruct (Z_lt_le_dec i (two_power_nat n)) as [Hi|Hi]; cbn;
[repeat rewrite (testbitToZLo _ _ Hi)
|repeat rewrite (testbitToZHi _ _ Hi)
]; auto.
Qed.

Definition pow_succ n : (2^n = S (pred (2^n)))%nat.
case_eq (2^n).
- abstract (intros H;elim (Nat.pow_nonzero 2 n);lia).
- reflexivity.
Defined.

Definition pow_hd {X n} (v : Vector.t X (2^n)) : X :=
Vector.hd (eq_rect _ (Vector.t X) v _ (pow_succ n)).

Definition pow_last {X n} (v : Vector.t X (2^n)) : X :=
Vector.last (eq_rect _ (Vector.t X) v _ (pow_succ n)).

Lemma hd_flatten {X n} (v0 v1 : Vector X n):
  pow_hd (@flatten X (S n) (v0,v1)) = pow_hd (@flatten X n v0).
Proof.
unfold pow_hd; cbn.
generalize (mul_2_r (2 ^ n)) (pow_succ n) (pow_succ (S n)).
  change (2 * 2 ^ n)%nat with (2 ^ (S n))%nat.
change (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat.
intros -> e0 e1; simpl.
cut (forall a b (e0 : a = S (Init.Nat.pred a))
(e1 : (a + b)%nat = S (Init.Nat.pred (a + b)))
  (v : Vector.t X a) (w : Vector.t X b),
Vector.hd
  (eq_rect (a + b)%nat (Vector.t X) (v ++ w)
     (S (Init.Nat.pred (a + b))) e1) =
Vector.hd
  (eq_rect a (Vector.t X) v (S (Init.Nat.pred a)) e0));
[intros H0; apply H0|clear e0 e1].
intros a b -> e; simpl.
elim e using K_dec_set;[apply Nat.eq_dec|simpl].
intros v.
rewrite (Vector.eta v).
reflexivity.
Qed.

Lemma leftmost_correct {X n v} : |[ leftmost ]| v = pow_hd (@flatten X n v).
Proof.
induction n.
- reflexivity.
- cbn.
  rewrite IHn; clear IHn.
  symmetry.
  apply hd_flatten.
Qed.

Lemma Vector_eta_shift {X n} (v : Vector.t X (S n)) : v = Vector.shiftin (Vector.last v) (Vector.shiftout v).
Proof.
elim v using Vector.rectS.
- reflexivity.
- simpl. intros a c w IH. f_equal. assumption.
Qed.

Lemma rightmost_correct {X n v} : |[ rightmost ]| v = pow_last (@flatten X n v).
Proof.
induction n.
- reflexivity.
- cbn.
  rewrite IHn; clear IHn.
  unfold pow_last.
  generalize (mul_2_r (2 ^ n)) (pow_succ n) (pow_succ (S n)).
    change (2 * 2 ^ n)%nat with (2 ^ (S n))%nat.
  change (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat.
  intros -> e0 e1; simpl.
  cut (forall a b (e0 : b = S (Init.Nat.pred b))
  (e1 : (a + b)%nat = S (Init.Nat.pred (a + b)))
  (v : Vector.t X a) (w : Vector.t X b),
Vector.last
  (eq_rect b (Vector.t X) w (S (Init.Nat.pred b)) e0) =
Vector.last
  (eq_rect (a + b)%nat (Vector.t X) (v ++ w)
     (S (Init.Nat.pred (a + b))) e1));
  [intros H0; apply H0|clear v e0 e1].
  intros a b ->; simpl.
  replace (Init.Nat.pred (a + S (Init.Nat.pred b))) with 
    (a + Init.Nat.pred b)%nat by (rewrite Nat.add_succ_r; reflexivity).
  intros e v w.
  transitivity (Vector.last (Vector.shiftin (Vector.last w) (v ++ Vector.shiftout w)));
  [rewrite Vector.shiftin_last; reflexivity|].
  f_equal.
  revert e w.
  generalize (pred b); clear b.
  (* This shiftin/app/shiftout lemma could perhaps be generalized *)
  induction v.
  + simpl.
    intros b e w.
    elim e using K_dec_set;[apply Nat.eq_dec|clear e].
    simpl.
    symmetry.
    apply Vector_eta_shift.
  + simpl.
    intros b e w.
    assert (e0 : (n0 + S b)%nat = S (n0 + b)) by lia.
    rewrite (IHv b e0).
    generalize (v ++ w).
    revert e.
    rewrite e0.
    intros e.
    elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
Qed.

Definition map_fst {A B C} (f : A -> B) (v : A * C) : B * C := (f (fst v), snd v).
Definition map_snd {A B C} (f : B -> C) (v : A * B) : A * C := (fst v, f (snd v)).

Lemma tail_shiftin {X n} x (v: Vector.t X (S n)) :
  Vector.tl (Vector.shiftin x v) = Vector.shiftin x (Vector.tl v).
Proof.
rewrite (Vector.eta v).
reflexivity.
Qed.

Lemma shiftin_append {X n m} (e : (n + S m = S (n + m))%nat) x (v0 : Vector.t X n) (v1 : Vector.t X m) :
  Vector.shiftin x (v0 ++ v1) = eq_rect _ (Vector.t X) (v0 ++ (Vector.shiftin x v1)) _ e.
Proof.
revert e.
induction v0.
- cbn; intros e.
  elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
- intros e.
  assert (e0 : (n + S m)%nat = S (n + m)) by lia.
  cbn in *.
  rewrite (IHv0 e0).
  revert e.
  rewrite <- e0.
  cbn.
  intros e.
  elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
Qed.

Lemma append_shiftin {X n m} (e : (n + S m = S (n + m))%nat) x (v0 : Vector.t X n) (v1 : Vector.t X m) :
  Vector.shiftin x v0 ++ v1 = eq_rect _ (Vector.t X) (v0 ++ x ::v1) _ e.
Proof.
revert e.
induction v0.
- cbn; intros e.
  elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
- intros e.
  assert (e0 : (n + S m)%nat = S (n + m)) by lia.
  cbn in *.
  rewrite (IHv0 e0).
  revert e.
  rewrite <- e0.
  cbn.
  intros e; elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
Qed.

Lemma last_flatten {X n} v0 v1 :
  pow_last (@flatten X (S n) (v0,v1)) = pow_last (@flatten X n v1).
Proof.
fold tySem Vector in *.
unfold pow_last; cbn.
generalize (mul_2_r (2 ^ n)) (pow_succ n) (pow_succ (S n)).
  change (2 * 2 ^ n)%nat with (2 ^ (S n))%nat.
change (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat.
intros -> e0 e1; simpl.
cut (forall a b (e0 : b = S (Init.Nat.pred b))
(e1 : (a + b)%nat = S (Init.Nat.pred (a + b)))
  (v : Vector.t X a) (w : Vector.t X b),
Vector.last
  (eq_rect (a + b)%nat (Vector.t X) (v ++ w)
     (S (Init.Nat.pred (a + b))) e1) =
Vector.last
  (eq_rect b (Vector.t X) w (S (Init.Nat.pred b)) e0));
[intros H0; apply H0|clear e0 e1].
intros a b -> e v w; simpl.
revert e.
replace (Init.Nat.pred (a + S (Init.Nat.pred b))) with (a + (Init.Nat.pred b))%nat by lia.
rewrite (Vector_eta_shift w).
intros e.
rewrite <- (shiftin_append e).
rewrite !VectorSpec.shiftin_last.
reflexivity.
Qed.

Lemma full_left_shift1_correct {X n v x} :
  map_snd flatten (|[ full_left_shift1 ]| (v, x)) = (pow_hd (@flatten X n v), Vector.tl (Vector.shiftin x (flatten v))).
Proof.
fold tySem in *.
revert x.
induction n.
- reflexivity.
- destruct v as [v0 v1].
  simpl.
  unfold build_full_left_shift1.
  intros x.
  unfold map_snd.
  cbn.
  injection (IHn v1 x); intros -> ->.
  set (y := pow_hd (flatten v1)).
  injection (IHn v0 y); intros -> ->.
  clear IHn.
  f_equal.
  + symmetry. apply hd_flatten.
  + generalize (mul_2_r (2 ^ n)).
    cbn; intros ->; cbn.
    unfold y.
    generalize (flatten v0) (flatten v1).
    clear y v0 v1.
    unfold pow_hd.
    generalize (pow_succ n).
    set (Z := pred (2^n)).
    rewrite (pow_succ n).
    intros ->.
    unfold Z; clear Z.
    cbn.
    intros v0 v1.
    rewrite tail_shiftin.
    rewrite (append_shiftin  (Nat.add_succ_r _ _)).
    replace (Vector.hd v1) with (Vector.hd (Vector.shiftin x v1)) by
      (rewrite (Vector.eta v1); reflexivity).
    rewrite <-Vector.eta.
    rewrite (shiftin_append (Nat.add_succ_r _ _) x v0 v1).
    set (e0 := (Nat.add_succ_r _ _)).
    set (e1 := (Nat.add_succ_r _ _)).
    clearbody e0 e1.
    cbn in *.
    revert e1.
    rewrite <- e0.
    intros e; elim e using K_dec_set;[apply Nat.eq_dec|].
    cbn.
    rewrite (Vector.eta v0).
    reflexivity.
Qed.

Lemma left_shift1_correct {X n v t} :
  @flatten X n (|[ left_shift1 t ]| v) = Vector.tl (Vector.shiftin (|[ t ]| tt) (flatten v)).
Proof.
unfold left_shift1.
cbn.
change (flatten (snd _)) with (snd (map_snd flatten (|[full_left_shift1]| (v, t tt)))).
rewrite full_left_shift1_correct.
reflexivity.
Qed.

Lemma shiftout_append {X n m} (e : (n + S m = S (n + m))%nat) (v0 : Vector.t X n) (v1 : Vector.t X (S m)) :
  Vector.shiftout (eq_rect _ (Vector.t X) (v0 ++ v1) _ e) = v0 ++ (Vector.shiftout v1).
Proof.
revert e.
induction v0.
- cbn; intros e.
  elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
- intros e.
  assert (e0 : (n + S m)%nat = S (n + m)) by lia.
  cbn in *.
  rewrite <-(IHv0 e0).
  generalize (v0 ++ v1).
  revert e.
  rewrite e0.
  cbn.
  intros e.
  elim e using K_dec_set;[apply Nat.eq_dec|reflexivity].
Qed.

Lemma full_right_shift1_correct {X n v x} :
  map_fst flatten (|[ full_right_shift1 ]| (x, v)) = (Vector.shiftout (x :: flatten v), pow_last (@flatten X n v)).
Proof.
fold tySem in *.
revert x.
induction n.
- reflexivity.
- destruct v as [v0 v1].
  simpl (map_fst _ _).
  unfold build_full_right_shift1.
  intros x.
  unfold map_fst.
  etransitivity;[cbn|reflexivity].
  unfold map_fst in IHn.
  replace (flatten (fst (|[full_right_shift1]| (x, v0)))) with (Vector.shiftout (x :: flatten v0))
  by (injection (IHn v0 x); auto).
  replace (snd (|[full_right_shift1]| (x, v0))) with (pow_last (flatten v0))
  by (injection (IHn v0 x); auto).
  set (y := pow_last (flatten v0)).
  replace (flatten (fst (|[full_right_shift1]| (y, v1)))) with (Vector.shiftout (y :: flatten v1))
  by (injection (IHn v1 y); auto).
  replace (snd (|[full_right_shift1]| (y, v1))) with (pow_last (flatten v1))
  by (injection (IHn v1 y); auto).
  clear IHn.
  f_equal.
  + simpl (@flatten X (S n) (v0, v1)).
    generalize (mul_2_r (2 ^ n)).
    simpl (2 * _)%nat; simpl (2 ^ (S n))%nat.
    intros ->.
    change (Vector.shiftout (x :: flatten v0) ++ Vector.shiftout (y :: flatten v1)
         = Vector.shiftout (x :: (flatten v0 ++ flatten v1))).
    unfold y.
    generalize (flatten v0) (flatten v1).
    clear y v0 v1.
    unfold pow_last.
    generalize (pow_succ n).
    set (Z := pred (2^n)).
    rewrite (pow_succ n).
    intros ->.
    unfold Z; clear Z.
    cbn.
    intros v0 v1.
    f_equal.
    change (eq_rect _ (Vector.t X) (Vector.shiftout v0 ++ Vector.last v0 :: Vector.shiftout v1) _ eq_refl
      = Vector.shiftout (v0 ++ v1)).
    rewrite <- (eq_trans_sym_inv_r (Nat.add_succ_r _ _)), eq_trans_rew_distr.
    rewrite <- append_shiftin.
    rewrite <- Vector_eta_shift.
    rewrite <- (shiftout_append (Nat.add_succ_r _ _)).
    generalize (v0 ++ v1).
    generalize (Nat.add_succ_r (S (Init.Nat.pred (2 ^ n)))
           (Init.Nat.pred (2 ^ n))).
    generalize (Nat.add_succ_r (Init.Nat.pred (2 ^ n))
           (Init.Nat.pred (2 ^ n))).
    cbn; intros <-; cbn.
    intros e;elim e using K_dec_set;[apply Nat.eq_dec|].
    reflexivity.
  + symmetry. apply last_flatten.
Qed.

Lemma right_shift1_correct {X n v t} :
  @flatten X n (|[ right_shift1 t ]| v) = Vector.shiftout (|[ t ]| tt :: flatten v).
Proof.
unfold right_shift1.
etransitivity;[cbn|reflexivity].
change (flatten (fst _)) with (fst (map_fst flatten (|[full_right_shift1]| (t tt, v)))).
rewrite full_right_shift1_correct.
reflexivity.
Qed.

Lemma nth_order_shiftout {X n i} (v : Vector.t X (S n)) (ix1 : i < n) (ix2 : i < S n) :
 Vector.nth_order (Vector.shiftout v) ix1 = Vector.nth_order v ix2.
Proof.
revert i ix1 ix2.
elim v using Vector.rectS.
- lia.
- intros h n0 t IHv i ix1 ix2.
  destruct i. 
  + rewrite !Vector.nth_order_hd.
    reflexivity.
  + assert (ix1' : i < n0) by lia.
    assert (ix2' : i < S n0) by lia.
    rewrite <-(Vector.nth_order_tl _ _ _ _ ix1').
    rewrite <-(Vector.nth_order_tl _ _ _ _ ix2').
    change (VectorDef.nth_order (Vector.shiftout t) ix1' = VectorDef.nth_order t ix2').
    apply IHv.
Qed.

Lemma nth_order_append_front {X n m i} (v : Vector.t X n) (w : Vector.t X m) (ix1 : i < n + m) (ix2 : i < n) :
  Vector.nth_order (v ++ w) ix1 = Vector.nth_order v ix2.
Proof.
revert i ix1 ix2.
induction v;[lia|].
intros [|i] ix1 ix2;simpl.
- rewrite !Vector.nth_order_hd.
  reflexivity.
- assert (ix1' : i < n + m) by lia.
  assert (ix2' : i < n) by lia.
  rewrite <-(Vector.nth_order_tl _ _ _ _ ix1'), <-(Vector.nth_order_tl _ _ _ _ ix2').
  simpl.
  apply IHv.
Qed.

Lemma nth_order_append_back {X n m i} (v : Vector.t X n) (w : Vector.t X m) (ix1 : n + i < n + m) (ix2 : i < m) :
  Vector.nth_order (v ++ w) ix1 = Vector.nth_order w ix2.
Proof.
revert i ix1 ix2.
induction v; intros i ix1 ix2.
- apply Vector.nth_order_ext.
- simpl.
  assert (ix1' : n + i < n + m) by lia.
  rewrite <- (Vector.nth_order_tl _ _ _ _ ix1').
  apply IHv.
Qed.

Lemma nth_order_flatten {X n i} (v : Vector (X * X) n) (ix :(i < 2^n)) (ix1 : 2*i < 2^(S n)) (ix2 : 2*i + 1 < 2^(S n)) : 
         Vector.nth_order (flatten v) ix =
         (Vector.nth_order (flatten (eq_rect _ tySem v _ (eq_sym VectorPromote))) ix1,
          Vector.nth_order (flatten (eq_rect _ tySem v _ (eq_sym VectorPromote))) ix2).
Proof.
revert v i ix ix1 ix2.
induction n; intros [v0 v1] i ix ix1 ix2.
- simpl in *|-.
  destruct i;[|lia].
  reflexivity.
- simpl (@flatten _ (S n) _).
  simpl (2 ^ _)%nat in *.
  revert ix.
  generalize (mul_2_r (2 ^ n)); simpl (2 * 2 ^ n)%nat.
  intros -> ix.
  fold (2^n).
  simpl (eq_rect _ _ _ _ (eq_sym eq_refl)).
  replace (eq_rect (Vector (X * X) (S n)) tySem (v0, v1) (Vector X (S (S n))) (eq_sym VectorPromote))
   with ((eq_rect (Vector (X * X) n) tySem v0
               (Vector X (S n)) (eq_sym VectorPromote)), (eq_rect (Vector (X * X) n) tySem v1
               (Vector X (S n)) (eq_sym VectorPromote))).
  2:{
    generalize (eq_sym (@VectorPromote X (S n))).
    revert v0 v1.
    generalize (eq_sym (@VectorPromote X n)).
    simpl.
    intros -> v0 v1 e.
    elim e using K_dec_set;[decide equality|].
    reflexivity.
  }
  set (v0' := (eq_rect (Vector (X * X) n) _ _ _ _)).
  set (v1' := (eq_rect (Vector (X * X) n) _ _ _ _)).
  change (@flatten _ (S (S n)) (v0', v1'))
   with (eq_rect _ (Vector.t X)
     (flatten v0' ++ flatten v1') _
     (eq_sym (mul_2_r (2 ^ (S n))))).
  revert ix1 ix2.
  generalize (mul_2_r (2 ^ S n)).
  simpl (2 * _)%nat.
  simpl (2 ^ _)%nat.
  intros -> ix1 ix2.
  change (Vector.nth_order (flatten v0 ++ flatten v1) ix =
    ( Vector.nth_order (flatten v0' ++ flatten v1') ix1
    , Vector.nth_order (flatten v0' ++ flatten v1') ix2)).
  destruct (Nat.le_gt_cases (2^n) i) as [Hi|ix'].
  + pose (j:= i - 2^n).
    assert (ix' : j < 2 ^ n) by lia.
    assert (ix1' : 2 * j < 2 ^ S n) by (cbn; lia).
    assert (ix2' : 2 * j + 1 < 2 ^ S n) by (cbn; lia).
    revert ix.
    pattern i at 1 2.
    replace i with (2^n + j)%nat by lia.
    intros ix.
    fold (2*i)%nat in *.
    revert ix1.
    pattern (2*i)%nat at 1 2.
    replace (2*i)%nat with (2^(S n) + 2*j)%nat by (cbn;lia).
    intros ix1.
    revert ix2.
    replace (2*i + 1)%nat with (2^(S n) + (2*j + 1))%nat by (cbn;lia).
    intros ix2.
    rewrite (nth_order_append_back _ _ _ ix'),
            (nth_order_append_back _ _ _ ix1'),
            (nth_order_append_back _ _ _ ix2').
    apply IHn.
  + assert (ix1' : 2 * i < 2 ^ S n) by (cbn; lia).
    assert (ix2' : 2 * i + 1 < 2 ^ S n) by (cbn; lia).
    rewrite (nth_order_append_front _ _ _ ix'),
            (nth_order_append_front _ _ _ ix1'),
            (nth_order_append_front _ _ _ ix2').
    apply IHn.
Qed.

Lemma nth_order_flatten_if {X n i} (v : Vector (X * X) n) (ix : i < 2^(S n)) (ix_half : Nat.div2 i < 2^n) :
      Vector.nth_order (flatten (eq_rect _ tySem v _ (eq_sym VectorPromote))) ix =
      (if Nat.even i then fst else snd) (Vector.nth_order (flatten v) ix_half).
Proof.
assert (ix_half1 : 2 * Nat.div2 i < 2 ^ (S n)) by (cbn;lia).
assert (ix_half2 : 2 * Nat.div2 i + 1 < 2 ^ (S n)) by (cbn;lia).
rewrite (nth_order_flatten _ _ ix_half1 ix_half2).
destruct (Nat.Even_Odd_dec i) as [Heven|Hodd].
- rewrite <- Nat.even_spec in Heven.
  rewrite Heven.
  rewrite Nat.even_spec in Heven.
  destruct Heven as [i' ->].
  revert ix_half1 ix_half2.
  rewrite Nat.div2_double.
  intros; apply Vector.nth_order_ext.
- rewrite <- Nat.odd_spec in Hodd.
  rewrite <- Nat.negb_odd, Hodd.
  rewrite Nat.odd_spec in Hodd.
  destruct Hodd as [i' ->].
  revert ix ix_half1 ix_half2.
  replace (2 * i' + 1)%nat with (S (2 * i'))%nat by lia.
  rewrite Nat.div2_succ_double.
  replace (2 * i' + 1)%nat with (S (2 * i'))%nat by lia.
  intros; apply Vector.nth_order_ext.
Qed.

Lemma right_shift_const_by_correct {X n v t p i} (ix1 : i < 2^n) (ix2 : i - Pos.to_nat p < 2^n) :
  Vector.nth_order (@flatten X n (|[ right_shift_const_by t p ]| v)) ix1 =
  if i <? Pos.to_nat p then |[ t ]| tt else Vector.nth_order (@flatten X n v) ix2.
Proof.
revert X t p v i ix1 ix2.
induction n;intros X t p v i ix1 ix2.
- simpl in *.
  destruct i;[|lia].
  elim (Z.leb_spec);[intros _|lia].
  elim (Nat.ltb_spec);[intros _|lia].
  reflexivity.
- simpl (right_shift_const_by t p v).
  change (_ <=? _)%Z with  (Zpower_nat 2 (S n) <=? Z.pos p)%Z.
  elim (Z.leb_spec).
  1:{
    rewrite Zpower_nat_Z.
    change 2%Z with (Z.of_nat 2%nat) at 1.
    rewrite <- Nat2Z.inj_pow.
    intros Hp.    
    elim (Nat.ltb_spec);[intros _|lia].
    change (Vector.nth_order (flatten (|[@fill _ X (S n)  _ t]| tt)) ix1 = |[t]| tt).
    rewrite fill_correct.
    apply nth_replicate.
  }
  intros Hpn.
  transitivity (match p with
      | (p0~1)%positive => Vector.nth_order (flatten ((
          eq_rect (Vector (X * X) n)
            (fun x : Ty => Arrow x x)
            (right_shift_const_by (t &&& t) p0)
            (Vector X (S n))
            (eq_sym VectorPromote)) (right_shift1 t v))) ix1
      | (p0~0)%positive =>
          Vector.nth_order (flatten ((eq_rect (Vector (X * X) n)
            (fun x : Ty => Arrow x x)
            (right_shift_const_by (t &&& t) p0)
            (Vector X (S n))
            (eq_sym VectorPromote)) v)) ix1
      | 1%positive => Vector.nth_order (flatten (right_shift1 t v)) ix1
      end);
  [destruct p; reflexivity|].
  assert (Hcast : forall (f : Arrow (Vector (X*X) n) (Vector (X*X) n)),
    (eq_rect _ (fun x : Ty => Arrow x x) f _ (eq_sym VectorPromote) =
    (fun w => eq_rect _ tySem (f (eq_rect _ tySem w _ VectorPromote)) _ (eq_sym VectorPromote)))).
  1:{
    generalize (@VectorPromote X n).
    intros <-.
    reflexivity.
  }
  assert (ix_half : Nat.div2 i < 2^n).
  1:{
    rewrite Nat.div2_div.
    apply Nat.div_lt_upper_bound;[lia|].
    rewrite <- Nat.pow_succ_r'.
    assumption.
  }
  specialize (IHn (X*X) (t &&& t)).
  destruct p.
  + rewrite Hcast.
    set (w:= right_shift_const_by (t &&& t) p _).
    rewrite (nth_order_flatten_if _ _ ix_half).
    assert (ix_half2 : Nat.div2 i - Pos.to_nat p < 2 ^ n) by lia.
    rewrite (IHn _ _ _ ix_half ix_half2).
    elim Nat.ltb_spec; rewrite Nat.div2_div at 1.
    * intros Hip.
      elim Nat.ltb_spec.
      2:{
        rewrite (Pos2Nat.inj_xI p) at 1.
        intros Hpi.
        assert (Hpi0 : S (2 * Pos.to_nat p) / 2 <= i / 2) by (apply Nat.div_le_mono;lia).
        rewrite <- (Nat.div_unique _ _ (Pos.to_nat p) 1) in Hpi0; lia.
      }
      intros _.
      destruct (Nat.even i);reflexivity.
    * intros Hpi.
      assert (ix_half2a : 2*(Nat.div2 i - Pos.to_nat p) < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      assert (ix_half2b : 2*(Nat.div2 i - Pos.to_nat p) + 1 < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      erewrite (nth_order_flatten _ _ ix_half2a ix_half2b).
      rewrite <-eq_trans_rew_distr, eq_trans_sym_inv_r.
      cbn -[right_shift1 flatten Pos.to_nat Nat.ltb].
      rewrite right_shift1_correct.
      elim Nat.ltb_spec.
      1:{
        rewrite (Pos2Nat.inj_xI p) at 1.
        intros Hip.
        assert (Hi : (i = 2*Pos.to_nat p)%nat).
        1:{
          apply Nat.le_antisymm;[lia|].
          apply (Nat.mul_le_mono_l _ _ 2) in Hpi.
          assert (Hle := Nat.mul_div_le i 2).
          lia.
        }
        replace (Nat.even i) with (Nat.even (2 * Pos.to_nat p)%nat) by congruence.
        rewrite Nat.even_mul.
        change (Vector.nth_order (Vector.shiftout (t tt :: flatten v)) ix_half2a = t tt).
        revert ix_half2a.
        rewrite Hi, Nat.div2_double.
        replace (2 * (Pos.to_nat p - Pos.to_nat p))%nat with 0 by lia.
        intros ix_half2a.
        assert (ix_half2a' : 0 < S (2 ^ S n)) by lia.
        rewrite (nth_order_shiftout _ _ ix_half2a').
        rewrite Vector.nth_order_hd.
        reflexivity.
      }
      assert (ix_half2a' : 2 * (Nat.div2 i - Pos.to_nat p) < S (2 ^ S n)) by lia.
      assert (ix_half2b' : 2 * (Nat.div2 i - Pos.to_nat p) + 1 < S (2 ^ S n)) by lia.
      rewrite (nth_order_shiftout _ _ ix_half2a'), (nth_order_shiftout _ _ ix_half2b').
      intros Hp1i.
      transitivity (Vector.nth_order (Vector.tl (t tt :: flatten v)) ix2);[|reflexivity].
      assert (ix2' : S (i - Pos.to_nat p~1) < S (2 ^ S n)) by lia.
      rewrite (VectorSpec.nth_order_tl _ _ _ _ _ ix2').
      destruct (Nat.Even_Odd_dec i) as [Heven|Hodd].
      1:{
        rewrite <- Nat.even_spec in Heven.
        rewrite Heven.
        rewrite Nat.even_spec in Heven.
        destruct Heven as [i' Hi'].
        revert ix2'.
        replace (S (i - Pos.to_nat p~1)) with (2 * (Nat.div2 i - Pos.to_nat p))%nat;
        [intros; apply Vector.nth_order_ext|].
        rewrite Hi', Nat.div2_double.
        lia.
      }
      1:{
        rewrite <- Nat.odd_spec in Hodd.
        rewrite <- Nat.negb_odd, Hodd.
        rewrite Nat.odd_spec in Hodd.
        destruct Hodd as [i' Hi'].
        revert ix2'.
        replace (S (i - Pos.to_nat p~1)) with (2 * (Nat.div2 i - Pos.to_nat p) + 1)%nat;
        [intros; apply Vector.nth_order_ext|].
        replace (2 * i' + 1)%nat with (S (2 * i')) in Hi' by lia.
        rewrite Hi', Nat.div2_succ_double.
        lia.
      }
  + rewrite Hcast.
    set (w:= right_shift_const_by (t &&& t) p _).
    rewrite (nth_order_flatten_if _ _ ix_half).
    assert (ix_half2 : Nat.div2 i - Pos.to_nat p < 2 ^ n) by lia.
    rewrite (IHn _ _ _ ix_half ix_half2).
    elim Nat.ltb_spec; rewrite Nat.div2_div at 1.
    * intros Hip.
      elim Nat.ltb_spec.
      2:{
        rewrite (Pos2Nat.inj_xO p) at 1.
        intros Hpi.
        assert (Hpi0 : (2 * Pos.to_nat p) / 2 <= i / 2) by (apply Nat.div_le_mono;lia).
        rewrite <- (Nat.div_unique _ _ (Pos.to_nat p) 0) in Hpi0; lia.
      }
      intros _.
      destruct (Nat.even i);reflexivity.
    * intros Hpi.
      elim Nat.ltb_spec.
      1:{ 
        rewrite (Pos2Nat.inj_xO p) at 1.
        assert (Hle := Nat.mul_div_le i 2).
        lia.
      }
      assert (ix_half2a : 2*(Nat.div2 i - Pos.to_nat p) < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      assert (ix_half2b : 2*(Nat.div2 i - Pos.to_nat p) + 1 < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      erewrite (nth_order_flatten _ _ ix_half2a ix_half2b).
      rewrite <-eq_trans_rew_distr, eq_trans_sym_inv_r.
      cbn -[right_shift1 flatten Pos.to_nat Nat.ltb].
      intros Hp0i.
      destruct (Nat.Even_Odd_dec i) as [Heven|Hodd].
      1:{
        rewrite <- Nat.even_spec in Heven.
        rewrite Heven.
        rewrite Nat.even_spec in Heven.
        destruct Heven as [i' Hi'].
        revert ix2.
        replace (i - Pos.to_nat p~0) with (2 * (Nat.div2 i - Pos.to_nat p))%nat;
        [intros; apply Vector.nth_order_ext|].
        rewrite Hi', Nat.div2_double.
        lia.
      }
      1:{
        rewrite <- Nat.odd_spec in Hodd.
        rewrite <- Nat.negb_odd, Hodd.
        rewrite Nat.odd_spec in Hodd.
        destruct Hodd as [i' Hi'].
        revert ix2.
        replace (i - Pos.to_nat p~0) with (2 * (Nat.div2 i - Pos.to_nat p) + 1)%nat;
        [intros; apply Vector.nth_order_ext|].
        replace (2 * i' + 1)%nat with (S (2 * i')) in Hi' by lia.
        rewrite Hi', Nat.div2_succ_double.
        lia.
      }
  + rewrite right_shift1_correct.
    assert (ix1' : i < S (2 ^ S n)) by lia.
    rewrite (nth_order_shiftout _ _ ix1').
    elim Nat.ltb_spec; intros Hi.
    * destruct i;[|lia].
      rewrite Vector.nth_order_hd.
      reflexivity.
    * destruct i;[lia|].
      assert (ix1'S : i < 2 ^ S n) by lia.
      rewrite <- (Vector.nth_order_tl _ _ _ _ ix1'S).
      change (Vector.nth_order (flatten v) ix1'S = Vector.nth_order (flatten v) ix2).
      revert ix2.
      replace (S i - Pos.to_nat 1)%nat with i;
      [intros; apply Vector.nth_order_ext|lia].
Qed.

Lemma shiftout_shiftin {X n} a (v : Vector.t X n) : (Vector.shiftout (Vector.shiftin a v)) = v.
Proof.
induction v.
- reflexivity.
- simpl.
  rewrite IHv.
  reflexivity.
Qed.

Lemma left_shift_const_by_correct {X n v t p i} (ix1 : i < 2^n) :
  Vector.nth_order (@flatten X n (|[ left_shift_const_by t p ]| v)) ix1 =
  match lt_dec (i + Pos.to_nat p) (2^n) with
  | left ix2 => Vector.nth_order (@flatten X n v) ix2
  | right _ => |[ t ]| tt
  end.
Proof.
revert X t p v i ix1.
induction n;intros X t p v i ix1.
- simpl in *.
  destruct i;[|lia].
  elim (Z.leb_spec);[intros _|lia].
  destruct (lt_dec _ _);[lia|reflexivity].
- simpl (left_shift_const_by t p v).
  change (_ <=? _)%Z with  (Zpower_nat 2 (S n) <=? Z.pos p)%Z.
  elim (Z.leb_spec).
  1:{
    rewrite Zpower_nat_Z.
    change 2%Z with (Z.of_nat 2%nat) at 1.
    rewrite <- Nat2Z.inj_pow.
    intros Hp.
    destruct (lt_dec _ _);[lia|].
    change (Vector.nth_order (flatten (|[@fill _ X (S n)  _ t]| tt)) ix1 = |[t]| tt).
    rewrite fill_correct.
    apply nth_replicate.
  }
  intros Hpn.
  transitivity (match p with
      | (p0~1)%positive => Vector.nth_order (flatten ((
          eq_rect (Vector (X * X) n)
            (fun x : Ty => Arrow x x)
            (left_shift_const_by (t &&& t) p0)
            (Vector X (S n))
            (eq_sym VectorPromote)) (left_shift1 t v))) ix1
      | (p0~0)%positive =>
          Vector.nth_order (flatten ((eq_rect (Vector (X * X) n)
            (fun x : Ty => Arrow x x)
            (left_shift_const_by (t &&& t) p0)
            (Vector X (S n))
            (eq_sym VectorPromote)) v)) ix1
      | 1%positive => Vector.nth_order (flatten (left_shift1 t v)) ix1
      end);
  [destruct p; reflexivity|].
  assert (Hcast : forall (f : Arrow (Vector (X*X) n) (Vector (X*X) n)),
    (eq_rect _ (fun x : Ty => Arrow x x) f _ (eq_sym VectorPromote) =
    (fun w => eq_rect _ tySem (f (eq_rect _ tySem w _ VectorPromote)) _ (eq_sym VectorPromote)))).
  1:{
    generalize (@VectorPromote X n).
    intros <-.
    reflexivity.
  }
  assert (ix_half : Nat.div2 i < 2^n).
  1:{
    rewrite Nat.div2_div.
    apply Nat.div_lt_upper_bound;[lia|].
    rewrite <- Nat.pow_succ_r'.
    assumption.
  }
  specialize (IHn (X*X) (t &&& t)).
  destruct p.
  + rewrite Hcast.
    set (w:= left_shift_const_by (t &&& t) p _).
    rewrite (nth_order_flatten_if _ _ ix_half).
    rewrite (IHn _ _ _ ix_half).
    elim lt_dec; rewrite Nat.div2_div.
    2:{
      intros Hip.
      elim lt_dec.
      1:{
        intros Hpi.
        exfalso.
        rewrite (Pos2Nat.inj_xI p) in Hpi.
        rewrite <- Nat.le_succ_l in Hpi.
        assert (Hpi0 : (i + (S (Pos.to_nat p)) * 2) / 2 <= 2 ^ (S n) / 2) by (apply Nat.div_le_mono;lia).
        rewrite Nat.div_add in Hpi0 by lia.
        change (2^(S n)) with (2*(2^n))%nat in Hpi0.
        rewrite Nat.mul_comm, Nat.div_mul in Hpi0 by lia.
        lia.
      }
      intros _.
      destruct (Nat.even i);reflexivity.
    }
    1:{
      intros ix_half2.
      assert (ix_half2a : 2 * (i / 2 + Pos.to_nat p) < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      assert (ix_half2b : 2 * (i / 2 + Pos.to_nat p) + 1 < 2 ^ (S n)) by (rewrite Nat.pow_succ_r';lia).
      erewrite (nth_order_flatten _ ix_half2 ix_half2a ix_half2b).
      rewrite <-eq_trans_rew_distr, eq_trans_sym_inv_r.
      cbn -[left_shift1 flatten Pos.to_nat Nat.ltb].
      rewrite left_shift1_correct.
      elim lt_dec.
      2:{
        intros Hip.
        assert (Hi : (i = 2^(S n) - 2*(Pos.to_nat p) - 1)%nat).
        1:{
          apply Nat.le_antisymm;[|cbn;lia].
          apply (Nat.mul_le_mono_l _ _ 2) in ix_half2.
          assert (Hlt := Nat.mul_succ_div_gt i 2).
          lia.
        }
        replace (Nat.even i) with (Nat.even (2^(S n) - 2*(Pos.to_nat p) - 1)) by congruence.
        rewrite !Nat.even_sub, Nat.even_pow, Nat.even_mul by lia.
        change (Vector.nth_order (Vector.tl (Vector.shiftin (t tt) (flatten v))) ix_half2b = t tt).
        revert ix_half2b.
        replace (2 * (i / 2 + Pos.to_nat p) + 1)%nat with (pred (2^(S n))).
        2:{
          rewrite Nat.mul_add_distr_l, Hi.
          change (2^ (S n)) with (2*(2^n))%nat.
          replace (2 * 2 ^ n - 2 * Pos.to_nat p - 1) with (((2 ^ n - Pos.to_nat p -1) * 2 + 1))%nat by lia.
          rewrite Nat.div_add_l by lia.
          change (1 / 2) with 0.
          lia.
        }
        intros ix_half2b.
        assert (ix_half2b' : S (Init.Nat.pred (2 ^ S n)) < S (2 ^ S n)) by lia.
        rewrite (VectorSpec.nth_order_tl _ _ _ _ _ ix_half2b').
        revert ix_half2b'.
        rewrite <- pow_succ.
        intros ix_half2b'.
        rewrite Vector.nth_order_last, Vector.shiftin_last.
        reflexivity.
      }
      assert (ix_half2a' : S (2 * (i / 2 + Pos.to_nat p)) < S (2 ^ S n)) by lia.
      assert (ix_half2b' : S (2 * (i / 2 + Pos.to_nat p) + 1) < S (2 ^ S n)) by lia.
      rewrite (VectorSpec.nth_order_tl _ _ _ _ _ ix_half2a'),
              (VectorSpec.nth_order_tl _ _ _ _ _ ix_half2b').
      intros ix2.
      transitivity (Vector.nth_order (Vector.shiftout (Vector.shiftin (t tt) (flatten v))) ix2);
      [|rewrite shiftout_shiftin;reflexivity].
      assert (ix2' :i + Pos.to_nat p~1 < S (2 ^ n + (2 ^ n + 0))) by lia.
      rewrite (nth_order_shiftout _ _ ix2').
      destruct (Nat.Even_Odd_dec i) as [Heven|Hodd].
      1:{
        rewrite <- Nat.even_spec in Heven.
        rewrite Heven.
        rewrite Nat.even_spec in Heven.
        destruct Heven as [i' Hi'].
        revert ix2'.
        replace (i + Pos.to_nat p~1)%nat with (S (2 * (i / 2 + Pos.to_nat p)))%nat;
        [intros; apply Vector.nth_order_ext|].
        rewrite Hi', (Nat.mul_comm _ i'), Nat.div_mul; lia.
      }
      1:{
        rewrite <- Nat.odd_spec in Hodd.
        rewrite <- Nat.negb_odd, Hodd.
        rewrite Nat.odd_spec in Hodd.
        destruct Hodd as [i' Hi'].
        revert ix2'.
        replace (i + Pos.to_nat p~1)%nat with (S (2 * (i / 2 + Pos.to_nat p) + 1))%nat;
        [intros; apply Vector.nth_order_ext|].
        replace (2 * i' + 1)%nat with (S (2 * i')) in Hi' by lia.
        rewrite Hi', <- Nat.div2_div, Nat.div2_succ_double.
        lia.
      }
    }
  + rewrite Hcast.
    set (w:= left_shift_const_by (t &&& t) p _).
    rewrite (nth_order_flatten_if _ _ ix_half).
    rewrite (IHn _ _ _ ix_half).
    elim lt_dec; rewrite Nat.div2_div.
    2:{
      intros Hip.
      elim lt_dec.
      1:{
        intros Hpi.
        elim Hip.
        rewrite (Pos2Nat.inj_xO p) in Hpi.
        change (2^(S n)) with (2*(2^n))%nat in Hpi.
        assert (Hle := Nat.mul_div_le i 2).
        cut (i/2 <= 2^n - (Pos.to_nat p + 1));[lia|].
        apply Nat.div_le_upper_bound;lia.
      }
      intros _.
      destruct (Nat.even i);reflexivity.
    }
    1:{
      intros ix_half2.
      elim lt_dec.
      2:{
        intros Hip.
        apply Nat.nlt_ge in Hip.
        rewrite (Pos2Nat.inj_xO p) in Hip.
        apply (Nat.div_le_mono _ _ 2) in Hip;[|lia].
        change (2^(S n)) with (2*(2^n))%nat in Hip.
        rewrite Nat.mul_comm, Nat.div_mul in Hip by lia.
        rewrite Nat.mul_comm, Nat.div_add in Hip by lia.
        lia.
      }
      assert (ix_half2a : 2 * (i / 2 + Pos.to_nat p) < 2 ^ S n) by (rewrite Nat.pow_succ_r';lia).
      assert (ix_half2b : 2 * (i / 2 + Pos.to_nat p) + 1 < 2 ^ S n) by (rewrite Nat.pow_succ_r';lia).
      erewrite (nth_order_flatten _ _ ix_half2a ix_half2b).
      rewrite <-eq_trans_rew_distr, eq_trans_sym_inv_r.
      cbn -[flatten Pos.to_nat Nat.ltb].
      intros ix2.
      destruct (Nat.Even_Odd_dec i) as [Heven|Hodd].
      1:{
        rewrite <- Nat.even_spec in Heven.
        rewrite Heven.
        rewrite Nat.even_spec in Heven.
        destruct Heven as [i' Hi'].
        revert ix2.
        replace (i + Pos.to_nat p~0)%nat with (2 * (i / 2 + Pos.to_nat p))%nat;
        [intros; apply Vector.nth_order_ext|].
        rewrite Hi', <- Nat.div2_div, Nat.div2_double.
        lia.
      }
      1:{
        rewrite <- Nat.odd_spec in Hodd.
        rewrite <- Nat.negb_odd, Hodd.
        rewrite Nat.odd_spec in Hodd.
        destruct Hodd as [i' Hi'].
        revert ix2.
        replace (i + Pos.to_nat p~0)%nat with (2 * (i / 2 + Pos.to_nat p) + 1)%nat;
        [intros; apply Vector.nth_order_ext|].
        replace (2 * i' + 1)%nat with (S (2 * i')) in Hi' by lia.
        rewrite Hi', <- Nat.div2_div, Nat.div2_succ_double.
        lia.
      }
    }
  + rewrite left_shift1_correct.
    assert (ix1' : S i < S (2 ^ S n)) by lia.
    rewrite (Vector.nth_order_tl _ _ _ _ _ ix1').
    elim lt_dec; intros Hi.
    * transitivity (VectorDef.nth_order (Vector.shiftout (Vector.shiftin (t tt) (flatten v))) Hi).
      1:{
       revert Hi.
       replace (i + Pos.to_nat 1)%nat with (S i) by lia.
       intros Hi.
       rewrite (nth_order_shiftout _ _ ix1').
       reflexivity.
      }
      f_equal.
      apply shiftout_shiftin.
    * revert ix1'.
      replace (S i) with (2^S n) by lia.
      intros ix1'.
      rewrite Vector.nth_order_last.
      apply Vector.shiftin_last.
Qed.

Lemma nth_Word {n i} (x : Word n) (ix : i < 2^n) :
  toBool (Vector.nth_order (flatten x) ix) = Z.testbit (toZ x) (2^(Z.of_nat n) - 1 - Z.of_nat i).
Proof.
revert i x ix.
induction n.
- intros [|i];[|cbn;lia].
  intros [[] | []];reflexivity.
- intros i [x0 x1].
  rewrite <- (Nat2Z.inj_pow 2) in *.
  simpl.
  generalize (mul_2_r (2 ^ n)); simpl.
  intros -> ix; simpl.
  destruct (lt_dec i (2^n)) as [ix'|Hi].
  + rewrite (nth_order_append_front _ _ _ ix'), IHn, testbitToZHi;
    rewrite two_power_nat_equiv, <- (Nat2Z.inj_pow 2);[f_equal|];lia.
  + assert (ix' : i - 2^n < 2^n) by lia.
    revert ix.
    replace i with (2^n + (i - 2^n))%nat by lia.
    intros ix.
    rewrite (nth_order_append_back _ _ _ ix'), IHn, testbitToZLo;[f_equal;lia|].
    rewrite two_power_nat_equiv, <- (Nat2Z.inj_pow 2).
    lia.
Qed.

Lemma shift_const_correct n z (x : Word n) i (Hi : (0 <= i < two_power_nat n)%Z) :
  Z.testbit (toZ (|[shift_const (-z)]| x : tySem (Word n))) i = Z.testbit (toZ x) (i + z)%Z.
Proof.
assert (Htwo : forall n, two_power_nat n = Z.of_nat (2 ^ n)).
1:{
  intros.
  rewrite two_power_nat_equiv, <- (Nat2Z.inj_pow 2).
  reflexivity.
}
rewrite Htwo in *.
assert (ix : 2^n - 1 - Z.to_nat i < 2^n) by lia.
destruct z;cbn.
- f_equal.
  lia.
- replace i with (Z.of_nat (2 ^  n - 1 - (2 ^ n - 1 - Z.to_nat i))) at 1 by lia.
  rewrite Nat2Z.inj_sub, (Nat2Z.inj_sub _ 1), Nat2Z.inj_pow by lia.
  rewrite <- (nth_Word _ ix).
  assert (ix2 : (2 ^ n - 1 - Z.to_nat i) - Pos.to_nat p < 2 ^ n) by lia.
  rewrite (right_shift_const_by_correct _ ix2).
  elim Nat.ltb_spec; intros Hp.
  + rewrite toZ_mod.
    rewrite two_power_nat_equiv, Z.mod_pow2_bits_high;[reflexivity|].
    rewrite bitSize_Word, two_power_nat_equiv, <- (Nat2Z.inj_pow 2). lia.
  + rewrite nth_Word.
    f_equal.
    rewrite <- (Nat2Z.inj_pow 2).
    lia.
- replace i with (Z.of_nat (2 ^  n - 1 - (2 ^ n - 1 - Z.to_nat i))) at 1 by lia.
  rewrite Nat2Z.inj_sub, (Nat2Z.inj_sub _ 1), Nat2Z.inj_pow by lia.
  rewrite <- (nth_Word _ ix).
  rewrite left_shift_const_by_correct.
  elim lt_dec; intros Hp.
  + rewrite nth_Word.
    f_equal.
    rewrite <- (Nat2Z.inj_pow 2).
    lia.
  + rewrite Z.testbit_neg_r;[reflexivity|].
    lia.
Qed.

Lemma left_rotate1_correct {X n v} :
  @flatten X n (|[ left_rotate1 ]| v) = Vector.tl (Vector.shiftin (pow_hd (flatten v)) (flatten v)).
Proof.
unfold left_rotate1.
etransitivity;[cbn|reflexivity].
change (flatten (snd _)) with (snd (map_snd flatten (|[full_left_shift1]| (v, |[leftmost]| v)))).
rewrite full_left_shift1_correct, leftmost_correct.
reflexivity.
Qed.

Lemma right_rotate1_correct {X n v} :
  @flatten X n (|[ right_rotate1 ]| v) = Vector.shiftout (pow_last (flatten v) :: (flatten v)).
Proof.
unfold right_rotate1.
etransitivity;[cbn|reflexivity].
change (flatten (fst _)) with (fst (map_fst flatten (|[full_right_shift1]| (|[rightmost]| v, v)))).
rewrite full_right_shift1_correct, rightmost_correct.
reflexivity.
Qed.

Lemma foldr_comp_correct {X} l v : |[foldr_comp l]| v = fold_right (@comp X X X CoreFunSem) |[iden]| l v.
Proof.
revert v.
induction l;[reflexivity|].
destruct l as [|b l];[reflexivity|].
- intros v. 
  change (foldr_comp (a :: b :: l) v) with (foldr_comp (b :: l) (a v)).
  apply IHl.
Qed.

Lemma rotate_const_correct {X n i j} z (v : Vector X n) (ix : i < 2^n) (jx : j < 2^n) :
  eqm (2^Z.of_nat n) (Z.of_nat j) (Z.of_nat i + z) ->
  Vector.nth_order (flatten (|[rotate_const z]| v)) ix = Vector.nth_order (flatten v) jx.
Proof.
rewrite <- (Nat2Z.inj_pow 2).
unfold rotate_const.
rewrite foldr_comp_correct.
intros Hij.
generalize jx.
rewrite <-(Nat2Z.id j), <-(Z.mod_small (Z.of_nat j) (Z.of_nat (2^n))), Hij by lia.
clear j jx Hij.
intros jx.
assert (ixmod : forall n a, Z.to_nat (a  mod Z.of_nat (2 ^ n)) < 2 ^ n).
1:{
  clear.
  intros n a.
  assert (Hmod := Z.mod_pos_bound a (Z.of_nat (2^n))).
  rewrite pow_succ in Hmod at 1.
  lia.
}
transitivity (Vector.nth_order (flatten v) (ixmod _ (Z.of_nat i + z)))%Z;[|apply Vector.nth_order_ext].
clear jx.
revert X i z v ix.
induction n;
[intros X [|i] z;simpl;[generalize (ixmod 0 z);simpl;rewrite Z.mod_1_r;intros;apply Vector.nth_order_ext|lia] |].
intros X i z v ix.
assert (Hcast : forall (l : list (Arrow (Vector (X*X) n) (Vector (X*X) n))) w,
  fold_right comp iden (eq_rect _ (fun x : Ty => list (Arrow x x)) l _ (eq_sym VectorPromote)) w =
  eq_rect _ tySem (fold_right comp iden l (eq_rect _ tySem w _ VectorPromote)) _ (eq_sym VectorPromote)).
1:{
  generalize (@VectorPromote X n).
  intros <-.
  reflexivity.
}
assert (ix_half : Nat.div2 i < 2^n).
1:{
  rewrite Nat.div2_div.
  apply Nat.div_lt_upper_bound;[lia|].
  rewrite <- Nat.pow_succ_r'.
  assumption.
}
assert (Heven : forall a, Nat.even a = Z.even (Z.of_nat a)).
1:{
  clear.
  intros a.
  induction a as [a IH] using lt_wf_ind.
  destruct a as [| [|a]]; try reflexivity.
  simpl (Nat.even _).
  rewrite IH;[|lia].
  symmetry.
  etransitivity;[|apply Z.even_succ_succ].
  f_equal.
  lia.
}
generalize (ixmod (S n) (Z.of_nat i + z)%Z).
change (2^S n) with (2 * 2^n)%nat.
rewrite Nat2Z.inj_mul.
change (Z.of_nat 2) with 2%Z.
intros jx.
simpl (rotate_const_list z).
case_eq (Z.even z);[|case_eq (Z.even (z/2))].
- rewrite Z.even_spec.
  intros [z' ->].
  replace (2 * z' / 2)%Z with z' by (rewrite Z.mul_comm, Z_div_mult by lia;reflexivity).
  rewrite Hcast, (nth_order_flatten_if _ _ ix_half).
  rewrite (IHn _ _ _ _ ix_half).
  generalize (ixmod n (Z.of_nat (Nat.div2 i) + z')%Z).
  set (j := Z.to_nat
       ((Z.of_nat i + 2 * z') mod (2 * Z.of_nat (2 ^ n)))) in *.
  replace (Z.to_nat ((Z.of_nat (Nat.div2 i) + z') mod Z.of_nat (2 ^ n))) 
     with (Nat.div2 j).
  2:{
    symmetry.
    rewrite !Nat.div2_div, Nat2Z.inj_div, <- Z_div_plus, <-Zaux.Zdiv_mod_mult, Z.mul_comm by lia.
    rewrite Z2Nat.inj_div by (assert (Hmod := Z.mod_pos_bound (Z.of_nat i + Z.of_nat 2 * z') (Z.of_nat 2 * Z.of_nat (2 ^ n)));lia). 
    reflexivity.
  }
  intros jx_half.
  replace (Nat.even i) with (Nat.even j);
  [rewrite <-(nth_order_flatten_if _ jx jx_half), <-eq_trans_rew_distr, eq_trans_sym_inv_r;
   apply Vector.nth_order_ext|].
  rewrite !Heven.
  symmetry.
  apply Bool.eqb_true_iff.
  rewrite <- Z.even_sub.
  symmetry.
  change ((Z.even 2 || Z.even z') = Z.even (Z.of_nat i - Z.of_nat j))%bool.
  apply Bool.eqb_true_iff.
  rewrite <- Z.even_mul, <- Z.even_add, Zeven_mod.
  apply Zeq_is_eq_bool.
  replace (_ + _)%Z with ((Z.of_nat i + 2 * z') - Z.of_nat j)%Z by lia.
  apply Z.mod_divide;[lia|].
  etransitivity;[apply (Z.divide_factor_l 2 (Z.of_nat (2^n)))|].
  apply Z.mod_divide;[lia|].
  unfold j.
  rewrite Z2Nat.id by (assert (Hmod := Z.mod_pos_bound (Z.of_nat i + 2 * z') (2 * Z.of_nat (2^n)));lia).
  rewrite Zminus_mod_idemp_r, Z.sub_diag.
  reflexivity.
- rewrite Z.even_spec, <-Z.negb_odd, Bool.negb_false_iff, Z.odd_spec.
  intros Hz' [z' ->].
  replace ((2 * z' + 1) / 2)%Z with z' in * by (rewrite Z.mul_comm, Z.div_add_l, Z.add_0_r by lia;reflexivity).
  destruct Hz' as [z ->].
  set (l := eq_rect _ _ _ _ _).
  change (fold_right comp H (_ :: l) v) with (fold_right comp H l (|[left_rotate1]| v)).
  rewrite Hcast, (nth_order_flatten_if _ _ ix_half), (IHn _ _ _ _ ix_half); clear l.
  generalize (ixmod n (Z.of_nat (Nat.div2 i) + 2 * z)%Z).  
  rewrite Nat.div2_div, Nat2Z.inj_div, <- Z_div_plus, <-Zaux.Zdiv_mod_mult, Z.mul_comm by lia.
  change (Z.of_nat 2) with 2%Z.
  set (k:= (Z.of_nat i + 2 * (2 * z))%Z).
  assert (Hmod := Z.mod_pos_bound k (2 * Z.of_nat (2^n))).
  rewrite Z2Nat.inj_div by lia.
  rewrite <-Nat.div2_div.
  revert jx.
  rewrite Z.add_assoc.
  set (j := Z.to_nat (k mod (2 * Z.of_nat (2 ^ n)))).
  intros jx jx_half.
  assert (jx' : j < 2 ^ (S n)) by (cbn;lia).
  replace (Nat.even i) with (Nat.even j).
  * rewrite <-(nth_order_flatten_if _ jx'), <-eq_trans_rew_distr, eq_trans_sym_inv_r;
    simpl (eq_rect _ _ _ _ eq_refl).
    rewrite left_rotate1_correct.
    assert (jx'S : S j < S (2^S n)) by lia.
    rewrite (VectorSpec.nth_order_tl _ _ _ _ _ jx'S).
    elim (lt_dec (S j) (2 ^ S n)).
    + intros jx'S'.
      rewrite <- (nth_order_shiftout _ jx'S'), shiftout_shiftin.
      revert jx.
      fold k.
      rewrite <- Zplus_mod_idemp_l, Z.mod_small;
      [rewrite Z2Nat.inj_succ;[apply Vector.nth_order_ext|lia] |].
      unfold j in jx'S'.
      rewrite <- Z2Nat.inj_succ in jx'S' by lia.
      change (2^S n) with (2 * 2^n)%nat in *.
      lia.
    + intros Hj.
      revert jx'S.
      replace (S j) with (2 ^ S n) by lia.
      intros jx'S.
      rewrite Vector.nth_order_last, Vector.shiftin_last.
      revert jx.
      rewrite <-Zplus_mod_idemp_l, <-(Z2Nat.id (k mod (2 * Z.of_nat (2 ^ n)))) by lia.
      fold (Z.succ (Z.of_nat (Z.to_nat (k mod (2 * Z.of_nat (2 ^ n)))))) j.
      rewrite <- Nat2Z.inj_succ.
      replace (S j) with (2 ^ S n) by lia.
      change (2^S n) with (2 * 2^n)%nat.
      rewrite Nat2Z.inj_mul, Z_mod_same_full.
      change (2 * 2^n)%nat with (2^S n).
      generalize (flatten v).
      unfold pow_hd.
      generalize (pow_succ (S n));intros -> w wx.
      symmetry.
      apply Vector.nth_order_hd.
  * rewrite !Heven, !Zeven_mod.
    change 2%Z with (2^1)%Z.
    unfold j.
    rewrite Z2Nat.id, Nat2Z.inj_pow, <- Z.pow_succ_r, <- !Z.land_ones, <- Z.land_assoc by lia.
    rewrite Z.land_ones, Z.ones_mod_pow2, !Z.land_ones, <-!Zeven_mod by lia.
    unfold k.
    rewrite Z.even_add, Z.even_mul.
    change (_ || _)%bool with (Z.even 0).
    rewrite <-Z.even_add.
    f_equal.
    lia.
- rewrite <-!Z.negb_odd, !Bool.negb_false_iff, !Z.odd_spec.
  intros Hz' [z' ->].
  replace ((2 * z' + 1) / 2)%Z with z' in * by (rewrite Z.mul_comm, Z.div_add_l, Z.add_0_r by lia;reflexivity).
  destruct Hz' as [z ->].
  replace (2 * (2 * z + 1) + 1 + 1)%Z with ((2*(z + 1))*2)%Z by lia.
  rewrite Z_div_mult by lia.
  set (l := eq_rect _ _ _ _ _).
  change (fold_right comp H (_ :: l) v) with (fold_right comp H l (|[right_rotate1]| v)).
  rewrite Hcast, (nth_order_flatten_if _ _ ix_half), (IHn _ _ _ _ ix_half); clear l.
  generalize (ixmod n (Z.of_nat (Nat.div2 i) + 2 * (z + 1))%Z).  
  rewrite Nat.div2_div, Nat2Z.inj_div, <- Z_div_plus, <-Zaux.Zdiv_mod_mult, Z.mul_comm by lia.
  change (Z.of_nat 2) with 2%Z.
  set (k:= (Z.of_nat i + 2 * (2 * (z + 1)))%Z).
  assert (Hmod := Z.mod_pos_bound k (2 * Z.of_nat (2^n))).
  rewrite Z2Nat.inj_div by lia.
  rewrite <-Nat.div2_div.
  revert jx.
  replace (Z.of_nat i + (2 * (2 * z + 1) + 1))%Z with (k - 1)%Z by lia.
  set (j := Z.to_nat (k mod (2 * Z.of_nat (2 ^ n)))).
  intros jx jx_half.
  assert (jx' : j < 2 ^ (S n)) by (cbn;lia).
  replace (Nat.even i) with (Nat.even j).
  * rewrite <-(nth_order_flatten_if _ jx'), <-eq_trans_rew_distr, eq_trans_sym_inv_r;
    simpl (eq_rect _ _ _ _ eq_refl).
    rewrite right_rotate1_correct.
    assert (jx'S : j < S (2^S n)) by lia.
    rewrite (nth_order_shiftout _ _ jx'S).
    elim (Nat.eq_dec j 0).
    + intros Hj.
      revert jx'S.
      rewrite Hj.
      intros jx'S.
      rewrite Vector.nth_order_hd.
      revert jx.
      rewrite <-Zplus_mod_idemp_l, <-(Z2Nat.id (k mod (2 * Z.of_nat (2 ^ n)))) by lia.
      fold j.
      rewrite Hj.
      simpl (Z.of_nat 0).
      rewrite <- (Z_mod_same_full (2 * Z.of_nat (2 ^ n))), Zplus_mod_idemp_l, Z.mod_small by lia.
      replace (_ * _)%Z with (Z.of_nat (2 * 2 ^ n)) by lia.
      change (2 * 2^n)%nat with (2^S n).
      generalize (flatten v).
      unfold pow_last.
      generalize (pow_succ (S n));intros -> w.
      replace (Z.to_nat _) with (Init.Nat.pred (2 ^ S n)) by lia.
      intros wx.
      symmetry.
      apply Vector.nth_order_last.
    + intros Hj.
      revert jx'S.
      replace j with (S (pred j)) by lia.
      intros jx'S.
      symmetry.
      change (flatten v) with (Vector.tl (pow_last (flatten v) :: flatten v)) at 1.
      revert jx.
      rewrite <-Zplus_mod_idemp_l, <-(Z2Nat.id (k mod (2 * Z.of_nat (2 ^ n)))) by lia.
      fold j.
      replace (Z.of_nat j + - (1))%Z with (Z.of_nat (pred j)) by lia.
      rewrite Z.mod_small, Nat2Z.id by lia.
      change (2 * 2^n)%nat with (2^S n).
      intros jx.
      apply Vector.nth_order_tl.
  * rewrite !Heven, !Zeven_mod.
    change 2%Z with (2^1)%Z.
    unfold j.
    rewrite Z2Nat.id, Nat2Z.inj_pow, <- Z.pow_succ_r, <- !Z.land_ones, <- Z.land_assoc by lia.
    rewrite Z.land_ones, Z.ones_mod_pow2, !Z.land_ones, <-!Zeven_mod by lia.
    unfold k.
    rewrite Z.even_add, Z.even_mul.
    change (_ || _)%bool with (Z.even 0).
    rewrite <-Z.even_add.
    f_equal.
    lia.
Qed.

Lemma rotate_const_correct_word n z (x : Word n) i (Hi : (0 <= i < two_power_nat n)%Z) :
  Z.testbit (toZ (|[rotate_const (-z)]| x : tySem (Word n))) i = Z.testbit (toZ x) (Zmod (i + z) (two_power_nat n))%Z.
Proof.
assert (Htwo : forall n, two_power_nat n = Z.of_nat (2 ^ n)).
1:{
  intros.
  rewrite two_power_nat_equiv, <- (Nat2Z.inj_pow 2).
  reflexivity.
}
rewrite Htwo in *.
set (i0 := Z.to_nat (Z.of_nat (2^n) - 1 - i)).
assert (ix : i0 < 2^n) by lia.
replace i with (Z.of_nat (2 ^ n) - 1 - Z.of_nat i0)%Z at 1 by lia.
rewrite Nat2Z.inj_pow by lia.
rewrite <- (nth_Word _ ix).
set (j0 := Z.to_nat ((Z.of_nat (2^n) - 1 - i - z) mod (2^Z.of_nat n))).
destruct (Z.mod_pos_bound (Z.of_nat (2 ^ n) - 1 - i - z) (2 ^ Z.of_nat n)) as [Hj0 Hj1];[lia|].
assert (jx : j0 < 2^n).
1:{
  rewrite <- (Nat2Z.id (2^n)).
  rewrite Nat2Z.inj_pow by lia.
  apply Z2Nat.inj_lt;lia.
}
rewrite (rotate_const_correct _ _ _ jx).
2:{
  unfold eqm, i0, j0.
  rewrite !Z2Nat.id, Zmod_mod by lia.
  reflexivity.
}
rewrite nth_Word.
f_equal.
rewrite <-(Z.mod_small (2 ^ Z.of_nat n - 1 - Z.of_nat j0)%Z (2 ^ Z.of_nat n)) by lia.
unfold j0.
rewrite Z2Nat.id, Nat2Z.inj_pow, Zminus_mod_idemp_r by lia.
f_equal.
lia.
Qed.

End Specifications.

Lemma zero_Parametric {n} {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ (Word n) zero zero.
Proof.
induction n; cbn; auto with parametricity.
Qed.
Hint Immediate zero_Parametric : parametricity.

Lemma adderBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ adderBit adderBit.
Proof.
unfold adderBit.
auto with parametricity.
Qed.
Hint Immediate adderBit_Parametric : parametricity.

Lemma fullAdderBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ fullAdderBit fullAdderBit.
Proof.
unfold fullAdderBit.
auto 10 with parametricity.
Qed.
Hint Immediate fullAdderBit_Parametric : parametricity.

Lemma buildFullAdder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ (Bit * W) t1 t2 -> R _ _ (buildFullAdder t1) (buildFullAdder t2).
Proof.
unfold buildFullAdder.
auto 10 with parametricity.
Qed.
Hint Resolve buildFullAdder_Parametric : parametricity.

Lemma fullAdder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ fullAdder (@fullAdder n _).
Proof.
induction n; cbn; auto with parametricity.
Qed.
Hint Immediate fullAdder_Parametric : parametricity.

Lemma adder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ adder (@adder n _).
Proof.
induction n; cbn; auto with parametricity.
Qed.
Hint Immediate adder_Parametric : parametricity.

Lemma fullMultiplierBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ fullMultiplierBit fullMultiplierBit.
Proof.
unfold fullMultiplierBit.
auto with parametricity.
Qed.
Hint Immediate fullMultiplierBit_Parametric : parametricity.

Lemma buildFullMultiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ (W * W) t1 t2 -> R _ _ (buildFullMultiplier t1) (buildFullMultiplier t2).
Proof.
unfold buildFullMultiplier.
auto 15 with parametricity.
Qed.
Hint Resolve buildFullMultiplier_Parametric : parametricity.

Lemma fullMultiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ (Word n * Word n) fullMultiplier (@fullMultiplier n _).
Proof.
induction n; cbn; auto with parametricity.
Qed.
Hint Immediate fullMultiplier_Parametric : parametricity.

Lemma multiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ multiplier (@multiplier n _).
Proof.
unfold multiplier.
cbn; auto with parametricity.
Qed.
Hint Immediate multiplier_Parametric : parametricity.

Lemma build_fill_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {C X} t1 t2 : R C X t1 t2 -> R _ _ (build_fill t1) (build_fill t2).
Proof.
unfold build_fill.
auto 10 with parametricity.
Qed.
Hint Resolve build_fill_Parametric : parametricity.

Lemma fill_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {C X n} op1 op2 : R _ _ op1 op2 -> R _ _ (fill op1) (@fill C X n _ op2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve fill_Parametric : parametricity.

Lemma buildBitwiseTri_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ W t1 t2 -> R _ _ (buildBitwiseTri t1) (buildBitwiseTri t2).
Proof.
unfold buildBitwiseTri.
auto 10 with parametricity.
Qed.
Hint Resolve buildBitwiseTri_Parametric : parametricity.

Lemma bitwiseTri_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} op1 op2 : R _ _ op1 op2 -> R _ _ (bitwiseTri op1) (@bitwiseTri X n _ op2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve bitwiseTri_Parametric : parametricity.

Lemma build_leftmost_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {V X} t1 t2 : R V X t1 t2 -> R _ _ (build_leftmost t1) (build_leftmost t2).
Proof.
unfold build_leftmost.
auto 10 with parametricity.
Qed.
Hint Resolve build_leftmost_Parametric : parametricity.

Lemma leftmost_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ leftmost (@leftmost X n term2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve leftmost_Parametric : parametricity.

Lemma build_rightmost_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {V X} t1 t2 : R V X t1 t2 -> R _ _ (build_rightmost t1) (build_rightmost t2).
Proof.
unfold build_rightmost.
auto 10 with parametricity.
Qed.
Hint Resolve build_rightmost_Parametric : parametricity.

Lemma rightmost_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ rightmost (@rightmost X n term2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve rightmost_Parametric : parametricity.

Lemma build_full_left_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X W} t1 t2 : R (W * X) (X * W) t1 t2 -> R _ _ (build_full_left_shift1 t1) (build_full_left_shift1 t2).
Proof.
unfold build_full_left_shift1.
auto 10 with parametricity.
Qed.
Hint Resolve build_full_left_shift1_Parametric : parametricity.

Lemma full_left_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ full_left_shift1 (@full_left_shift1 X n term2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve full_left_shift1_Parametric : parametricity.

Lemma build_full_right_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X W} t1 t2 : R (W * X) (X * W) t1 t2 -> R _ _ (build_full_right_shift1 t1) (build_full_right_shift1 t2).
Proof.
unfold build_full_right_shift1.
auto 10 with parametricity.
Qed.
Hint Resolve build_full_right_shift1_Parametric : parametricity.

Lemma full_right_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ full_right_shift1 (@full_right_shift1 X n term2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve full_right_shift1_Parametric : parametricity.

Lemma left_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} t1 t2 : R _ _ t1 t2 -> R _ _ (left_shift1 t1) (@left_shift1 X n term2 t2).
Proof.
unfold left_shift1.
auto 10 with parametricity.
Qed.
Hint Resolve left_shift1_Parametric : parametricity.

Lemma left_shift_const_by_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} t1 t2 p : R _ _ t1 t2 -> R _ _ (left_shift_const_by t1 p) (@left_shift_const_by X n term2 t2 p).
Proof.
revert X t1 t2 p.
induction n; intros X t1 t2 p Ht; simpl; destruct (_ <=? _)%Z; auto with parametricity.
change (Vector X n * Vector X n) with (Vector X (S n)).
destruct p;
try apply comp_Parametric;auto 10 with parametricity;
destruct (@eq_sym Ty (Vector X (S n)) (Vector (X * X) n) (@VectorPromote X n));
apply IHn;auto 10 with parametricity.
Qed.
Hint Resolve left_shift_const_by_Parametric : parametricity.

Lemma right_shift1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} t1 t2 : R _ _ t1 t2 -> R _ _ (right_shift1 t1) (@right_shift1 X n term2 t2).
Proof.
unfold right_shift1.
auto 10 with parametricity.
Qed.
Hint Resolve right_shift1_Parametric : parametricity.

Lemma right_shift_const_by_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} t1 t2 p : R _ _ t1 t2 -> R _ _ (right_shift_const_by t1 p) (@right_shift_const_by X n term2 t2 p).
Proof.
revert X t1 t2 p.
induction n; intros X t1 t2 p Ht; simpl; destruct (_ <=? _)%Z; auto with parametricity.
change (Vector X n * Vector X n) with (Vector X (S n)).
destruct p;
try apply comp_Parametric;auto 10 with parametricity;
destruct (@eq_sym Ty (Vector X (S n)) (Vector (X * X) n) (@VectorPromote X n));
apply IHn;auto 10 with parametricity.
Qed.
Hint Resolve right_shift_const_by_Parametric : parametricity.

Lemma shift_const_by_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} t1 t2 z : R _ _ t1 t2 -> R _ _ (shift_const_by t1 z) (@shift_const_by X n term2 t2 z).
Proof.
destruct z;simpl;auto 10 with parametricity.
Qed.
Hint Resolve shift_const_by_Parametric : parametricity.

Lemma shift_const_Parametric {n} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word n) (shift_const z) (shift_const z).
Proof.
unfold shift_const.
apply shift_const_by_Parametric.
auto 10 with parametricity.
Qed.
Hint Immediate shift_const_Parametric : parametricity.

Lemma left_rotate1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ left_rotate1 (@left_rotate1 X n term2).
Proof.
unfold left_rotate1.
auto 10 with parametricity.
Qed.
Hint Resolve left_rotate1_Parametric : parametricity.

Lemma right_rotate1_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} : R _ _ right_rotate1 (@right_rotate1 X n term2).
Proof.
unfold right_rotate1.
auto 10 with parametricity.
Qed.
Hint Resolve right_rotate1_Parametric : parametricity.

Lemma rotate_const_list_length {term1 term2 : Core.Algebra}
  {X n} z : length (@rotate_const_list X n term1 z) = length (@rotate_const_list X n term2 z).
Proof.
revert X z.
induction n; intros X z; simpl.
- reflexivity.
- repeat destruct (Z.even _);simpl;change (Vector X n * Vector X n) with (Vector X (S n));
  destruct (@eq_sym Ty (Vector X (S n)) (Vector (X * X) n) (@VectorPromote X n)); simpl;
  firstorder.
Qed.

Lemma rotate_const_list_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X n} z i : R _ _ (nth i (@rotate_const_list X n term1 z) iden) (nth i (@rotate_const_list X n term2 z) iden).
Proof.
revert X z i.
induction n; intros X z i; simpl.
- destruct i; auto with parametricity.
- repeat destruct (Z.even _);[|destruct i|destruct i];simpl;change (Vector X n * Vector X n) with (Vector X (S n));auto 10 with parametricity;
  destruct (@eq_sym Ty (Vector X (S n)) (Vector (X * X) n) (@VectorPromote X n));apply IHn.
Qed.

Lemma foldr_comp_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {X} l1 l2 : length l1 = length l2 -> (forall i, R X X (nth i l1 iden) (nth i l2 iden)) -> R _ _ (foldr_comp l1) (foldr_comp l2).
Proof.
revert l2.
induction l1; intros [|x l2]; simpl; try discriminate.
- auto with parametricity.
- intros H.
  inversion H.
  intros H0.
  assert (H00 := H0 0).
  destruct l1; destruct l2; try discriminate.
  + assumption.
  + apply comp_Parametric;[assumption|].
    apply IHl1;[assumption|].
    intros i.
    apply (H0 (S i)).
Qed.

Lemma rotate_const_Parametric {n} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word n) (rotate_const z) (rotate_const z).
Proof.
unfold rotate_const.
apply foldr_comp_Parametric.
- apply rotate_const_list_length.
- apply rotate_const_list_Parametric.
Qed.
Hint Immediate rotate_const_Parametric : parametricity.
