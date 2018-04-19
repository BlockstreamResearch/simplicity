Require Import Logic.Eqdep_dec.
Require Import Coq.Strings.String.
Require Import List.
Require BinInt.

Require compcert.lib.Integers.
Require sha.SHA256.
Require Import sha.functional_prog.
Require Import sha.general_lemmas.
Global Unset Asymmetric Patterns. (* the VST library does a Global Set so we must unset it. *)

Set Implicit Arguments.

Record Hash256 : Set := hash256 
 {hash256_reg :> SHA256.registers
 ;hash256_len : length hash256_reg = 8
 }.

Definition Hash256_to_Zlist (x : Hash256) := intlist_to_Zlist (hash256_reg x).

(* The normalizeInt and normalizeHash functions are extensionally the idenity
 * function.  Operationally they work by replacing the internal proof
 * obligations of their inputs with canonical versions of those proofs.  When
 * evaluated in the empty context, this has the effect of pruning away any
 * opaque proof terms.  This will also work whenever the internal data values
 * of the inputs are independent of the context.
 *)
Definition normalizeInt (x : Integers.Int.int) : Integers.Int.int.
set (v := Integers.Int.intval x).
exists v.
assert (Hv := Integers.Int.intrange x).
fold v in Hv.
unfold BinInt.Z.lt in *.
split;
[destruct (BinInt.Z.compare (-1) v)
|destruct (BinInt.Z.compare v Integers.Int.modulus)
]; solve [reflexivity|destruct Hv; discriminate].
Defined.

Lemma normalizeInt_correct x : normalizeInt x = x.
Proof.
destruct x as [v [Hv0 Hv1]].
unfold normalizeInt.
unfold BinInt.Z.lt in *.
cbn -[BinInt.Z.compare].
repeat f_equal; apply UIP_dec; decide equality.
Qed.

Definition normalizeHash (x : Hash256) : Hash256.
exists (map normalizeInt (hash256_reg x)).
assert (Heq := hash256_len x).
rewrite <- (map_length normalizeInt) in Heq.
destruct (length (map normalizeInt (hash256_reg x))) as [|n]; try discriminate.
repeat (destruct n as [|n]; try reflexivity; try discriminate).
Defined.

Lemma normalizeHash_correct x : normalizeHash x = x.
Proof.
destruct x as [x Hx].
unfold normalizeHash;cbn.
set (Heq:= eq_ind_r _ _ _).
generalize Heq; clear Heq.
replace (map normalizeInt x) with x
 by (clear; induction x; cbn;[|rewrite normalizeInt_correct, <- IHx]; auto).
intros Heq.
f_equal.
apply UIP_dec; decide equality.
Qed.

Definition stringHash (x : string) : Hash256 :=
 hash256 (process_msg SHA256.init_registers (generate_and_pad_alt (SHA256.str_to_Z x)))
  (length_process_msg _).

Definition compress (iv h1 h2 : Hash256) : Hash256 :=
  hash256 (process_block iv (List.rev (hash256_reg h1 ++ hash256_reg h2)))
   (length_process_block _ _ (hash256_len iv)).

Definition compress_half (iv h: Hash256) : Hash256 :=
  hash256 (process_block iv (List.rev (hash256_reg h) ++ repeat Integers.Int.zero 8))
   (length_process_block _ _ (hash256_len iv)).