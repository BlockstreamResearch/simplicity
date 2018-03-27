Require Import Simplicity.Ty.
Require Import Util.Monad.
Require Import Util.Option.

Variable Hash256 : Set (* TODO: Fill in suitable type for 256-bit word *).

Local Open Scope monad_scope.

Inductive Term : Ty -> Ty -> Set :=
| iden : forall {A}, Term A A
| comp : forall {A B C}, Term A B -> Term B C -> Term A C
| unit : forall {A}, Term A Unit
| injl : forall {A B C}, Term A B -> Term A (Sum B C)
| injr : forall {A B C}, Term A C -> Term A (Sum B C)
| case : forall {A B C D},
    Term (Prod A C) D -> Term (Prod B C) D -> Term (Prod (Sum A B) C) D
| pair : forall {A B C}, Term A B -> Term A C -> Term A (Prod B C)
| take : forall {A B C}, Term A C -> Term (Prod A B) C
| drop : forall {A B C}, Term B C -> Term (Prod A B) C
| assertl : forall {A B C D},
    Term (Prod A C) D -> Hash256 -> Term (Prod (Sum A B) C) D
| assertr : forall {A B C D},
    Hash256 -> Term (Prod B C) D -> Term (Prod (Sum A B) C) D
| fail : forall {A B}, Hash256 * Hash256 -> Term A B.

Fixpoint eval {A B} (x : Term A B) : tySem A -> option (tySem B) :=
match x in Term A B return tySem A -> option (tySem B) with
| iden => fun a => eta a
| comp s t => fun a => (eval t <-< eval s) a
| unit => fun _ => eta tt
| injl t => fun a => map inl (eval t a)
| injr t => fun a => map inr (eval t a)
| case s t => fun p => let (ab, c) := p in
    match ab with
    | inl a => eval s (a, c)
    | inr b => eval t (b, c)
    end
| pair s t => fun a => phi (eval s a) (eval t a)
| take t => fun ab => eval t (fst ab)
| drop t => fun ab => eval t (snd ab)
| assertl s _ => fun p => let (ab, c) := p in
    match ab with
    | inl a => eval s (a, c)
    | inr b => mzero
    end
| assertr _ t => fun p => let (ab, c) := p in
    match ab with
    | inl a => mzero
    | inr b => eval t (b, c)
    end
| fail _ => kzero
end.
