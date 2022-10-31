Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import jets_secp256k1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition Int128_modulus : Z := 2^128.
Definition Int128_max_unsigned : Z := Int128_modulus - 1.
Definition Int128_max_signed : Z := 2^127 - 1.
Definition Int128_min_signed : Z := -2^127.
Definition t_secp256k1_uint128 := Tstruct _secp256k1_uint128 noattr.  
(* (secp256k1_uint128_at sh x p) says that the structure pointed to by p
 * is equivalent to x modulo 2^128.
 *)
Definition secp256k1_uint128_at sh x :=
   data_at sh
     t_secp256k1_uint128 (Vlong (Int64.repr x), Vlong (Int64.repr (Z.shiftr x 64))).

(*
Definition secp256k1_u128_load_spec : ident * funspec :=
DECLARE _secp256k1_u128_load
  WITH r : val, sh : share, hi : Z, lo : Z
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP(writable_share sh;
         0 <= lo < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr hi); Vlong (Int64.repr lo))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftl hi 64 + lo) r).
*)

Definition secp256k1_u128_mul_spec : ident * funspec :=
DECLARE _secp256k1_u128_mul
  WITH r : val, sh : share, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus;
         0 <= b < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * b) r).

Definition secp256k1_u128_accum_mul_spec : ident * funspec :=
DECLARE _secp256k1_u128_accum_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus;
         0 <= b < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a * b) r).

Definition secp256k1_u128_accum_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_accum_u64
  WITH r : val, sh : share, r0 : Z, a : Z
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a) r).

Definition secp256k1_u128_rshift_spec : ident * funspec :=
DECLARE _secp256k1_u128_rshift
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(writable_share sh;
         0 <= r0 < Int128_modulus;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftr r0 n) r).

Definition secp256k1_u128_to_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_to_u64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr r0))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_u128_hi_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_hi_u64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr (Z.shiftr r0 64)))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_u128_from_u64_spec : ident * funspec :=
DECLARE _secp256k1_u128_from_u64
  WITH r : val, sh : share, a : Z
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP(writable_share sh;
         0 <= a < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh a r).

Definition secp256k1_u128_check_bits_spec : ident * funspec :=
DECLARE _secp256k1_u128_check_bits
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(readable_share sh;
         0 <= r0 < 2^128;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if r0 <? 2^n then 1 else 0)))
  SEP(secp256k1_uint128_at sh r0 r).

(*
Definition secp256k1_i128_load_spec : ident * funspec :=
DECLARE _secp256k1_i128_load
  WITH r : val, sh : share, hi : Z, lo : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tulong ]
    PROP(writable_share sh;
         Int64.min_signed <= hi <= Int64.max_signed;
         0 <= lo < Int64.modulus)
    PARAMS(r; Vlong (Int64.repr hi); Vlong (Int64.repr lo))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftl hi 64 + lo) r).
*)

Definition secp256k1_i128_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_mul
  WITH r : val, sh : share, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * b) r).

Definition secp256k1_i128_accum_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_accum_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int128_min_signed <= r0 <= Int128_max_signed;
         Int128_min_signed <= r0 + a * b <= Int128_max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 + a * b) r).

Definition secp256k1_i128_dissip_mul_spec : ident * funspec :=
DECLARE _secp256k1_i128_dissip_mul
  WITH r : val, sh : share, r0 : Z, a : Z, b : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int128_min_signed <= r0 <= Int128_max_signed;
         Int128_min_signed <= r0 - a * b <= Int128_max_signed)
   PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (r0 - a * b) r).

Definition secp256k1_i128_det_spec : ident * funspec :=
DECLARE _secp256k1_i128_det
  WITH r : val, sh : share, a : Z, b : Z, c : Z, d : Z
  PRE [ tptr t_secp256k1_uint128, tlong, tlong, tlong, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed;
         Int64.min_signed <= b <= Int64.max_signed;
         Int64.min_signed <= c <= Int64.max_signed;
         Int64.min_signed <= d <= Int64.max_signed)
    PARAMS(r; Vlong (Int64.repr a); Vlong (Int64.repr b);
              Vlong (Int64.repr c); Vlong (Int64.repr d))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (a * d - b * c) r).

Definition secp256k1_i128_rshift_spec : ident * funspec :=
DECLARE _secp256k1_i128_rshift
  WITH r : val, sh : share, r0 : Z, n : Z
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP(writable_share sh;
         Int128_min_signed <= r0 <= Int128_max_signed;
         0 <= n < 128)
    PARAMS(r; Vint (Int.repr n))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh (Z.shiftr r0 n) r).

Definition secp256k1_i128_to_u64_spec : ident * funspec :=
DECLARE _secp256k1_i128_to_u64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tulong ]
  PROP()
  RETURN(Vlong (Int64.repr r0))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_i128_to_i64_spec : ident * funspec :=
DECLARE _secp256k1_i128_to_i64
  WITH r : val, sh : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128 ]
    PROP(readable_share sh;
         Int64.min_signed <= r0 <= Int64.max_signed)
    PARAMS(r)
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tlong ]
  PROP()
  RETURN(Vlong (Int64.repr r0))
  SEP(secp256k1_uint128_at sh r0 r).

Definition secp256k1_i128_from_i64_spec : ident * funspec :=
DECLARE _secp256k1_i128_from_i64
  WITH r : val, sh : share, a : Z
  PRE [ tptr t_secp256k1_uint128, tlong ]
    PROP(writable_share sh;
         Int64.min_signed <= a <= Int64.max_signed)
    PARAMS(r; Vlong (Int64.repr a))
  SEP(data_at_ sh t_secp256k1_uint128 r)
POST [ tvoid ]
  PROP()
  RETURN()
  SEP(secp256k1_uint128_at sh a r).

Definition secp256k1_i128_eq_var_spec : ident * funspec :=
DECLARE _secp256k1_i128_eq_var
  WITH r : val, shr : share, r0 : Z,
       s : val, shs : share, s0 : Z
  PRE [ tptr t_secp256k1_uint128, tptr t_secp256k1_uint128 ]
    PROP(readable_share shr;
         readable_share shs)
    PARAMS(r; s)
  SEP(secp256k1_uint128_at shr r0 r;
      secp256k1_uint128_at shs s0 s)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (if r0 mod 2^128 =? s0 mod 2^128 then 1 else 0)))
  SEP(secp256k1_uint128_at shr r0 r
     ;secp256k1_uint128_at shs s0 s).

Definition secp256k1_i128_eq_var_spec_alias : ident * funspec :=
DECLARE _secp256k1_i128_eq_var
  WITH r : val, shr : share, r0 : Z
  PRE [ tptr t_secp256k1_uint128, tptr t_secp256k1_uint128 ]
    PROP(readable_share shr)
    PARAMS(r; r)
  SEP(secp256k1_uint128_at shr r0 r)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr 1))
  SEP(secp256k1_uint128_at shr r0 r).

Definition secp256k1_i128_check_pow2_spec : ident * funspec :=
DECLARE _secp256k1_i128_check_pow2
  WITH r : val, sh : share, r0 : Z, n : Z, sign : Z
  PRE [ tptr t_secp256k1_uint128, tuint, tint ]
    PROP(readable_share sh;
         Int128_min_signed <= r0 <= Int128_max_signed;
         0 <= n < 127;
         sign = -1 \/ sign = 1)
    PARAMS(r; Vint (Int.repr n); Vint (Int.repr sign))
  SEP(secp256k1_uint128_at sh r0 r)
POST [ tint ]
  PROP()
  RETURN(Vint (Int.repr (Z.b2z (r0 =? sign*2^n))))
  SEP(secp256k1_uint128_at sh r0 r).
