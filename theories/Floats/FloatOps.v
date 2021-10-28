(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith Uint63 SpecFloat PrimFloat.

(** * Derived operations and mapping between primitive [float]s and [spec_float]s *)

Definition prec := 53%Z.
Definition emax := 1024%Z.
Notation emin := (emin prec emax).

Definition shift := 2101%Z. (** [= 2*emax + prec] *)

Module Z.
  Definition frexp f :=
    let (m, se) := frshiftexp f in
    (m, (φ se - shift)%Z%uint63).

  Definition ldexp f e :=
    let e' := Z.max (Z.min e (emax - emin)) (emin - emax - 1) in
    ldshiftexp f (of_Z (e' + shift)).
End Z.

#[deprecated(since = "8.15.0", note = "Use Z.frexp instead.")]
Notation frexp := Z.frexp (only parsing).

#[deprecated(since = "8.15.0", note = "Use Z.ldexp instead.")]
Notation ldexp := Z.ldexp (only parsing).

Definition ulp f := Z.ldexp one (fexp prec emax (snd (Z.frexp f))).

(** [Prim2SF] is an injective function that will be useful to express
the properties of the implemented Binary64 format (see [FloatAxioms]).
*)
Definition Prim2SF f :=
  if is_nan f then S754_nan
  else if is_zero f then S754_zero (get_sign f)
       else if is_infinity f then S754_infinity (get_sign f)
            else
              let (r, exp) := Z.frexp f in
              let e := (exp - prec)%Z in
              let (shr, e') := shr_fexp prec emax (φ (normfr_mantissa r))%uint63 e loc_Exact in
              match shr_m shr with
              | Zpos p => S754_finite (get_sign f) p e'
              | Zneg _ | Z0 => S754_zero false (* must never occur *)
              end.

Definition SF2Prim ef :=
  match ef with
  | S754_nan => nan
  | S754_zero false => zero
  | S754_zero true => neg_zero
  | S754_infinity false => infinity
  | S754_infinity true => neg_infinity
  | S754_finite s m e =>
    let pm := of_uint63 (of_Z (Zpos m)) in
    let f := Z.ldexp pm e in
    if s then (-f)%float else f
  end.
