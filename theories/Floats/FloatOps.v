(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinNums PosDef IntDef Uint63Axioms.
From Stdlib Require Import FloatClass SpecFloat PrimFloat.

(** * Derived operations and mapping between primitive [float]s and [spec_float]s *)

Definition prec := Eval compute in Z.of_nat 53.
Definition emax := Eval compute in Z.of_nat 1024.
Notation emin := (emin prec emax).

Definition shift := Eval compute in Z.of_nat 2101. (** [= 2*emax + prec] *)

Module Z.
  Definition frexp f :=
    let (m, se) := frshiftexp f in
    (m, (Z.sub (to_Z se) shift)).

  Definition ldexp f e :=
    let e' := Z.max (Z.min e (Z.sub emax emin)) (Z.sub (Z.sub emin emax) (Zpos 1)) in
    ldshiftexp f (of_Z (Z.add e' shift)).
End Z.

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
              let e := Z.sub exp prec in
              let (shr, e') := shr_fexp prec emax (to_Z (normfr_mantissa r))%uint63 e loc_Exact in
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
