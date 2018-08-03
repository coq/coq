Require Import ZArith Int63 SpecFloat PrimFloat.

(* Properties of the Binary64 IEEE 754 format *)
Definition prec := 53%Z.
Definition emax := 1024%Z.
Notation emin := (emin prec emax).

Definition frexp f :=
  let (m, se) := frshiftexp f in
  (m, ([| se |] - [| shift |])%Z%int63).

Definition ldexp f e :=
  let e' := Z.max (Z.min e (emax - emin)) (emin - emax - 1) in
  ldshiftexp f (of_Z e' + shift).

Definition Prim2SF f :=
  if is_nan f then S754_nan
  else if is_zero f then S754_zero (get_sign f)
       else if is_infinity f then S754_infinity (get_sign f)
            else
              let (r, exp) := frexp f in
              let e := (exp - prec)%Z in
              let (shr, e') := shr_fexp prec emax [| normfr_mantissa r |]%int63 e loc_Exact in
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
    let pm := of_int63 (of_Z (Zpos m)) in
    let f := ldexp pm e in
    if s then (-f)%float else f
  end.
