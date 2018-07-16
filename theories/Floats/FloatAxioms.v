Require Import ZArith Int63 SpecFloat PrimFloat.

(* Properties of the Binary64 IEEE 754 format *)
Definition prec := 53%Z.
Definition emax := 1024%Z.

Notation valid_binary := (valid_binary prec emax).

Definition SF64mul := SFmul prec emax.
Definition SF64add := SFadd prec emax.
Definition SF64sub := SFsub prec emax.
Definition SF64div := SFdiv prec emax.
Definition SF64sqrt := SFsqrt prec emax.

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

Axiom Prim2SF_valid : forall x, valid_binary (Prim2SF x) = true.
Axiom SF2Prim_Prim2SF : forall x, SF2Prim (Prim2SF x) = x.
Axiom Prim2SF_SF2Prim : forall x, valid_binary x = true -> Prim2SF (SF2Prim x) = x.

Theorem Prim2SF_inj : forall x y, Prim2SF x = Prim2SF y -> x = y.
  intros. rewrite <- SF2Prim_Prim2SF. symmetry. rewrite <- SF2Prim_Prim2SF. now rewrite H.
Qed.

Theorem SF2Prim_inj : forall x y, SF2Prim x = SF2Prim y -> valid_binary x = true -> valid_binary y = true -> x = y.
  intros. rewrite <- Prim2SF_SF2Prim by assumption. symmetry. rewrite <- Prim2SF_SF2Prim by assumption. rewrite H. reflexivity.
Qed.

Axiom opp_spec : forall x, Prim2SF (-x)%float = SFopp (Prim2SF x).
Axiom abs_spec : forall x, Prim2SF (abs x) = SFabs (Prim2SF x).
Axiom compare_spec : forall x y, (x ?= y)%float = SFcompare (Prim2SF x) (Prim2SF y).
Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).
Axiom add_spec : forall x y, Prim2SF (x + y)%float = SF64add (Prim2SF x) (Prim2SF y).
Axiom sub_spec : forall x y, Prim2SF (x - y)%float = SF64sub (Prim2SF x) (Prim2SF y).
Axiom div_spec : forall x y, Prim2SF (x / y)%float = SF64div (Prim2SF x) (Prim2SF y).
Axiom sqrt_spec : forall x, Prim2SF (sqrt x) = SF64sqrt (Prim2SF x).

Axiom of_int63_spec : forall n, Prim2SF (of_int63 n) = binary_normalize prec emax (to_Z n) 0%Z false.
Axiom normfr_mantissa_spec : forall f, to_Z (normfr_mantissa f) = Z.of_N (SFnormfr_mantissa prec (Prim2SF f)).

Axiom frexp_spec : forall f, let (m,e) := frexp f in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF f).
Axiom ldexp_spec : forall f e, Prim2SF (ldexp f e) = SFldexp prec emax (Prim2SF f) e.
