Require Import ZArith.
Require Import Int63.

Primitive float := #float64_type.

Declare Scope float_scope.
Delimit Scope float_scope with float.
Bind Scope float_scope with float.

Primitive opp := #float64_opp.
Notation "- x" := (opp x) : float_scope.

Primitive abs := #float64_abs.

Register option as kernel.ind_option.
Primitive compare := #float64_compare.
Notation "x ?= y" := (compare x y) (at level 70, no associativity) : float_scope.

Primitive mul := #float64_mul.
Notation "x * y" := (mul x y) : float_scope.

Primitive add := #float64_add.
Notation "x + y" := (add x y) : float_scope.
Primitive sub := #float64_sub.
Notation "x - y" := (sub x y) : float_scope.

Primitive div := #float64_div.
Notation "x / y" := (div x y) : float_scope.

Primitive sqrt := #float64_sqrt.

(* Convert a primitive integer into a float value.
 * The value is rounded if necessary. *)
Primitive of_int63 := #float64_of_int63.

(* If the input is a float value with an absolute value
 * inside [0.5; 1.) then return its mantissa as a primitive integer.
 * The mantissa will be a 53-bit integer with its most significant bit set to 1.
 * Else return zero.
 * The sign bit is always ignored. *)
Primitive normfr_mantissa := #float64_normfr_mantissa.

(* Exponent manipulation functions *)
Definition shift := (1022 + 52)%int63.
Primitive frshiftexp := #float64_frshiftexp.
Primitive ldshiftexp := #float64_ldshiftexp.

Definition frexp f :=
  let (m, se) := frshiftexp f in
  (m, ([| se |] - [| shift |])%Z%int63).

Definition ldexp f e := ldshiftexp f (of_Z e + shift).

Local Open Scope float_scope.

(* Special values *)
Definition infinity := Eval compute in div (of_int63 1) (of_int63 0).
Definition neg_infinity := Eval compute in opp infinity.
Definition nan := Eval compute in div (of_int63 0) (of_int63 0).

Definition one := Eval compute in (of_int63 1).
Definition zero := Eval compute in (of_int63 0).
Definition neg_zero := Eval compute in (-zero).
Definition two := Eval compute in (of_int63 2).

Definition is_nan f :=
  match f ?= f with
  | None => true
  | _ => false
  end.

Definition is_zero f :=
  match f ?= zero with
  | Some Eq => true (* note: 0 == -0 with floats *)
  | _ => false
  end.

Definition is_infinity f :=
  match f ?= infinity with
  | Some Eq => true
  | Some Lt => match f ?= neg_infinity with
           | Some Eq => true
           | _ => false
           end
  | _ => false
  end.

Definition get_sign f := (* + => false, - => true *)
  let f := if is_zero f then one / f else f in
  match f ?= zero with
  | Some Gt => false
  | _ => true
  end.

Definition is_finite (x : float) := negb (is_nan x || is_infinity x).
