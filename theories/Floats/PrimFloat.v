Require Import Int63 FloatClass.

(** * Definition of the interface for primitive floating-point arithmetic

This interface provides processor operators for the Binary64 format of the
IEEE 754-2008 standard. *)

(** ** Type definition for the co-domain of [compare] *)
Variant float_comparison : Set := FEq | FLt | FGt | FNotComparable.

Register float_comparison as kernel.ind_f_cmp.

Register float_class as kernel.ind_f_class.

(** ** The main type *)
(** [float]: primitive type for Binary64 floating-point numbers. *)
Primitive float := #float64_type.

(** ** Syntax support *)
Declare Scope float_scope.
Delimit Scope float_scope with float.
Bind Scope float_scope with float.

Declare ML Module "float_syntax_plugin".

(** ** Floating-point operators *)
Primitive classify := #float64_classify.

Primitive abs := #float64_abs.

Primitive sqrt := #float64_sqrt.

Primitive opp := #float64_opp.
Notation "- x" := (opp x) : float_scope.

Primitive eqb := #float64_eq.
Notation "x == y" := (eqb x y) (at level 70, no associativity) : float_scope.

Primitive ltb := #float64_lt.
Notation "x < y" := (ltb x y) (at level 70, no associativity) : float_scope.

Primitive leb := #float64_le.
Notation "x <= y" := (leb x y) (at level 70, no associativity) : float_scope.

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

(** ** Conversions *)

(** [of_int63]: convert a primitive integer into a float value.
    The value is rounded if need be. *)
Primitive of_int63 := #float64_of_int63.

(** Specification of [normfr_mantissa]:
- If the input is a float value with an absolute value inside $[0.5, 1.)$#[0.5, 1.)#;
- Then return its mantissa as a primitive integer.
  The mantissa will be a 53-bit integer with its most significant bit set to 1;
- Else return zero.

The sign bit is always ignored. *)
Primitive normfr_mantissa := #float64_normfr_mantissa.

(** ** Exponent manipulation functions *)
Definition shift := 2101%int63. (** [= 2*emax + prec] *)

(** [frshiftexp]: convert a float to fractional part in $[0.5, 1.)$#[0.5, 1.)#
and integer part. *)
Primitive frshiftexp := #float64_frshiftexp.

(** [ldshiftexp]: multiply a float by an integral power of 2. *)
Primitive ldshiftexp := #float64_ldshiftexp.

(** ** Predecesor/Successor functions *)

(** [next_up]: return the next float towards positive infinity. *)
Primitive next_up := #float64_next_up.

(** [next_down]: return the next float towards negative infinity. *)
Primitive next_down := #float64_next_down.

(** ** Special values (needed for pretty-printing) *)
Definition infinity := Eval compute in div (of_int63 1) (of_int63 0).
Definition neg_infinity := Eval compute in opp infinity.
Definition nan := Eval compute in div (of_int63 0) (of_int63 0).

Register infinity as num.float.infinity.
Register neg_infinity as num.float.neg_infinity.
Register nan as num.float.nan.

(** ** Other special values *)
Definition one := Eval compute in (of_int63 1).
Definition zero := Eval compute in (of_int63 0).
Definition neg_zero := Eval compute in (-zero)%float.
Definition two := Eval compute in (of_int63 2).

(** ** Predicates and helper functions *)
Definition is_nan f := negb (f == f)%float.

Definition is_zero f := (f == zero)%float. (* note: 0 == -0 with floats *)

Definition is_infinity f := (abs f == infinity)%float.

Definition is_finite (x : float) := negb (is_nan x || is_infinity x).

(** [get_sign]: return [true] for [-] sign, [false] for [+] sign. *)
Definition get_sign f :=
  let f := if is_zero f then (one / f)%float else f in
  (f < zero)%float.
