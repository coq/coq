(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [t] is currently implemented by OCaml's [float] type.

Beware: NaNs have a sign and a payload, while they should be
indistinguishable from Rocq's perspective. *)
type t

(** Test functions for special values to avoid calling [classify] *)
val is_nan : t -> bool
val is_infinity : t -> bool
val is_neg_infinity : t -> bool

val of_string : string -> t

(** Print a float exactly as an hexadecimal value (exact decimal
 * printing would be possible but sometimes requires more than 700
 * digits). *)
val to_hex_string : t -> string

(** Print a float as a decimal value. The printing is not exact (the
 * real value printed is not always the given floating-point value),
 * however printing is precise enough that forall float [f],
 * [of_string (to_decimal_string f) = f]. *)
val to_string : t -> string

val compile : t -> string

val of_float : float -> t

(** All NaNs are normalized to [Stdlib.nan].
    @since 8.15 *)
val to_float : t -> float

(** Return [true] for "-", [false] for "+". *)
val sign : t -> bool

val opp : t -> t
val abs : t -> t

type float_comparison = FEq | FLt | FGt | FNotComparable

val eq : t -> t -> bool

val lt : t -> t -> bool

val le : t -> t -> bool

(** The IEEE 754 float comparison.
 * NotComparable is returned if there is a NaN in the arguments *)
val compare : t -> t -> float_comparison

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

val classify : t -> float_class

val mul : t -> t -> t

val add : t -> t -> t

val sub : t -> t -> t

val div : t -> t -> t

val sqrt : t -> t

(** Link with integers *)
val of_uint63 : Uint63.t -> t

val normfr_mantissa : t -> Uint63.t

(** Shifted exponent extraction *)
val eshift : int

val frshiftexp : t -> t * Uint63.t (* float remainder, shifted exponent *)

val ldshiftexp : t -> Uint63.t -> t

val next_up : t -> t

val next_down : t -> t

(** Return true if two floats are equal.
 * All NaN values are considered equal. *)
val equal : t -> t -> bool

val hash : t -> int

(** Total order relation over float values. Behaves like [Pervasives.compare].*)
val total_compare : t -> t -> int

val is_float64 : Obj.t -> bool
