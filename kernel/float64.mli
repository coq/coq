(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [t] is currently implemented by OCaml's [float] type.

Beware: NaNs have a sign and a payload, while they should be
indistinguishable from Coq's perspective. *)
type t

val is_nan : t -> bool
val is_infinity : t -> bool
val is_neg_infinity : t -> bool

val to_string : t -> string
val of_string : string -> t

val compile : t -> string

val of_float : float -> t

val opp : t -> t
val abs : t -> t

type float_comparison = FEq | FLt | FGt | FNotComparable

(** The IEEE 754 float comparison.
 * NotComparable is returned if there is a NaN in the arguments *)
val compare : t -> t -> float_comparison
[@@ocaml.inline always]

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

val classify : t -> float_class
[@@ocaml.inline always]

val mul : t -> t -> t
[@@ocaml.inline always]

val add : t -> t -> t
[@@ocaml.inline always]

val sub : t -> t -> t
[@@ocaml.inline always]

val div : t -> t -> t
[@@ocaml.inline always]

val sqrt : t -> t
[@@ocaml.inline always]

(** Link with integers *)
val of_int63 : Uint63.t -> t
[@@ocaml.inline always]

val normfr_mantissa : t -> Uint63.t
[@@ocaml.inline always]

(** Shifted exponent extraction *)
val eshift : int

val frshiftexp : t -> t * Uint63.t (* float remainder, shifted exponent *)
[@@ocaml.inline always]

val ldshiftexp : t -> Uint63.t -> t
[@@ocaml.inline always]

val next_up : t -> t
[@@ocaml.inline always]

val next_down : t -> t
[@@ocaml.inline always]

(** Return true if two floats are equal.
 * All NaN values are considered equal. *)
val equal : t -> t -> bool
[@@ocaml.inline always]

val hash : t -> int

(** Total order relation over float values. Behaves like [Pervasives.compare].*)
val total_compare : t -> t -> int
