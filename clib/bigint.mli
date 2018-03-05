(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Arbitrary large integer numbers *)

type bigint

val of_string : string -> bigint
(** May raise a Failure just as [int_of_string] on non-numerical strings *)

val to_string : bigint -> string

val of_int : int -> bigint
val to_int : bigint -> int (** May raise a Failure on oversized numbers *)

val zero : bigint
val one : bigint
val two : bigint

val div2_with_rest : bigint -> bigint * bool (** true=odd; false=even *)
val add_1 : bigint -> bigint
val sub_1 : bigint -> bigint
val mult_2 : bigint -> bigint

val add : bigint -> bigint -> bigint
val sub : bigint -> bigint -> bigint
val mult : bigint -> bigint -> bigint

(** Euclid division m/d = (q,r), with m = q*d+r and |r|<|q|.
    This is the "Trunc" variant (a.k.a "Truncated-Toward-Zero"),
    as with ocaml's / (but not as ocaml's Big_int.quomod_big_int).
    We have sign r = sign m *)

val euclid : bigint -> bigint -> bigint * bigint

val less_than : bigint -> bigint -> bool
val equal : bigint -> bigint -> bool

val is_strictly_pos : bigint -> bool
val is_strictly_neg : bigint -> bool
val is_pos_or_zero : bigint -> bool
val is_neg_or_zero : bigint -> bool
val neg : bigint -> bigint

val pow : bigint -> int -> bigint
