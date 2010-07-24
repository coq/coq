(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
(*i*)

(* Arbitrary large integer numbers *)

type bigint

val of_string : string -> bigint
val to_string : bigint -> string

val zero : bigint
val one : bigint
val two : bigint

val div2_with_rest : bigint -> bigint * bool (* true=odd; false=even *)
val add_1 : bigint -> bigint
val sub_1 : bigint -> bigint
val mult_2 : bigint -> bigint

val add : bigint -> bigint -> bigint
val sub : bigint -> bigint -> bigint
val mult : bigint -> bigint -> bigint
val euclid : bigint -> bigint -> bigint * bigint

val less_than : bigint -> bigint -> bool
val equal : bigint -> bigint -> bool

val is_strictly_pos : bigint -> bool
val is_strictly_neg : bigint -> bool
val is_pos_or_zero : bigint -> bool
val is_neg_or_zero : bigint -> bool
val neg : bigint -> bigint

val pow : bigint -> bigint -> bigint

val pr_bigint : bigint -> std_ppcmds
