(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Pp
(*i*)

(* Arbitrary big natural numbers *)

type bignat

val of_string : string -> bignat
val to_string : bignat -> string

val is_nonzero : bignat -> bool
val zero : bignat
val one : bignat
val is_one : bignat -> bool
val div2_with_rest : bignat -> bignat * bool (* true=odd; false=even *)

val add_1 : bignat -> bignat
val sub_1 : bignat -> bignat (* Remark: [sub_1 0]=0 *)
val mult_2 : bignat -> bignat

val less_than : bignat -> bignat -> bool

type bigint = POS of bignat | NEG of bignat

val bigint_to_string : bigint -> string
val pr_bigint : bigint -> std_ppcmds
