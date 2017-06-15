(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Make (P : Polynom.S) :
sig
(* Polynomials *)

type deg = int
type coef = P.t
type poly

val repr : poly -> (coef * int array) list
val polconst : int -> coef -> poly
val zeroP : poly
val gen : int -> int -> poly

val equal : poly -> poly -> bool
val name_var : string list ref

val plusP : poly -> poly -> poly
val oppP : poly -> poly
val multP : poly -> poly -> poly
val puisP : poly -> int -> poly

val poldepcontent : coef list ref

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

val in_ideal : deg -> poly list -> poly -> poly list * poly * certificate

module Hashpol : Hashtbl.S with type key = poly

val sugar_flag : bool ref
val divide_rem_with_critical_pair : bool ref

end

exception NotInIdeal

val lexico : bool ref
