(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Sos_types

type poly

val poly_isconst : poly -> bool

val poly_neg : poly -> poly

val poly_mul : poly -> poly -> poly

val poly_pow : poly -> int -> poly

val poly_const : Num.num -> poly

val poly_of_term : term -> poly

val term_of_poly : poly -> term

val term_of_sos : positivstellensatz * (Num.num * poly) list ->
     positivstellensatz

val string_of_poly : poly -> string

val real_positivnullstellensatz_general : bool -> int -> poly list ->
     (poly * positivstellensatz) list ->
     poly -> poly list * (positivstellensatz * (Num.num * poly) list) list

val sumofsquares : poly -> Num.num * ( Num.num * poly) list
