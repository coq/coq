(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type metadata = {
  name_var : string list;
}

module Monomial :
sig
type t
val repr : t -> int array
val make : int array -> t
end

module Make (P : Polynom.S) :
sig
(* Polynomials *)

type deg = int
type coef = P.t
type poly

val repr : poly -> (coef * Monomial.t) list
val polconst : int -> coef -> poly
val zeroP : poly
val gen : int -> int -> poly

val equal : poly -> poly -> bool

val plusP : poly -> poly -> poly
val oppP : poly -> poly
val multP : poly -> poly -> poly
val puisP : poly -> int -> poly

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

val in_ideal : metadata -> deg -> poly list -> poly -> certificate

module Hashpol : Hashtbl.S with type key = poly

end

exception NotInIdeal

val lexico : bool ref
