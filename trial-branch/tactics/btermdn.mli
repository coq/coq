(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Pattern
(*i*)

(* Discrimination nets with bounded depth. *)

type 'a t

val create : unit -> 'a t

val add : 'a t -> (constr_pattern * 'a) -> 'a t
val rmv : 'a t -> (constr_pattern * 'a) -> 'a t

val lookup : 'a t -> constr -> (constr_pattern * 'a) list
val app : ((constr_pattern * 'a) -> unit) -> 'a t -> unit

val dnet_depth : int ref
