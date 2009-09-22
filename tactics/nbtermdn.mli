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
open Libnames
(*i*)

(* Named, bounded-depth, term-discrimination nets. *)

type ('na,'a) t
type ('na,'a) frozen_t

val create : unit -> ('na,'a) t

val add : ('na,'a) t -> ('na * (constr_pattern * 'a)) -> unit
val rmv : ('na,'a) t -> 'na -> unit
val in_dn : ('na,'a) t -> 'na -> bool
val remap : ('na,'a) t -> 'na -> (constr_pattern * 'a) -> unit

val lookup : ('na,'a) t -> constr -> (constr_pattern * 'a) list
val app : ('na -> (constr_pattern * 'a) -> unit) -> ('na,'a) t -> unit

val dnet_depth : int ref

val freeze : ('na,'a) t -> ('na,'a) frozen_t
val unfreeze : ('na,'a) frozen_t -> ('na,'a) t -> unit
val empty : ('na,'a) t -> unit
val to2lists : ('na,'a) t -> ('na * (constr_pattern * 'a)) list *
                             (Termdn.term_label option * 'a Btermdn.t) list
