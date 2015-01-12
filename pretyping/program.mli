(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Globnames

(** A bunch of Coq constants used by Progam *)

val sig_typ : unit -> global_reference
val sig_intro : unit -> global_reference
val sig_proj1 : unit -> global_reference
val sigT_typ : unit -> global_reference
val sigT_intro : unit -> global_reference
val sigT_proj1 : unit -> global_reference
val sigT_proj2 : unit -> global_reference

val prod_typ : unit -> global_reference
val prod_intro : unit -> global_reference
val prod_proj1 : unit -> global_reference
val prod_proj2 : unit -> global_reference

val coq_eq_ind : unit -> global_reference
val coq_eq_refl : unit -> global_reference
val coq_eq_refl_ref : unit -> global_reference
val coq_eq_rect : unit -> global_reference

val coq_JMeq_ind : unit -> global_reference
val coq_JMeq_refl : unit -> global_reference

val mk_coq_and : constr list -> constr
val mk_coq_not : constr -> constr

(** Polymorphic application of delayed references *)
val papp : Evd.evar_map ref -> (unit -> global_reference) -> constr array -> constr
