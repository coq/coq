(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term

(** A bunch of Coq constants used by Progam *)

val sig_typ : unit -> constr
val sig_intro : unit -> constr
val sig_proj1 : unit -> constr
val sigT_typ : unit -> constr
val sigT_intro : unit -> constr
val sigT_proj1 : unit -> constr
val sigT_proj2 : unit -> constr

val prod_typ : unit -> constr
val prod_intro : unit -> constr
val prod_proj1 : unit -> constr
val prod_proj2 : unit -> constr

val coq_eq_ind : unit -> constr
val coq_eq_refl : unit -> constr
val coq_eq_refl_ref : unit -> Globnames.global_reference
val coq_eq_rect : unit -> constr

val coq_JMeq_ind : unit -> constr
val coq_JMeq_refl : unit -> constr

val mk_coq_and : constr list -> constr
val mk_coq_not : constr -> constr
