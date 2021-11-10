(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Evd

(** A bunch of Coq constants used by Program *)

val sig_typ : unit -> GlobRef.t
val sig_intro : unit -> GlobRef.t
val sig_proj1 : unit -> GlobRef.t
val sigT_typ : unit -> GlobRef.t
val sigT_intro : unit -> GlobRef.t
val sigT_proj1 : unit -> GlobRef.t
val sigT_proj2 : unit -> GlobRef.t

val prod_typ : unit -> GlobRef.t
val prod_intro : unit -> GlobRef.t
val prod_proj1 : unit -> GlobRef.t
val prod_proj2 : unit -> GlobRef.t

val coq_eq_ind : unit -> GlobRef.t
val coq_eq_refl : unit -> GlobRef.t
val coq_eq_refl_ref : unit -> GlobRef.t
val coq_eq_rect : unit -> GlobRef.t

val coq_JMeq_ind : unit -> GlobRef.t
val coq_JMeq_refl : unit -> GlobRef.t

val mk_coq_and : Evd.evar_map -> constr list -> Evd.evar_map * constr
val mk_coq_not : Evd.evar_map -> constr -> Evd.evar_map * constr

(** Polymorphic application of delayed references *)
val papp : evar_map -> (unit -> GlobRef.t) -> constr array -> evar_map * constr

val get_proofs_transparency : unit -> bool
val is_program_cases : unit -> bool
val is_program_generalized_coercion : unit -> bool
