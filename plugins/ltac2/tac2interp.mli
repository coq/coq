(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2expr
open Tac2val

type environment = Tac2env.environment

val empty_environment : environment

val interp : environment -> glb_tacexpr -> valexpr Proofview.tactic

val interp_value : environment -> glb_tacexpr -> valexpr
(** Same as [interp] but assumes that the argument is a syntactic value. *)

val eval_global : ltac_constant -> valexpr

val eval_glb_ext : environment -> Tac2dyn.Arg.glb -> valexpr Proofview.tactic

val push_id : environment -> Id.t -> valexpr -> environment

(* val interp_app : closure -> ml_tactic *)

(** {5 Cross-boundary encodings} *)

val get_env : Ltac_pretype.unbound_ltac_var_map -> environment
val set_env : environment -> Ltac_pretype.unbound_ltac_var_map -> Ltac_pretype.unbound_ltac_var_map

(** {5 Exceptions} *)

exception LtacError of KerName.t * valexpr array
(** Ltac2-defined exceptions seen from OCaml side *)
