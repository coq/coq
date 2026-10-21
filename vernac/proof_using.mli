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

(** Utility code for section variables handling in Proof using... *)

(** At some point it would be good to make this abstract *)
type t = Id.Set.t

(** Process a [using] expression in definitions to provide the list of
    used terms *)
val definition_using
  : Environ.env
  -> Evd.evar_map
  -> using:Vernacexpr.section_subset_expr
  -> terms:EConstr.constr list
  -> t

val name_set : Id.t -> Vernacexpr.section_subset_expr -> unit

val valid_exprs : Environ.env -> type_vars:Id.Set.t -> used:Id.Set.t -> Pp.t list

val suggest_constant : proofloc:Loc.t option -> Environ.env -> Constant.t -> unit

val suggest_variable : proofloc:Loc.t option -> Environ.env -> Id.t -> unit

val get_default_proof_using : unit -> Vernacexpr.section_subset_expr option

val proof_using_opt_name : string list
(** For the stm *)

val using_from_string : string -> Vernacexpr.section_subset_expr
