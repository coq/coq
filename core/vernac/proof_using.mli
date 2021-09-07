(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Utility code for section variables handling in Proof using... *)

(** At some point it would be good to make this abstract *)
type t = Names.Id.Set.t

(** Process a [using] expression in definitions to provide the list of
    used terms *)
val definition_using
  : Environ.env
  -> Evd.evar_map
  -> using:Vernacexpr.section_subset_expr
  -> terms:EConstr.constr list
  -> t

val name_set : Names.Id.t -> Vernacexpr.section_subset_expr -> unit

val suggest_constant : Environ.env -> Names.Constant.t -> unit

val suggest_variable : Environ.env -> Names.Id.t -> unit

val get_default_proof_using : unit -> Vernacexpr.section_subset_expr option

val proof_using_opt_name : string list
(** For the stm *)

val using_from_string : string -> Vernacexpr.section_subset_expr
