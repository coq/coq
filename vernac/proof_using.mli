(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Utility code for section variables handling in Proof using... *)

val process_expr :
  Environ.env -> Vernacexpr.section_subset_expr -> Constr.types list ->
    Names.Id.t list

val name_set : Names.Id.t -> Vernacexpr.section_subset_expr -> unit

val suggest_constant : Environ.env -> Names.Constant.t -> unit

val suggest_variable : Environ.env -> Names.Id.t -> unit

val get_default_proof_using : unit -> Vernacexpr.section_subset_expr option
