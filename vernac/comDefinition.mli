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
open Redexpr
open Constrexpr

(** {6 Definitions/Let} *)

val interp_definition
  :  program_mode:bool
  -> Environ.env
  -> Evd.evar_map
  -> Constrintern.internalization_env
  -> Constrexpr.local_binder_expr list
  -> red_expr option
  -> constr_expr
  -> constr_expr option
  -> Evd.evar_map * (EConstr.t * EConstr.t option) * Impargs.manual_implicits

val do_definition
  :  ?hook:Declare.Hook.t
  -> name:Id.t
  -> ?scope:Locality.definition_scope
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> kind:Decls.definition_object_kind
  -> ?using:Vernacexpr.section_subset_expr
  -> universe_decl_expr option
  -> local_binder_expr list
  -> red_expr option
  -> constr_expr
  -> constr_expr option
  -> unit

val do_definition_program
  :  ?hook:Declare.Hook.t
  -> pm:Declare.OblState.t
  -> name:Id.t
  -> scope:Locality.definition_scope
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> kind:Decls.logical_kind
  -> ?using:Vernacexpr.section_subset_expr
  -> universe_decl_expr option
  -> local_binder_expr list
  -> red_expr option
  -> constr_expr
  -> constr_expr option
  -> Declare.OblState.t
