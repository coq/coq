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
open Vernacexpr
open Constrexpr

(** {6 Parameters/Assumptions} *)

val interp_assumption
  : program_mode:bool
  -> Environ.env
  -> Evd.evar_map
  -> Constrintern.internalization_env
  -> Constrexpr.local_binder_expr list
  -> constr_expr
  -> Evd.evar_map * EConstr.t * Impargs.manual_implicits

val do_assumptions
  :  program_mode:bool
  -> poly:bool
  -> scope:Locality.definition_scope
  -> kind:Decls.assumption_object_kind
  -> Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> unit

val declare_variable
  : coercion_flag
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> UState.named_universes_entry
  -> Impargs.manual_implicits
  -> Glob_term.binding_kind
  -> variable CAst.t
  -> unit

val declare_axiom
  : coercion_flag
  -> poly:bool
  -> local:Locality.import_status
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> UState.named_universes_entry
  -> Impargs.manual_implicits
  -> Declaremods.inline
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t

(** Context command *)

val do_context
  :  poly:bool
  -> local_binder_expr list
  -> unit

(** The first half of the context command, from expr to constr *)
val interp_context
  :  Environ.env
  -> Evd.evar_map
  -> local_binder_expr list
  -> Evd.evar_map * (Id.t * Constr.t option * Constr.t * Glob_term.binding_kind) list
