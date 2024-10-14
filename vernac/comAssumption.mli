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
open Vernacexpr
open Constrexpr

(** {6 Parameters/Assumptions} *)

(** Declaration of a local assumption (Variable/Hypothesis) *)
val declare_variable
  :  coe:coercion_flag
  -> kind:Decls.assumption_object_kind
  -> univs:UState.named_universes_entry
  -> impargs:Impargs.manual_implicits
  -> impl:Glob_term.binding_kind
  -> name:variable
  -> Constr.types
  -> GlobRef.t * UVars.Instance.t

(** Declaration of a local construction (Variable/Hypothesis/Let) *)
val declare_local
  :  coe:coercion_flag
  -> try_assum_as_instance:bool (* true = declare a variable of type a class as an instance *)
  -> kind:Decls.logical_kind
  -> univs:UState.named_universes_entry
  -> impargs:Impargs.manual_implicits
  -> impl:Glob_term.binding_kind
  -> name:variable
  -> Constr.constr option
  -> Constr.types
  -> GlobRef.t * UVars.Instance.t

(** Declaration of a global assumption (Axiom/Parameter) *)
val declare_axiom
  :  coe:coercion_flag
  -> local:Locality.import_status
  -> kind:Decls.assumption_object_kind
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
  -> univs:UState.named_universes_entry
  -> impargs:Impargs.manual_implicits
  -> inline:Declaremods.inline
  -> name:variable
  -> Constr.types
  -> GlobRef.t * UVars.Instance.t

(** Declaration of a global construction (Axiom/Parameter/Definition) *)
val declare_global
  :  coe:coercion_flag
  -> try_assum_as_instance:bool (* true = declare a parameter of type a class as an instance *)
  -> local:Locality.import_status
  -> kind:Decls.logical_kind
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
  -> univs:UState.named_universes_entry
  -> impargs:Impargs.manual_implicits
  -> inline:Declaremods.inline
  -> name:variable
  -> Constr.constr option
  -> Constr.types
  -> GlobRef.t * UVars.Instance.t

(** Interpret the commands Variable/Hypothesis/Axiom/Parameter *)
val do_assumptions
  :  program_mode:bool
  -> poly:bool
  -> scope:Locality.definition_scope
  -> kind:Decls.assumption_object_kind
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
  -> inline:Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> unit

(** Interpret the command Context *)
val do_context
  :  program_mode:bool
  -> poly:bool
  -> local_binder_expr list
  -> unit

(** Interpret a declaration of the form [binders |- typ] as a type *)
val interp_assumption
  :  program_mode:bool
  -> Environ.env
  -> Evd.evar_map
  -> Constrintern.internalization_env
  -> Constrexpr.local_binder_expr list
  -> constr_expr
  -> Evd.evar_map * EConstr.types * Impargs.manual_implicits

(** The first half of the context command, returning the declarations
    in the same order as [Context], using de Bruijn indices (used by Elpi) *)
val interp_context
  :  Environ.env
  -> Evd.evar_map
  -> local_binder_expr list
  -> Evd.evar_map * (Id.t * Constr.t option * Constr.t * Glob_term.binding_kind) list
