(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr
open Constrexpr

val primitive_flag : bool ref

val declare_projections :
  inductive ->
  Entries.constant_universes_entry ->
  ?kind:Decl_kinds.definition_object_kind ->
  Id.t ->
  bool list ->
  UnivNames.universe_binders ->
  Impargs.manual_implicits list ->
  Constr.rel_context ->
    (Name.t * bool) list * Constant.t option list

val definition_structure :
  inductive_kind -> Decl_kinds.cumulative_inductive_flag -> Decl_kinds.polymorphic ->
  Declarations.recursivity_kind ->
  (coercion_flag *
  Names.lident *
  universe_decl_expr option *
  local_binder_expr list *
  (local_decl_expr with_instance with_priority with_notation) list *
  Id.t * constr_expr option) list ->
  GlobRef.t list

val declare_existing_class : GlobRef.t -> unit
