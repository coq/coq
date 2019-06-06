(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

type projection_flags = {
  pf_subclass: bool;
  pf_canonical: bool;
}

val declare_projections :
  inductive ->
  Entries.universes_entry ->
  ?kind:Decl_kinds.definition_object_kind ->
  Id.t ->
  projection_flags list ->
  Impargs.manual_implicits list ->
  Constr.rel_context ->
    Recordops.proj_kind list * Constant.t option list

val declare_structure_entry : Recordops.struc_tuple -> unit

val definition_structure
  :  universe_decl_expr option
  -> inductive_kind
  -> template:bool option
  -> Decl_kinds.cumulative_inductive_flag
  -> poly:bool
  -> Declarations.recursivity_kind
  -> (coercion_flag *
      Names.lident *
      local_binder_expr list *
      (local_decl_expr * record_field_attr) list *
      Id.t * constr_expr option) list
  -> GlobRef.t list

val declare_existing_class : GlobRef.t -> unit
