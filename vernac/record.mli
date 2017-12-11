(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Vernacexpr
open Constrexpr
open Globnames

val primitive_flag : bool ref

val definition_structure :
  inductive_kind * Decl_kinds.cumulative_inductive_flag * Decl_kinds.polymorphic *
  Declarations.recursivity_kind * ident_decl with_coercion * local_binder_expr list *
  (local_decl_expr with_instance with_priority with_notation) list *
  Id.t * constr_expr option -> global_reference

val declare_existing_class : global_reference -> unit
