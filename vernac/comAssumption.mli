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
open Constr
open Entries
open Globnames
open Vernacexpr
open Constrexpr
open Decl_kinds

(** {6 Parameters/Assumptions} *)

val do_assumptions : locality * polymorphic * assumption_object_kind ->
  Vernacexpr.inline -> (ident_decl list * constr_expr) with_coercion list -> bool

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Exported for Classes *)

(** returns [false] if the assumption is neither local to a section,
    nor in a module type and meant to be instantiated. *)
val declare_assumption : coercion_flag -> assumption_kind ->
  types in_constant_universes_entry ->
  Universes.universe_binders -> Impargs.manual_implicits ->
  bool (** implicit *) -> Vernacexpr.inline -> variable CAst.t ->
  global_reference * Univ.Instance.t * bool
