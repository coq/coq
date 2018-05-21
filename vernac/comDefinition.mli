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
open Entries
open Decl_kinds
open Redexpr
open Constrexpr

(** {6 Definitions/Let} *)

val do_definition : program_mode:bool ->
  Id.t -> definition_kind -> universe_decl_expr option ->
  local_binder_expr list -> red_expr option -> constr_expr ->
  constr_expr option -> unit Lemmas.declaration_hook -> unit

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Not used anywhere. *)
val interp_definition :
  universe_decl_expr option -> local_binder_expr list -> polymorphic -> red_expr option -> constr_expr ->
  constr_expr option -> Safe_typing.private_constants definition_entry * Evd.evar_map *
                        UState.universe_decl * Impargs.manual_implicits
