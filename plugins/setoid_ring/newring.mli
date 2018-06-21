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
open EConstr
open Libnames
open Constrexpr
open Newring_ast

val protect_tac_in : string -> Id.t -> unit Proofview.tactic

val protect_tac : string -> unit Proofview.tactic

val add_theory :
  Id.t ->
  constr_expr ->
  constr_expr ring_mod list -> unit

val from_name : ring_info Spmap.t ref

val ring_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic

val add_field_theory :
  Id.t ->
  constr_expr ->
  constr_expr field_mod list -> unit

val field_from_name : field_info Spmap.t ref

val field_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic
