(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open EConstr
open Libnames
open Globnames
open Constrexpr
open Newring_ast

val protect_tac_in : string -> Id.t -> unit Proofview.tactic

val protect_tac : string -> unit Proofview.tactic

val closed_term : EConstr.constr -> global_reference list -> unit Proofview.tactic

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
