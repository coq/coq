(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Libnames
open Globnames
open Constrexpr
open Tacexpr
open Proof_type
open Newring_ast

val protect_tac_in : string -> Id.t -> unit Proofview.tactic

val protect_tac : string -> unit Proofview.tactic

val closed_term : EConstr.constr -> global_reference list -> unit Proofview.tactic

val process_ring_mods :
  constr_expr ring_mod list ->
  constr coeff_spec * (constr * constr) option *
  cst_tac_spec option * raw_tactic_expr option *
  raw_tactic_expr option *
  (cst_tac_spec * constr_expr) option *
  constr_expr option * constr_expr option

val add_theory :
  Id.t ->
  Evd.evar_map * constr ->
  (constr * constr) option ->
  constr coeff_spec ->
  cst_tac_spec option ->
  raw_tactic_expr option * raw_tactic_expr option ->
  (cst_tac_spec * constr_expr) option ->
  constr_expr option ->
  constr_expr option -> unit

val ic : constr_expr -> Evd.evar_map * constr

val from_name : ring_info Spmap.t ref

val ring_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic

val process_field_mods :
  constr_expr field_mod list ->
  constr coeff_spec *
  (constr * constr) option * constr option *
  cst_tac_spec option * raw_tactic_expr option *
  raw_tactic_expr option *
  (cst_tac_spec * constr_expr) option *
  constr_expr option * constr_expr option

val add_field_theory :
  Id.t ->
  Evd.evar_map * constr ->
  (constr * constr) option ->
  constr coeff_spec ->
  cst_tac_spec option ->
  constr option ->
  raw_tactic_expr option * raw_tactic_expr option ->
  (cst_tac_spec * constr_expr) option ->
  constr_expr option ->
  constr_expr option -> unit

val field_from_name : field_info Spmap.t ref

val field_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic
