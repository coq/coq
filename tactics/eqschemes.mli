(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file builds schemes relative to equality inductive types *)

open Names
open Constr
open Environ
open Ind_tables

(** Builds a left-to-right rewriting scheme for an equality type *)

val rew_l2r_dep_scheme_kind : individual scheme_kind
val rew_l2r_scheme_kind : individual scheme_kind
val rew_r2l_forward_dep_scheme_kind : individual scheme_kind
val rew_l2r_forward_dep_scheme_kind : individual scheme_kind
val rew_r2l_dep_scheme_kind : individual scheme_kind
val rew_r2l_scheme_kind : individual scheme_kind

val build_r2l_rew_scheme : bool -> env -> inductive -> Sorts.family -> 
  constr Evd.in_evar_universe_context
val build_l2r_rew_scheme : bool -> env -> inductive -> Sorts.family -> 
  constr Evd.in_evar_universe_context * Safe_typing.private_constants
val build_r2l_forward_rew_scheme :
  bool -> env -> inductive -> Sorts.family -> constr Evd.in_evar_universe_context
val build_l2r_forward_rew_scheme :
  bool -> env -> inductive -> Sorts.family -> constr Evd.in_evar_universe_context

(** Builds a symmetry scheme for a symmetrical equality type *)

val build_sym_scheme : env -> inductive -> constr Evd.in_evar_universe_context
val sym_scheme_kind : individual scheme_kind

val build_sym_involutive_scheme : env -> inductive -> 
  constr Evd.in_evar_universe_context * Safe_typing.private_constants
val sym_involutive_scheme_kind : individual scheme_kind

(** Builds a congruence scheme for an equality type *)

val congr_scheme_kind : individual scheme_kind
val build_congr : env -> constr * constr * Univ.ContextSet.t -> inductive -> 
  constr Evd.in_evar_universe_context
