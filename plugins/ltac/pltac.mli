(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Ltac parsing entries *)

open Grammar_API
open Loc
open Names
open Pcoq
open Libnames
open Constrexpr
open Tacexpr
open Genredexpr
open Misctypes

val open_constr : constr_expr Gram.entry
val constr_with_bindings : constr_expr with_bindings Gram.entry
val bindings : constr_expr bindings Gram.entry
val hypident : (Id.t located * Locus.hyp_location_flag) Gram.entry
val constr_may_eval : (constr_expr,reference or_by_notation,constr_expr) may_eval Gram.entry
val constr_eval : (constr_expr,reference or_by_notation,constr_expr) may_eval Gram.entry
val uconstr : constr_expr Gram.entry
val quantified_hypothesis : quantified_hypothesis Gram.entry
val destruction_arg : constr_expr with_bindings destruction_arg Gram.entry
val int_or_var : int or_var Gram.entry
val simple_tactic : raw_tactic_expr Gram.entry
val simple_intropattern : constr_expr intro_pattern_expr located Gram.entry
val in_clause : Names.Id.t Loc.located Locus.clause_expr Gram.entry
val clause_dft_concl : Names.Id.t Loc.located Locus.clause_expr Gram.entry
val tactic_arg : raw_tactic_arg Gram.entry
val tactic_expr : raw_tactic_expr Gram.entry
val binder_tactic : raw_tactic_expr Gram.entry
val tactic : raw_tactic_expr Gram.entry
val tactic_eoi : raw_tactic_expr Gram.entry
