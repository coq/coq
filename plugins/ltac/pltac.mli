(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac parsing entries *)

open Pcoq
open Libnames
open Constrexpr
open Tacexpr
open Genredexpr
open Tactypes

val open_constr : constr_expr Entry.t
val constr_with_bindings : constr_expr with_bindings Entry.t
val bindings : constr_expr bindings Entry.t
val hypident : (Names.lident * Locus.hyp_location_flag) Entry.t
val constr_may_eval : (constr_expr,qualid or_by_notation,constr_expr) may_eval Entry.t
val constr_eval : (constr_expr,qualid or_by_notation,constr_expr) may_eval Entry.t
val uconstr : constr_expr Entry.t
val quantified_hypothesis : quantified_hypothesis Entry.t
val destruction_arg : constr_expr with_bindings Tactics.destruction_arg Entry.t
val int_or_var : int Locus.or_var Entry.t
val simple_tactic : raw_tactic_expr Entry.t
val simple_intropattern : constr_expr intro_pattern_expr CAst.t Entry.t
val in_clause : Names.lident Locus.clause_expr Entry.t
val clause_dft_concl : Names.lident Locus.clause_expr Entry.t
val tactic_arg : raw_tactic_arg Entry.t
val tactic_expr : raw_tactic_expr Entry.t
val binder_tactic : raw_tactic_expr Entry.t
val tactic : raw_tactic_expr Entry.t
val tactic_eoi : raw_tactic_expr Entry.t
