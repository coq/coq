(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr

(** This file extends Matching with the main logic for Ltac2 match goal. *)

type context = Constr_matching.context

type match_pattern =
| MatchPattern of Pattern.constr_pattern
| MatchContext of Pattern.constr_pattern

type match_context_hyps = match_pattern option * match_pattern

type match_rule = match_context_hyps list * match_pattern

val match_goal:
  Environ.env ->
  Evd.evar_map ->
  constr ->
  rev:bool ->
  match_rule ->
    ((Id.t * context option option * context option) list * (* List of hypotheses matching: name + body context + context *)
    context option * (* Context for conclusion *)
    Ltac_pretype.patvar_map (* Pattern variable substitution *)) Proofview.tactic
