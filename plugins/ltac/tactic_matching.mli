(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** This file extends Matching with the main logic for Ltac's
    (lazy)match and (lazy)match goal. *)


(** [t] is the type of matching successes. It ultimately contains a
    {!Tacexpr.glob_tactic_expr} representing the left-hand side of the
    corresponding matching rule, a matching substitution to be
    applied, a context substitution mapping identifier to context like
    those of {!Matching.matching_result}), and a {!Term.constr}
    substitution mapping corresponding to matched hypotheses. *)
type 'a t = {
  subst : Constr_matching.bound_ident_map * Ltac_pretype.extended_patvar_map ;
  context : EConstr.constr Names.Id.Map.t;
  terms : EConstr.constr Names.Id.Map.t;
  lhs : 'a;
}


(** [match_term env sigma term rules] matches the term [term] with the
    set of matching rules [rules]. The environment [env] and the
    evar_map [sigma] are not currently used, but avoid code
    duplication. *)
val match_term :
  Environ.env ->
  Evd.evar_map ->
  EConstr.constr ->
  (Tacexpr.binding_bound_vars * Pattern.constr_pattern, Tacexpr.glob_tactic_expr) Tacexpr.match_rule list ->
  Tacexpr.glob_tactic_expr t Proofview.tactic

(** [match_goal env sigma hyps concl rules] matches the goal
    [hyps|-concl] with the set of matching rules [rules]. The
    environment [env] and the evar_map [sigma] are used to check
    convertibility for pattern variables shared between hypothesis
    patterns or the conclusion pattern. *)
val match_goal:
  Environ.env ->
  Evd.evar_map ->
  EConstr.named_context ->
  EConstr.constr ->
  (Tacexpr.binding_bound_vars * Pattern.constr_pattern, Tacexpr.glob_tactic_expr) Tacexpr.match_rule list ->
  Tacexpr.glob_tactic_expr t Proofview.tactic
