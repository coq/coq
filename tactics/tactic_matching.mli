 (************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
  subst : Constr_matching.bound_ident_map * Pattern.extended_patvar_map ;
  context : Term.constr Names.Id.Map.t;
  terms : Term.constr Names.Id.Map.t;
  lhs : 'a;
}


(** [match_term env sigma term rules] matches the term [term] with the
    set of matching rules [rules]. The environment [env] and the
    evar_map [sigma] are not currently used, but avoid code
    duplication. *)
val match_term :
  Environ.env ->
  Evd.evar_map ->
  Term.constr ->
  (Pattern.constr_pattern, Tacexpr.glob_tactic_expr) Tacexpr.match_rule list ->
  Tacexpr.glob_tactic_expr t Proofview.tactic

(** [match_goal env sigma hyps concl rules] matches the goal
    [hyps|-concl] with the set of matching rules [rules]. The
    environment [env] and the evar_map [sigma] are used to check
    convertibility for pattern variables shared between hypothesis
    patterns or the conclusion pattern. *)
val match_goal:
  Environ.env ->
  Evd.evar_map ->
  Context.named_context ->
  Term.constr ->
  (Pattern.constr_pattern, Tacexpr.glob_tactic_expr) Tacexpr.match_rule list ->
  Tacexpr.glob_tactic_expr t Proofview.tactic
