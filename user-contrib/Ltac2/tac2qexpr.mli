(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2expr

(** Quoted variants of Ltac syntactic categories. Contrarily to the former, they
    sometimes allow anti-quotations. Used for notation scopes. *)

type 'a or_anti =
| QExpr of 'a
| QAnti of Id.t CAst.t

type reference_r =
| QReference of Libnames.qualid
| QHypothesis of Id.t

type reference = reference_r CAst.t

type quantified_hypothesis =
| QAnonHyp of int CAst.t
| QNamedHyp of Id.t CAst.t

type bindings_r =
| QImplicitBindings of Constrexpr.constr_expr list
| QExplicitBindings of (quantified_hypothesis CAst.t or_anti * Constrexpr.constr_expr) CAst.t list
| QNoBindings

type bindings = bindings_r CAst.t

type intro_pattern_r =
| QIntroForthcoming of bool
| QIntroNaming of intro_pattern_naming
| QIntroAction of intro_pattern_action
and intro_pattern_naming_r =
| QIntroIdentifier of Id.t CAst.t or_anti
| QIntroFresh of Id.t CAst.t or_anti
| QIntroAnonymous
and intro_pattern_action_r =
| QIntroWildcard
| QIntroOrAndPattern of or_and_intro_pattern
| QIntroInjection of intro_pattern list CAst.t
(* | QIntroApplyOn of Empty.t (** Not implemented yet *) *)
| QIntroRewrite of bool
and or_and_intro_pattern_r =
| QIntroOrPattern of intro_pattern list CAst.t list
| QIntroAndPattern of intro_pattern list CAst.t

and intro_pattern = intro_pattern_r CAst.t
and intro_pattern_naming = intro_pattern_naming_r CAst.t
and intro_pattern_action = intro_pattern_action_r CAst.t
and or_and_intro_pattern = or_and_intro_pattern_r CAst.t

type occurrences_r =
| QAllOccurrences
| QAllOccurrencesBut of int CAst.t or_anti list
| QNoOccurrences
| QOnlyOccurrences of int CAst.t or_anti list

type occurrences = occurrences_r CAst.t

type hyp_location = (occurrences * Id.t CAst.t or_anti) * Locus.hyp_location_flag

type clause_r =
  { q_onhyps : hyp_location list option; q_concl_occs : occurrences; }

type clause = clause_r CAst.t

type constr_with_bindings = (Constrexpr.constr_expr * bindings) CAst.t

type destruction_arg_r =
| QElimOnConstr of constr_with_bindings
| QElimOnIdent of Id.t CAst.t
| QElimOnAnonHyp of int CAst.t

type destruction_arg = destruction_arg_r CAst.t

type induction_clause_r = {
  indcl_arg : destruction_arg;
  indcl_eqn : intro_pattern_naming option;
  indcl_as : or_and_intro_pattern option;
  indcl_in : clause option;
}

type induction_clause = induction_clause_r CAst.t

type conversion_r =
| QConvert of Constrexpr.constr_expr
| QConvertWith of Constrexpr.constr_expr * Constrexpr.constr_expr

type conversion = conversion_r CAst.t

type multi_r =
| QPrecisely of int CAst.t
| QUpTo of int CAst.t
| QRepeatStar
| QRepeatPlus

type multi = multi_r CAst.t

type rewriting_r = {
  rew_orient : bool option CAst.t;
  rew_repeat : multi;
  rew_equatn : constr_with_bindings;
}

type rewriting = rewriting_r CAst.t

type dispatch_r = raw_tacexpr option list * (raw_tacexpr option * raw_tacexpr option list) option

type dispatch = dispatch_r CAst.t

type red_flag_r =
| QBeta
| QIota
| QMatch
| QFix
| QCofix
| QZeta
| QConst of reference or_anti list CAst.t
| QDeltaBut of reference or_anti list CAst.t

type red_flag = red_flag_r CAst.t

type strategy_flag = red_flag list CAst.t

type constr_match_pattern_r =
| QConstrMatchPattern of Constrexpr.constr_expr
| QConstrMatchContext of Id.t option * Constrexpr.constr_expr

type constr_match_pattern = constr_match_pattern_r CAst.t

type constr_match_branch = (constr_match_pattern * raw_tacexpr) CAst.t

type constr_matching = constr_match_branch list CAst.t

type goal_match_pattern_r = {
  q_goal_match_concl : constr_match_pattern;
  q_goal_match_hyps : (Names.lname * constr_match_pattern) list;
}

type goal_match_pattern = goal_match_pattern_r CAst.t

type goal_match_branch = (goal_match_pattern * raw_tacexpr) CAst.t

type goal_matching = goal_match_branch list CAst.t

type hintdb_r =
| QHintAll
| QHintDbs of Id.t CAst.t or_anti list

type hintdb = hintdb_r CAst.t

type move_location_r =
| QMoveAfter of Id.t CAst.t or_anti
| QMoveBefore of Id.t CAst.t or_anti
| QMoveFirst
| QMoveLast

type move_location = move_location_r CAst.t

type pose = (Id.t CAst.t or_anti option * Constrexpr.constr_expr) CAst.t

type assertion_r =
| QAssertType of intro_pattern option * Constrexpr.constr_expr * raw_tacexpr option
| QAssertValue of Id.t CAst.t or_anti * Constrexpr.constr_expr

type assertion = assertion_r CAst.t
