(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Tac2expr

(** Quoted variants of Ltac syntactic categories. Contrarily to the former, they
    sometimes allow anti-quotations. Used for notation scopes. *)

type 'a or_anti =
| QExpr of 'a
| QAnti of Id.t located

type quantified_hypothesis =
| QAnonHyp of int located
| QNamedHyp of Id.t located

type bindings_r =
| QImplicitBindings of Constrexpr.constr_expr list
| QExplicitBindings of (quantified_hypothesis located or_anti * Constrexpr.constr_expr) located list
| QNoBindings

type bindings = bindings_r located

type intro_pattern_r =
| QIntroForthcoming of bool
| QIntroNaming of intro_pattern_naming
| QIntroAction of intro_pattern_action
and intro_pattern_naming_r =
| QIntroIdentifier of Id.t located or_anti
| QIntroFresh of Id.t located or_anti
| QIntroAnonymous
and intro_pattern_action_r =
| QIntroWildcard
| QIntroOrAndPattern of or_and_intro_pattern
| QIntroInjection of intro_pattern list located
(* | QIntroApplyOn of Empty.t (** Not implemented yet *) *)
| QIntroRewrite of bool
and or_and_intro_pattern_r =
| QIntroOrPattern of intro_pattern list located list
| QIntroAndPattern of intro_pattern list located

and intro_pattern = intro_pattern_r located
and intro_pattern_naming = intro_pattern_naming_r located
and intro_pattern_action = intro_pattern_action_r located
and or_and_intro_pattern = or_and_intro_pattern_r located

type occurrences_r =
| QAllOccurrences
| QAllOccurrencesBut of int located or_anti list
| QNoOccurrences
| QOnlyOccurrences of int located or_anti list

type occurrences = occurrences_r located

type hyp_location = (occurrences * Id.t located or_anti) * Locus.hyp_location_flag

type clause_r =
  { q_onhyps : hyp_location list option; q_concl_occs : occurrences; }

type clause = clause_r located

type constr_with_bindings = (Constrexpr.constr_expr * bindings) located

type destruction_arg_r =
| QElimOnConstr of constr_with_bindings
| QElimOnIdent of Id.t located
| QElimOnAnonHyp of int located

type destruction_arg = destruction_arg_r located

type induction_clause_r = {
  indcl_arg : destruction_arg;
  indcl_eqn : intro_pattern_naming option;
  indcl_as : or_and_intro_pattern option;
  indcl_in : clause option;
}

type induction_clause = induction_clause_r located

type conversion_r =
| QConvert of Constrexpr.constr_expr
| QConvertWith of Constrexpr.constr_expr * Constrexpr.constr_expr

type conversion = conversion_r located

type multi_r =
| QPrecisely of int located
| QUpTo of int located
| QRepeatStar
| QRepeatPlus

type multi = multi_r located

type rewriting_r = {
  rew_orient : bool option located;
  rew_repeat : multi;
  rew_equatn : constr_with_bindings;
}

type rewriting = rewriting_r located

type dispatch_r = raw_tacexpr option list * (raw_tacexpr option * raw_tacexpr option list) option

type dispatch = dispatch_r located

type red_flag_r =
| QBeta
| QIota
| QMatch
| QFix
| QCofix
| QZeta
| QConst of Libnames.reference or_anti list located
| QDeltaBut of Libnames.reference or_anti list located

type red_flag = red_flag_r located

type strategy_flag = red_flag list located

type constr_match_pattern_r =
| QConstrMatchPattern of Constrexpr.constr_expr
| QConstrMatchContext of Id.t option * Constrexpr.constr_expr

type constr_match_pattern = constr_match_pattern_r located

type constr_match_branch = (constr_match_pattern * raw_tacexpr) located

type constr_matching = constr_match_branch list located

type goal_match_pattern_r = {
  q_goal_match_concl : constr_match_pattern;
  q_goal_match_hyps : (Misctypes.lname * constr_match_pattern) list;
}

type goal_match_pattern = goal_match_pattern_r located

type goal_match_branch = (goal_match_pattern * raw_tacexpr) located

type goal_matching = goal_match_branch list located

type hintdb_r =
| QHintAll
| QHintDbs of Id.t located or_anti list

type hintdb = hintdb_r located

type move_location_r =
| QMoveAfter of Id.t located or_anti
| QMoveBefore of Id.t located or_anti
| QMoveFirst
| QMoveLast

type move_location = move_location_r located

type pose = (Id.t located or_anti option * Constrexpr.constr_expr) located

type assertion_r =
| QAssertType of intro_pattern option * Constrexpr.constr_expr * raw_tacexpr option
| QAssertValue of Id.t located or_anti * Constrexpr.constr_expr

type assertion = assertion_r located
