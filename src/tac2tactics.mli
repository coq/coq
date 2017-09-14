(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Locus
open Globnames
open Tac2expr
open EConstr
open Genredexpr
open Misctypes
open Tactypes
open Proofview

(** Redefinition of Ltac1 data structures because of impedance mismatch *)

type explicit_bindings = (quantified_hypothesis * EConstr.t) list

type bindings =
| ImplicitBindings of EConstr.t list
| ExplicitBindings of explicit_bindings
| NoBindings

type constr_with_bindings = EConstr.constr * bindings

type core_destruction_arg =
| ElimOnConstr of constr_with_bindings tactic
| ElimOnIdent of Id.t
| ElimOnAnonHyp of int

type destruction_arg = core_destruction_arg

type intro_pattern =
| IntroForthcoming of bool
| IntroNaming of intro_pattern_naming
| IntroAction of intro_pattern_action
and intro_pattern_naming =
| IntroIdentifier of Id.t
| IntroFresh of Id.t
| IntroAnonymous
and intro_pattern_action =
| IntroWildcard
| IntroOrAndPattern of or_and_intro_pattern
| IntroInjection of intro_pattern list
| IntroApplyOn of EConstr.t tactic * intro_pattern
| IntroRewrite of bool
and or_and_intro_pattern =
| IntroOrPattern of intro_pattern list list
| IntroAndPattern of intro_pattern list

type induction_clause =
  destruction_arg *
  intro_pattern_naming option *
  or_and_intro_pattern option *
  clause option

type rewriting =
  bool option *
  multi *
  constr_with_bindings tactic

(** Local reimplementations of tactics variants from Coq *)

val intros_patterns : evars_flag -> intro_pattern list -> unit tactic

val apply : advanced_flag -> evars_flag ->
  constr_with_bindings tactic list ->
  (Id.t * intro_pattern option) option -> unit tactic

val induction_destruct : rec_flag -> evars_flag ->
  induction_clause list -> constr_with_bindings option -> unit tactic

val elim : evars_flag -> constr_with_bindings -> constr_with_bindings option ->
  unit tactic

val general_case_analysis : evars_flag -> constr_with_bindings ->  unit tactic

val constructor_tac : evars_flag -> int option -> int -> bindings -> unit tactic

val left_with_bindings  : evars_flag -> bindings -> unit tactic
val right_with_bindings : evars_flag -> bindings -> unit tactic
val split_with_bindings : evars_flag -> bindings -> unit tactic

val rewrite :
  evars_flag -> rewriting list -> clause -> unit tactic option -> unit tactic

val forward : bool -> unit tactic option option ->
  intro_pattern option -> constr -> unit tactic

val letin_pat_tac : evars_flag -> (bool * intro_pattern_naming) option ->
  Name.t -> (Evd.evar_map * constr) -> clause -> unit tactic

val simpl : global_reference glob_red_flag ->
  (Pattern.constr_pattern * occurrences_expr) option -> clause -> unit tactic

val cbv : global_reference glob_red_flag -> clause -> unit tactic

val cbn : global_reference glob_red_flag -> clause -> unit tactic

val lazy_ : global_reference glob_red_flag -> clause -> unit tactic

val unfold : (global_reference * occurrences_expr) list -> clause -> unit tactic

val pattern : (constr * occurrences_expr) list -> clause -> unit tactic

val vm : (Pattern.constr_pattern * occurrences_expr) option -> clause -> unit tactic

val native : (Pattern.constr_pattern * occurrences_expr) option -> clause -> unit tactic

val eval_red : constr -> constr tactic

val eval_hnf : constr -> constr tactic

val eval_simpl : global_reference glob_red_flag ->
  (Pattern.constr_pattern * occurrences_expr) option -> constr -> constr tactic

val eval_cbv : global_reference glob_red_flag -> constr -> constr tactic

val eval_cbn : global_reference glob_red_flag -> constr -> constr tactic

val eval_lazy : global_reference glob_red_flag -> constr -> constr tactic

val eval_unfold : (global_reference * occurrences_expr) list -> constr -> constr tactic

val eval_fold : constr list -> constr -> constr tactic

val eval_pattern : (EConstr.t * occurrences_expr) list -> constr -> constr tactic

val eval_vm : (Pattern.constr_pattern * occurrences_expr) option -> constr -> constr tactic

val eval_native : (Pattern.constr_pattern * occurrences_expr) option -> constr -> constr tactic

val discriminate : evars_flag -> destruction_arg option -> unit tactic

val injection : evars_flag -> intro_pattern list option -> destruction_arg option -> unit tactic

val autorewrite : all:bool -> unit tactic option -> Id.t list -> clause -> unit tactic

val trivial : Hints.debug -> constr tactic list -> Id.t list option ->
  unit Proofview.tactic

val auto : Hints.debug -> int option -> constr tactic list ->
  Id.t list option -> unit Proofview.tactic

val new_auto : Hints.debug -> int option -> constr tactic list ->
  Id.t list option -> unit Proofview.tactic

val eauto : Hints.debug -> int option -> int option -> constr tactic list ->
  Id.t list option -> unit Proofview.tactic

val typeclasses_eauto : Class_tactics.search_strategy option -> int option ->
  Id.t list option -> unit Proofview.tactic

val inversion : inversion_kind -> destruction_arg -> intro_pattern option -> Id.t list option -> unit tactic

val contradiction : constr_with_bindings option -> unit tactic

val firstorder : unit Proofview.tactic option -> global_reference list -> Id.t list -> unit tactic
