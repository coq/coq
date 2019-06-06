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
open EConstr
open Genredexpr
open Tac2types
open Proofview

(** Local reimplementations of tactics variants from Coq *)

val intros_patterns : evars_flag -> intro_pattern list -> unit tactic

val apply : advanced_flag -> evars_flag ->
  constr_with_bindings thunk list ->
  (Id.t * intro_pattern option) option -> unit tactic

val induction_destruct : rec_flag -> evars_flag ->
  induction_clause list -> constr_with_bindings option -> unit tactic

val elim : evars_flag -> constr_with_bindings -> constr_with_bindings option ->
  unit tactic

val general_case_analysis : evars_flag -> constr_with_bindings ->  unit tactic

val generalize : (constr * occurrences * Name.t) list -> unit tactic

val constructor_tac : evars_flag -> int option -> int -> bindings -> unit tactic

val left_with_bindings  : evars_flag -> bindings -> unit tactic
val right_with_bindings : evars_flag -> bindings -> unit tactic
val split_with_bindings : evars_flag -> bindings -> unit tactic

val specialize : constr_with_bindings -> intro_pattern option -> unit tactic

val change : Pattern.constr_pattern option -> (constr array, constr) Tac2ffi.fun1 -> clause -> unit tactic

val rewrite :
  evars_flag -> rewriting list -> clause -> unit thunk option -> unit tactic

val symmetry : clause -> unit tactic

val forward : bool -> unit tactic option option ->
  intro_pattern option -> constr -> unit tactic

val assert_ : assertion -> unit tactic

val letin_pat_tac : evars_flag -> (bool * intro_pattern_naming) option ->
  Name.t -> (Evd.evar_map * constr) -> clause -> unit tactic

val reduce : Redexpr.red_expr -> clause -> unit tactic

val simpl : GlobRef.t glob_red_flag ->
  (Pattern.constr_pattern * occurrences) option -> clause -> unit tactic

val cbv : GlobRef.t glob_red_flag -> clause -> unit tactic

val cbn : GlobRef.t glob_red_flag -> clause -> unit tactic

val lazy_ : GlobRef.t glob_red_flag -> clause -> unit tactic

val unfold : (GlobRef.t * occurrences) list -> clause -> unit tactic

val pattern : (constr * occurrences) list -> clause -> unit tactic

val vm : (Pattern.constr_pattern * occurrences) option -> clause -> unit tactic

val native : (Pattern.constr_pattern * occurrences) option -> clause -> unit tactic

val eval_red : constr -> constr tactic

val eval_hnf : constr -> constr tactic

val eval_simpl : GlobRef.t glob_red_flag ->
  (Pattern.constr_pattern * occurrences) option -> constr -> constr tactic

val eval_cbv : GlobRef.t glob_red_flag -> constr -> constr tactic

val eval_cbn : GlobRef.t glob_red_flag -> constr -> constr tactic

val eval_lazy : GlobRef.t glob_red_flag -> constr -> constr tactic

val eval_unfold : (GlobRef.t * occurrences) list -> constr -> constr tactic

val eval_fold : constr list -> constr -> constr tactic

val eval_pattern : (EConstr.t * occurrences) list -> constr -> constr tactic

val eval_vm : (Pattern.constr_pattern * occurrences) option -> constr -> constr tactic

val eval_native : (Pattern.constr_pattern * occurrences) option -> constr -> constr tactic

val discriminate : evars_flag -> destruction_arg option -> unit tactic

val injection : evars_flag -> intro_pattern list option -> destruction_arg option -> unit tactic

val autorewrite : all:bool -> unit thunk option -> Id.t list -> clause -> unit tactic

val trivial : Hints.debug -> constr thunk list -> Id.t list option ->
  unit Proofview.tactic

val auto : Hints.debug -> int option -> constr thunk list ->
  Id.t list option -> unit Proofview.tactic

val new_auto : Hints.debug -> int option -> constr thunk list ->
  Id.t list option -> unit Proofview.tactic

val eauto : Hints.debug -> int option -> int option -> constr thunk list ->
  Id.t list option -> unit Proofview.tactic

val typeclasses_eauto : Class_tactics.search_strategy option -> int option ->
  Id.t list option -> unit Proofview.tactic

val inversion : Inv.inversion_kind -> destruction_arg -> intro_pattern option -> Id.t list option -> unit tactic

val contradiction : constr_with_bindings option -> unit tactic
