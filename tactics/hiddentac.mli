(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Pp
open Term
open Proof_type
open Tacmach
open Genarg
open Tacexpr
open Glob_term
open Evd
open Clenv
open Termops
open Misctypes

(** Tactics for the interpreter. They used to left a trace in the proof tree
   when they are called. *)

(** Basic tactics *)

val h_intro_move      : Id.t option -> Id.t move_location -> tactic
val h_intro           : Id.t -> tactic
val h_intros_until    : quantified_hypothesis -> tactic

val h_assumption      : tactic
val h_exact           : constr -> tactic
val h_exact_no_check  : constr -> tactic
val h_vm_cast_no_check  : constr -> tactic

val h_apply           : advanced_flag -> evars_flag ->
  constr with_bindings located list -> tactic
val h_apply_in        : advanced_flag -> evars_flag ->
  constr with_bindings located list ->
  Id.t * intro_pattern_expr located option -> tactic

val h_elim            : evars_flag -> constr with_bindings ->
                        constr with_bindings option -> tactic
val h_elim_type       : constr -> tactic
val h_case            : evars_flag -> constr with_bindings -> tactic
val h_case_type       : constr -> tactic

val h_mutual_fix      : Id.t -> int ->
                        (Id.t * int * constr) list -> tactic
val h_fix             : Id.t option -> int -> tactic
val h_mutual_cofix    : Id.t -> (Id.t * constr) list -> tactic
val h_cofix           : Id.t option -> tactic

val h_cut             : constr -> tactic
val h_generalize      : constr list -> tactic
val h_generalize_gen  : (constr Locus.with_occurrences * Name.t) list -> tactic
val h_generalize_dep  : ?with_let:bool -> constr -> tactic
val h_let_tac         : letin_flag -> Name.t -> constr -> Locus.clause ->
                        intro_pattern_expr located option -> tactic
val h_let_pat_tac     : letin_flag -> Name.t -> evar_map * constr ->
                        Locus.clause -> intro_pattern_expr located option ->
                        tactic

(** Derived basic tactics *)

val h_simple_induction   : quantified_hypothesis -> tactic
val h_simple_destruct    : quantified_hypothesis -> tactic
val h_simple_induction_destruct : rec_flag -> quantified_hypothesis -> tactic
val h_new_induction   : evars_flag ->
  (evar_map * constr with_bindings) induction_arg ->
  intro_pattern_expr located option * intro_pattern_expr located option ->
  constr with_bindings option ->
  Locus.clause option -> tactic
val h_new_destruct    : evars_flag ->
  (evar_map * constr with_bindings) induction_arg ->
  intro_pattern_expr located option * intro_pattern_expr located option ->
  constr with_bindings option ->
  Locus.clause option -> tactic
val h_induction_destruct : rec_flag -> evars_flag ->
  ((evar_map * constr with_bindings) induction_arg *
   (intro_pattern_expr located option * intro_pattern_expr located option) *
    Locus.clause option) list *
  constr with_bindings option -> tactic

val h_specialize      : int option -> constr with_bindings -> tactic
val h_lapply          : constr -> tactic

(** Automation tactic : see Auto *)


(** Context management *)
val h_clear           : bool -> Id.t list -> tactic
val h_clear_body      : Id.t list -> tactic
val h_move            : bool -> Id.t -> Id.t move_location -> tactic
val h_rename          : (Id.t*Id.t) list -> tactic
val h_revert          : Id.t list -> tactic

(** Constructors *)
val h_constructor     : evars_flag -> int -> constr bindings -> tactic
val h_left            : evars_flag -> constr bindings -> tactic
val h_right           : evars_flag -> constr bindings -> tactic
val h_split           : evars_flag -> constr bindings list -> tactic

val h_one_constructor : int -> tactic
val h_simplest_left   : tactic
val h_simplest_right  : tactic


(** Conversion *)
val h_reduce          : Redexpr.red_expr -> Locus.clause -> tactic
val h_change          :
  Pattern.constr_pattern option -> constr -> Locus.clause -> tactic

(** Equivalence relations *)
val h_reflexivity     : tactic
val h_symmetry        : Locus.clause -> tactic
val h_transitivity    : constr option -> tactic

val h_simplest_apply  : constr -> tactic
val h_simplest_eapply : constr -> tactic
val h_simplest_elim   : constr -> tactic
val h_simplest_case   : constr -> tactic

val h_intro_patterns  : intro_pattern_expr located list -> tactic
