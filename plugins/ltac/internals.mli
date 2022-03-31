(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Proofview
open Ltac_pretype

(** Implementation of Ltac-specific code to be exported in mlg files.

    This is voluntarily undocumented. Please do not use in plugin code. *)

(** {5 Tactics} *)

val assert_succeeds : unit Proofview.tactic -> unit Proofview.tactic

val mytclWithHoles : (Tactics.evars_flag ->
  EConstr.constr Tactypes.with_bindings Tactics.destruction_arg option ->
    unit Proofview.tactic) ->
  Tactics.evars_flag ->
  Tactypes.delayed_open_constr_with_bindings Tactics.destruction_arg ->
  unit Proofview.tactic

val with_delayed_uconstr : Tacinterp.interp_sign ->
  closed_glob_constr -> (EConstr.constr -> unit tactic) -> unit tactic
val replace_in_clause_maybe_by : Tacinterp.interp_sign ->
  closed_glob_constr -> EConstr.constr ->
  Locus.clause -> Tacinterp.Value.t option -> unit tactic
val replace_term : Geninterp.interp_sign -> bool option -> closed_glob_constr ->
  Locus.clause -> unit tactic

val discrHyp : Names.Id.t -> unit tactic
val injHyp : Names.Id.t -> unit tactic
(* TODO: remove these, they are not used from within Coq *)

val refine_tac : Tacinterp.interp_sign -> simple:bool -> with_classes:bool ->
  closed_glob_constr -> unit tactic

val hResolve : Id.t -> EConstr.t -> int -> EConstr.t -> unit tactic
val hResolve_auto : Id.t -> EConstr.t -> EConstr.t -> unit tactic

val destauto : unit tactic
val destauto_in : Id.t -> unit tactic

val has_evar : EConstr.t -> unit tactic
val is_evar : EConstr.t -> unit tactic
val is_var : EConstr.t -> unit tactic
val is_fix : EConstr.t -> unit tactic
val is_cofix : EConstr.t -> unit tactic
val is_ind : EConstr.t -> unit tactic
val is_constructor : EConstr.t -> unit tactic
val is_proj : EConstr.t -> unit tactic
val is_const : EConstr.t -> unit tactic

val unshelve : Tacinterp.interp_sign -> Tacinterp.Value.t -> unit tactic

val decompose : EConstr.t list -> EConstr.t -> unit tactic

val tclOPTIMIZE_HEAP : unit tactic

val onSomeWithHoles : ('a option -> unit tactic) -> 'a Tactypes.delayed_open option -> unit tactic

val exact : Geninterp.interp_sign -> Ltac_pretype.closed_glob_constr -> unit Proofview.tactic

(** {5 Commands} *)

val declare_equivalent_keys : Constrexpr.constr_expr -> Constrexpr.constr_expr -> unit

val infoH : pstate:Declare.Proof.t -> Tacexpr.raw_tactic_expr -> unit
(** ProofGeneral command *)
