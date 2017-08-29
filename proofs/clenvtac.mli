(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Legacy components of the previous proof engine. *)

open Clenv
open EConstr
open Unification
open Misctypes

(** Tactics *)
val unify : ?flags:unify_flags -> ?with_ho:bool -> constr -> unit Proofview.tactic
val clenv_refine : evars_flag -> ?with_classes:bool -> clausenv -> unit Proofview.tactic
val res_pf : ?with_evars:evars_flag -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic

val clenv_pose_dependent_evars : evars_flag -> clausenv -> clausenv
val clenv_value_cast_meta : clausenv -> constr

(** New clauses *)

val with_clause : constr * types -> (clause -> unit Proofview.tactic) -> unit Proofview.tactic
(** [with_clause (c, t) k] Turn (c, t) into a clause and apply the tactic to it.  *)

val clenv_chain_last : constr -> clause -> unit Proofview.tactic
(** [clenv_chain_last c cl] Coerce [c] with [cl]'s last hole type and
    define it. *)

val clenv_refine2 :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags -> ?origsigma:Evd.evar_map ->
  clause -> unit Proofview.tactic
(** Refine the goal with the given clause:
    - First unify the clause with the goals conclusion, then:
    - If with_classes is true, resolve typeclasses and fail if
    with_evars is false and resolution fails.
    - If with_evars is false, check for remaining dependent subgoals that
    would be introduced by the refinement. Fresh existential variables
    resulting from the pruning of an original one from origsigma
    (due to clearing an hypothesis) are still allowed.
    - If shelve_subgoals is true (the default), dependent subgoals are shelved. *)

val clenv_refine_no_check :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags -> ?origsigma:Evd.evar_map ->
  clause -> unit Proofview.tactic
(** Refine the goal without going through the first step of unification with
    the goal's conclusion. *)

val clenv_refine_bindings :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags ->
  hyps_only:bool -> delay_bindings:bool -> EConstr.constr Misctypes.bindings ->
  ?origsigma:Evd.evar_map -> clause -> unit Proofview.tactic
(** Refine the goal additionally using the given bindings to complete the clause. *)

val clenv_solve_clause_constraints :
  ?flags:unify_flags -> with_ho:bool -> clause -> clause Proofview.tactic
(** Multi-goal tactic to solve the remaining constraints in the current [sigma]
    and advance the clause according to their solution. Fails if there remains
    unsolvable unification constraints. *)

val clenv_check_dep_holes : evars_flag -> Evd.evar_map -> ?origsigma:Evd.evar_map ->
                            clause -> Goal.goal list Proofview.tactic
(** Check that dependent holes do not remain if the evars_flag is false,
    returning the dependent holes as a result. This takes optionally into account
    an original evar_map to check for fresh existentials resulting from pruning
    original ones, which are allowed dependent holes even if evars_flag is false. *)

val clenv_unify_concl : Evarconv.unify_flags -> Clenv.clause ->
                        (Evd.evar_map * Clenv.clause) Ftactic.t
(** Unify a clause with the goal's conclusion and advance it. See [Clenv.clenv_unify_concl].
    This assumes the clause is typable in the focused tactic's sigma *)

(** Debug *)
val debug_print_shelf : string -> unit Proofview.tactic
