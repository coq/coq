(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global proof state. A quite redundant wrapper on {!Proof_global}. *)

open Names
open Constr
open Environ

(** {6 ... } *)

exception NoSuchGoal

(** [get_goal_context n] returns the context of the [n]th subgoal of
   the current focused proof or raises a [UserError] if there is no
   focused proof or if there is no more subgoals *)

val get_goal_context : Proof_global.t -> int -> Evd.evar_map * env

(** [get_current_goal_context ()] works as [get_goal_context 1] *)
val get_current_goal_context : Proof_global.t -> Evd.evar_map * env

(** [get_current_context ()] returns the context of the
  current focused goal. If there is no focused goal but there
  is a proof in progress, it returns the corresponding evar_map.
  If there is no pending proof then it returns the current global
  environment and empty evar_map. *)
val get_current_context : Proof_global.t -> Evd.evar_map * env

(** {6 ... } *)

(** [solve (SelectNth n) tac] applies tactic [tac] to the [n]th
    subgoal of the current focused proof. [solve SelectAll
    tac] applies [tac] to all subgoals. *)

val solve : ?with_end_tac:unit Proofview.tactic ->
      Goal_select.t -> int option -> unit Proofview.tactic ->
      Proof.t -> Proof.t * bool

(** [by tac] applies tactic [tac] to the 1st subgoal of the current
    focused proof.
    Returns [false] if an unsafe tactic has been used. *)

val by : unit Proofview.tactic -> Proof_global.t -> Proof_global.t * bool

(** Option telling if unification heuristics should be used. *)
val use_unification_heuristics : unit -> bool

(** [build_by_tactic typ tac] returns a term of type [typ] by calling
    [tac]. The return boolean, if [false] indicates the use of an unsafe
    tactic. *)

val build_constant_by_tactic
  :  name:Id.t
  -> UState.t
  -> named_context_val
  -> poly:bool
  -> EConstr.types
  -> unit Proofview.tactic
  -> Evd.side_effects Proof_global.proof_entry * bool * UState.t

val build_by_tactic
  :  ?side_eff:bool
  -> env
  -> UState.t
  -> poly:bool
  -> EConstr.types
  -> unit Proofview.tactic
  -> constr * bool * UState.t

val refine_by_tactic
  :  name:Id.t
  -> poly:bool
  -> env -> Evd.evar_map
  -> EConstr.types
  -> unit Proofview.tactic
  -> constr * Evd.evar_map
(** A variant of the above function that handles open terms as well.
    Caveat: all effects are purged in the returned term at the end, but other
    evars solved by side-effects are NOT purged, so that unexpected failures may
    occur. Ideally all code using this function should be rewritten in the
    monad. *)
