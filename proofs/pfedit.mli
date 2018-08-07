(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
open Decl_kinds

(** {6 ... } *)
(** [start_proof s str env t hook tac] starts a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism); init_tac is possibly a tactic to
    systematically apply at initialization time (e.g. to start the
    proof of mutually dependent theorems) *)

val start_proof :
  Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map -> named_context_val -> EConstr.constr ->
  ?init_tac:unit Proofview.tactic ->
  Proof_global.proof_terminator -> unit

(** {6 ... } *)
(** [cook_proof opacity] turns the current proof (assumed completed) into
    a constant with its name, kind and possible hook (see [start_proof]);
    it fails if there is no current proof of if it is not completed;
    it also tells if the guardness condition has to be inferred. *)

val cook_this_proof :
    Proof_global.proof_object ->
  (Id.t *
    (Safe_typing.private_constants Entries.definition_entry * UState.t * goal_kind))

val cook_proof : unit ->
  (Id.t *
    (Safe_typing.private_constants Entries.definition_entry * UState.t * goal_kind))

(** {6 ... } *)
(** [get_goal_context n] returns the context of the [n]th subgoal of
   the current focused proof or raises a [UserError] if there is no
   focused proof or if there is no more subgoals *)

val get_goal_context : int -> Evd.evar_map * env

(** [get_current_goal_context ()] works as [get_goal_context 1] *)

val get_current_goal_context : unit -> Evd.evar_map * env

(** [get_current_context ()] returns the context of the
  current focused goal. If there is no focused goal but there
  is a proof in progress, it returns the corresponding evar_map.
  If there is no pending proof then it returns the current global
  environment and empty evar_map. *)

val get_current_context : ?p:Proof.t -> unit -> Evd.evar_map * env

(** [current_proof_statement] *)

val current_proof_statement :
  unit -> Id.t * goal_kind * EConstr.types

(** {6 ... } *)

(** [solve (SelectNth n) tac] applies tactic [tac] to the [n]th
    subgoal of the current focused proof or raises a [UserError] if no
    proof is focused or if there is no [n]th subgoal. [solve SelectAll
    tac] applies [tac] to all subgoals. *)

val solve : ?with_end_tac:unit Proofview.tactic ->
      Goal_select.t -> int option -> unit Proofview.tactic ->
      Proof.t -> Proof.t * bool

(** [by tac] applies tactic [tac] to the 1st subgoal of the current
    focused proof or raises a UserError if there is no focused proof or
    if there is no more subgoals.
    Returns [false] if an unsafe tactic has been used. *)

val by : unit Proofview.tactic -> bool

(** Option telling if unification heuristics should be used. *)
val use_unification_heuristics : unit -> bool

(** [instantiate_nth_evar_com n c] instantiate the [n]th undefined
   existential variable of the current focused proof by [c] or raises a
   UserError if no proof is focused or if there is no such [n]th
   existential variable *)

val instantiate_nth_evar_com : int -> Constrexpr.constr_expr -> unit

(** [build_by_tactic typ tac] returns a term of type [typ] by calling
    [tac]. The return boolean, if [false] indicates the use of an unsafe
    tactic. *)

val build_constant_by_tactic :
  Id.t -> UState.t -> named_context_val -> ?goal_kind:goal_kind ->
  EConstr.types -> unit Proofview.tactic -> 
  Safe_typing.private_constants Entries.definition_entry * bool *
    UState.t

val build_by_tactic : ?side_eff:bool -> env -> UState.t -> ?poly:polymorphic ->
  EConstr.types -> unit Proofview.tactic -> 
  constr * bool * UState.t

val refine_by_tactic : env -> Evd.evar_map -> EConstr.types -> unit Proofview.tactic ->
  constr * Evd.evar_map
(** A variant of the above function that handles open terms as well.
    Caveat: all effects are purged in the returned term at the end, but other
    evars solved by side-effects are NOT purged, so that unexpected failures may
    occur. Ideally all code using this function should be rewritten in the
    monad. *)

(** Declare the default tactic to fill implicit arguments *)

val declare_implicit_tactic : unit Proofview.tactic -> unit

(** To remove the default tactic *)
val clear_implicit_tactic : unit -> unit

(* Raise Exit if cannot solve *)
val solve_by_implicit_tactic : unit -> Pretyping.inference_hook option
