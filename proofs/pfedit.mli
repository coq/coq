(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Term
open Context
open Environ
open Decl_kinds
open Tacmach
open Tacexpr

(** Several proofs can be opened simultaneously but at most one is
   focused at some time. The following functions work by side-effect
   on current set of open proofs. In this module, ``proofs'' means an
   open proof (something started by vernacular command [Goal], [Lemma]
   or [Theorem]), and ``goal'' means a subgoal of the current focused
   proof *)

(** {6 ... } *)
(** [refining ()] tells if there is some proof in progress, even if a not
   focused one *)

val refining : unit -> bool

(** [check_no_pending_proofs ()] fails if there is still some proof in
   progress *)

val check_no_pending_proofs : unit -> unit

(** {6 ... } *)
(** [delete_proof name] deletes proof of name [name] or fails if no proof
    has this name *)

val delete_proof : Id.t located -> unit

(** [delete_current_proof ()] deletes current focused proof or fails if
    no proof is focused *)

val delete_current_proof : unit -> unit

(** [delete_all_proofs ()] deletes all open proofs if any *)

val delete_all_proofs : unit -> unit

(** {6 ... } *)
(** [start_proof s str env t hook tac] starts a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism); init_tac is possibly a tactic to
    systematically apply at initialization time (e.g. to start the
    proof of mutually dependent theorems) *)

type lemma_possible_guards = Proof_global.lemma_possible_guards

val start_proof :
  Id.t -> goal_kind -> named_context_val -> constr ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:lemma_possible_guards -> 
  unit declaration_hook -> unit

(** {6 ... } *)
(** [cook_proof opacity] turns the current proof (assumed completed) into
    a constant with its name, kind and possible hook (see [start_proof]);
    it fails if there is no current proof of if it is not completed;
    it also tells if the guardness condition has to be inferred. *)

val cook_this_proof : (Proof.proof -> unit) ->
    Id.t *
    (Entries.definition_entry list *
    lemma_possible_guards *
    Decl_kinds.goal_kind *
    unit Tacexpr.declaration_hook Ephemeron.key) ->
  Id.t *
    (Entries.definition_entry * lemma_possible_guards * goal_kind *
     unit declaration_hook Ephemeron.key)

val cook_proof : (Proof.proof -> unit) ->
  Id.t *
    (Entries.definition_entry * lemma_possible_guards * goal_kind *
     unit declaration_hook Ephemeron.key)

(** {6 ... } *)
(** [get_pftreestate ()] returns the current focused pending proof.
   @raise NoCurrentProof if there is no pending proof. *)

val get_pftreestate : unit -> Proof.proof

(** [get_goal_context n] returns the context of the [n]th subgoal of
   the current focused proof or raises a [UserError] if there is no
   focused proof or if there is no more subgoals *)

val get_goal_context : int -> Evd.evar_map * env

(** [get_current_goal_context ()] works as [get_goal_context 1] *)

val get_current_goal_context : unit -> Evd.evar_map * env

(** [current_proof_statement] *)

val current_proof_statement :
  unit -> Id.t * goal_kind * types * unit declaration_hook Ephemeron.key

(** {6 ... } *)
(** [get_current_proof_name ()] return the name of the current focused
    proof or failed if no proof is focused *)

val get_current_proof_name : unit -> Id.t

(** [get_all_proof_names ()] returns the list of all pending proof names.
    The first name is the current proof, the other names may come in
    any order. *)

val get_all_proof_names : unit -> Id.t list

(** {6 ... } *)
(** [set_end_tac tac] applies tactic [tac] to all subgoal generate
    by [solve_nth] *)

val set_end_tac : Tacexpr.raw_tactic_expr -> unit

(** {6 ... } *)
(** [set_used_variables l] declares that section variables [l] will be
    used in the proof *)
val set_used_variables : Id.t list -> unit
val get_used_variables : unit -> Context.section_context option

(** {6 ... } *)
(** [solve_nth n tac] applies tactic [tac] to the [n]th subgoal of the
   current focused proof or raises a UserError if no proof is focused or
   if there is no [n]th subgoal *)

val solve_nth : ?with_end_tac:unit Proofview.tactic -> int -> unit Proofview.tactic ->
      Proof.proof -> Proof.proof*bool

(** [by tac] applies tactic [tac] to the 1st subgoal of the current
   focused proof or raises a UserError if there is no focused proof or
   if there is no more subgoals.
   Returns [false] if an unsafe tactic has been used. *)

val by : unit Proofview.tactic -> bool

(** [instantiate_nth_evar_com n c] instantiate the [n]th undefined
   existential variable of the current focused proof by [c] or raises a
   UserError if no proof is focused or if there is no such [n]th
   existential variable *)

val instantiate_nth_evar_com : int -> Constrexpr.constr_expr -> unit

(** [build_by_tactic typ tac] returns a term of type [typ] by calling
    [tac]. The return boolean, if [false] indicates the use of an unsafe
    tactic. *)

val build_constant_by_tactic :
  Id.t -> named_context_val -> ?goal_kind:goal_kind ->
    types -> unit Proofview.tactic -> Entries.definition_entry * bool
val build_by_tactic : env -> types -> unit Proofview.tactic -> constr * bool

(** Declare the default tactic to fill implicit arguments *)

val declare_implicit_tactic : unit Proofview.tactic -> unit

(* Raise Exit if cannot solve *)
val solve_by_implicit_tactic : env -> Evd.evar_map -> Evd.evar -> constr
