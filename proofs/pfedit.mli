(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Global proof state. A quite redundant wrapper on {!Proof_global}. *)

open Loc
open Names
open Term
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
  Id.t -> ?pl:Proof_global.universe_binders -> goal_kind -> Evd.evar_map -> named_context_val -> EConstr.constr ->
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
    (Safe_typing.private_constants Entries.definition_entry * Proof_global.proof_universes * goal_kind))

val cook_proof : unit ->
  (Id.t *
    (Safe_typing.private_constants Entries.definition_entry * Proof_global.proof_universes * goal_kind))

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

val get_current_context : unit -> Evd.evar_map * env

(** [current_proof_statement] *)

val current_proof_statement :
  unit -> Id.t * goal_kind * EConstr.types

(** {6 ... } *)
(** [solve (SelectNth n) tac] applies tactic [tac] to the [n]th
    subgoal of the current focused proof or raises a [UserError] if no
    proof is focused or if there is no [n]th subgoal. [solve SelectAll
    tac] applies [tac] to all subgoals. *)

val solve : ?with_end_tac:unit Proofview.tactic ->
      Vernacexpr.goal_selector -> int option -> unit Proofview.tactic ->
      Proof.proof -> Proof.proof*bool

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
  Id.t -> Evd.evar_universe_context -> named_context_val -> ?goal_kind:goal_kind ->
  EConstr.types -> unit Proofview.tactic -> 
  Safe_typing.private_constants Entries.definition_entry * bool *
    Evd.evar_universe_context

val build_by_tactic : ?side_eff:bool -> env -> Evd.evar_universe_context -> ?poly:polymorphic ->
  EConstr.types -> unit Proofview.tactic -> 
  constr * bool * Evd.evar_universe_context

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

(** {5 Deprecated functions in favor of [Proof_global]} *)

(** {6 ... } *)
(** Several proofs can be opened simultaneously but at most one is
   focused at some time. The following functions work by side-effect
   on current set of open proofs. In this module, ``proofs'' means an
   open proof (something started by vernacular command [Goal], [Lemma]
   or [Theorem]), and ``goal'' means a subgoal of the current focused
   proof *)

(** [refining ()] tells if there is some proof in progress, even if a not
   focused one *)

val refining : unit -> bool
[@@ocaml.deprecated "use Proof_global.there_are_pending_proofs"]

(** [check_no_pending_proofs ()] fails if there is still some proof in
   progress *)

val check_no_pending_proofs : unit -> unit
[@@ocaml.deprecated "use Proof_global.check_no_pending_proofs"]

(** {6 ... } *)
(** [delete_proof name] deletes proof of name [name] or fails if no proof
    has this name *)

val delete_proof : Id.t located -> unit
[@@ocaml.deprecated "use Proof_global.discard"]

(** [delete_current_proof ()] deletes current focused proof or fails if
    no proof is focused *)

val delete_current_proof : unit -> unit
[@@ocaml.deprecated "use Proof_global.discard_current"]

(** [delete_all_proofs ()] deletes all open proofs if any *)
val delete_all_proofs : unit -> unit
[@@ocaml.deprecated "use Proof_global.discard_all"]

(** [get_pftreestate ()] returns the current focused pending proof.
   @raise NoCurrentProof if there is no pending proof. *)

val get_pftreestate : unit -> Proof.proof
[@@ocaml.deprecated "use Proof_global.give_me_the_proof"]

(** {6 ... } *)
(** [set_end_tac tac] applies tactic [tac] to all subgoal generate
    by [solve] *)

val set_end_tac : Genarg.glob_generic_argument -> unit
[@@ocaml.deprecated "use Proof_global.set_endline_tactic"]

(** {6 ... } *)
(** [set_used_variables l] declares that section variables [l] will be
    used in the proof *)
val set_used_variables :
  Id.t list -> Context.Named.t * Names.Id.t Loc.located list
[@@ocaml.deprecated "use Proof_global.set_used_variables"]

val get_used_variables : unit -> Context.Named.t option
[@@ocaml.deprecated "use Proof_global.get_used_variables"]

(** {6 Universe binders } *)
val get_universe_binders : unit -> Proof_global.universe_binders option
[@@ocaml.deprecated "use Proof_global.get_universe_binders"]

(** {6 ... } *)
(** [get_current_proof_name ()] return the name of the current focused
    proof or failed if no proof is focused *)
val get_current_proof_name : unit -> Id.t
[@@ocaml.deprecated "use Proof_global.get_current_proof_name"]

(** [get_all_proof_names ()] returns the list of all pending proof names.
    The first name is the current proof, the other names may come in
    any order. *)
val get_all_proof_names : unit -> Id.t list
[@@ocaml.deprecated "use Proof_global.get_all_proof_names"]

type lemma_possible_guards = Proof_global.lemma_possible_guards
[@@ocaml.deprecated "use Proof_global.lemma_possible_guards"]

type universe_binders = Proof_global.universe_binders
[@@ocaml.deprecated "use Proof_global.universe_binders"]

