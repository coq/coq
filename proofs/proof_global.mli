(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines proof facilities relevant to the
     toplevel. In particular it defines the global proof
     environment. *)

val there_are_pending_proofs : unit -> bool
val check_no_pending_proof : unit -> unit

val get_current_proof_name : unit -> Names.Id.t
val get_all_proof_names : unit -> Names.Id.t list

val discard : Names.Id.t Loc.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

exception NoCurrentProof
val give_me_the_proof : unit -> Proof.proof
(** @raise NoCurrentProof when outside proof mode. *)

val compact_the_proof : unit -> unit

(** When a proof is closed, it is reified into a [proof_object], where
    [id] is the name of the proof, [entries] the list of the proof terms
    (in a form suitable for definitions). Together with the [terminator]
    function which takes a [proof_object] together with a [proof_end]
    (i.e. an proof ending command) and registers the appropriate
    values. *)
type lemma_possible_guards = int list list
type proof_universes = Evd.evar_universe_context * Universes.universe_binders option

type proof_object = {
  id : Names.Id.t;
  entries : Safe_typing.private_constants Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: proof_universes;
}

type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry *
		  proof_universes
  | Proved of Vernacexpr.opacity_flag *
              Vernacexpr.lident option *
              proof_object
type proof_terminator
type closed_proof = proof_object * proof_terminator

val make_terminator : (proof_ending -> unit) -> proof_terminator
val apply_terminator : proof_terminator -> proof_ending -> unit

(** [start_proof id str pl goals terminator] starts a proof of name [id]
    with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. The proof is started in the
    evar map [sigma] (which can typically contain universe
    constraints), and with universe bindings pl. *)
val start_proof :
  Evd.evar_map -> Names.Id.t -> ?pl:Univdecls.universe_decl ->
  Decl_kinds.goal_kind -> (Environ.env * EConstr.types) list  ->
    proof_terminator -> unit

(** Like [start_proof] except that there may be dependencies between
    initial goals. *)
val start_dependent_proof :
  Names.Id.t -> ?pl:Univdecls.universe_decl -> Decl_kinds.goal_kind ->
  Proofview.telescope -> proof_terminator -> unit

(** Update the proofs global environment after a side-effecting command
  (e.g. a sublemma definition) has been run inside it. Assumes
  there_are_pending_proofs. *)
val update_global_env : unit -> unit

(* Takes a function to add to the exceptions data relative to the
   state in which the proof was built *)
val close_proof : keep_body_ucst_separate:bool -> Future.fix_exn -> closed_proof

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The former is supposed to be
 * chained with a computation that completed the proof *)

type closed_proof_output = (Term.constr * Safe_typing.private_constants) list * Evd.evar_universe_context

(* If allow_partial is set (default no) then an incomplete proof
 * is allowed (no error), and a warn is given if the proof is complete. *)
val return_proof : ?allow_partial:bool -> unit -> closed_proof_output
val close_future_proof : feedback_id:Stateid.t ->
  closed_proof_output Future.computation -> closed_proof

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
val get_terminator : unit -> proof_terminator
val set_terminator : proof_terminator -> unit

exception NoSuchProof

val get_open_goals : unit -> int

(** Runs a tactic on the current proof. Raises [NoCurrentProof] is there is
    no current proof.
    The return boolean is set to [false] if an unsafe tactic has been used. *)
val with_current_proof :
  (unit Proofview.tactic -> Proof.proof -> Proof.proof*'a) -> 'a
val simple_with_current_proof :
  (unit Proofview.tactic -> Proof.proof -> Proof.proof) -> unit

(** Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : Genarg.glob_generic_argument -> unit

(** Sets the section variables assumed by the proof, returns its closure
 * (w.r.t. type dependencies and let-ins covered by it) + a list of
 * ids to be cleared *)
val set_used_variables :
  Names.Id.t list -> Context.Named.t * Names.Id.t Loc.located list
val get_used_variables : unit -> Context.Named.t option

(** Get the universe declaration associated to the current proof. *)
val get_universe_decl : unit -> Univdecls.universe_decl

module V82 : sig
  val get_current_initial_conclusions : unit -> Names.Id.t *(EConstr.types list *
  Decl_kinds.goal_kind)
end

type state
val freeze : marshallable:[`Yes | `No | `Shallow] -> state
val unfreeze : state -> unit
val proof_of_state : state -> Proof.proof
val copy_terminators : src:state -> tgt:state -> state


(**********************************************************)
(* Proof Mode API                                         *)
(* The current Proof Mode API is deprecated and a new one *)
(* will be (hopefully) defined in 8.8                     *)
(**********************************************************)

(** Type of proof modes :
    - A name
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it 

*)
type proof_mode_name = string
type proof_mode = {
  name : proof_mode_name ;
  set : unit -> unit ;
  reset : unit -> unit
}

(** Registers a new proof mode which can then be adressed by name
    in [set_default_proof_mode].
    One mode is already registered - the standard mode - named "No",
    It corresponds to Coq default setting are they are set when coqtop starts. *)
val register_proof_mode : proof_mode -> unit
(* Can't make this deprecated due to limitations of camlp5 *)
(* [@@ocaml.deprecated "the current proof mode API is deprecated, use with care, see PR #459 and #566 "] *)

val get_default_proof_mode_name : unit -> proof_mode_name
[@@ocaml.deprecated "the current proof mode API is deprecated, use with care, see PR #459 and #566 "]

(** [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
val set_proof_mode : proof_mode_name -> unit
[@@ocaml.deprecated "the current proof mode API is deprecated, use with care, see PR #459 and #566 "]

val activate_proof_mode : proof_mode_name -> unit
[@@ocaml.deprecated "the current proof mode API is deprecated, use with care, see PR #459 and #566 "]

val disactivate_current_proof_mode : unit -> unit
[@@ocaml.deprecated "the current proof mode API is deprecated, use with care, see PR #459 and #566 "]

