(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines proof facilities relevant to the
     toplevel. In particular it defines the global proof
     environment. *)

(** Type of proof modes :
    - A name
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it 

*)
type proof_mode = {
  name : string ;
  set : unit -> unit ;
  reset : unit -> unit
}

(** Registers a new proof mode which can then be adressed by name
    in [set_default_proof_mode].
    One mode is already registered - the standard mode - named "No",
    It corresponds to Coq default setting are they are set when coqtop starts. *)
val register_proof_mode : proof_mode -> unit

val there_are_pending_proofs : unit -> bool
val check_no_pending_proof : unit -> unit

val get_current_proof_name : unit -> Names.Id.t
val get_all_proof_names : unit -> Names.Id.t list

val discard : Names.Id.t Loc.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

(** [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
val set_proof_mode : string -> unit

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
type proof_universes = Evd.evar_universe_context
type proof_object = {
  id : Names.Id.t;
  entries : Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: proof_universes;
  (* constraints : Univ.constraints; *)
  (** guards : lemma_possible_guards; *)
}

type proof_ending =
  | Admitted
  | Proved of Vernacexpr.opacity_flag *
             (Vernacexpr.lident * Decl_kinds.theorem_kind option) option *
              proof_object
type proof_terminator = proof_ending -> unit
type closed_proof = proof_object * proof_terminator

(** [start_proof id str goals terminator] starts a proof of name [id]
    with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. *)
val start_proof :
  Evd.evar_map -> Names.Id.t -> Decl_kinds.goal_kind -> (Environ.env * Term.types) list  ->
    proof_terminator -> unit

(** Like [start_proof] except that there may be dependencies between
    initial goals. *)
val start_dependent_proof :
  Names.Id.t -> Decl_kinds.goal_kind -> Proofview.telescope  ->
    proof_terminator -> unit

(* Takes a function to add to the exceptions data relative to the
   state in which the proof was built *)
val close_proof : keep_body_ucst_sepatate:bool -> Future.fix_exn -> closed_proof

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The formes is supposed to be
 * chained with a computation that completed the proof *)

type closed_proof_output = (Term.constr * Declareops.side_effects) list * Evd.evar_universe_context

val return_proof : unit -> closed_proof_output
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
val set_endline_tactic : Tacexpr.raw_tactic_expr -> unit
val set_interp_tac :
  (Tacexpr.raw_tactic_expr -> unit Proofview.tactic)
    -> unit

(** Sets the section variables assumed by the proof, returns its closure
 * (w.r.t. type dependencies *)
val set_used_variables : Names.Id.t list -> Context.section_context
val get_used_variables : unit -> Context.section_context option

(**********************************************************)
(*                                                        *)
(*                            Proof modes                 *)
(*                                                        *)
(**********************************************************)


val activate_proof_mode : string -> unit
val disactivate_proof_mode : string -> unit

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet : sig
  type t = Vernacexpr.bullet

  (** A [behavior] is the data of a put function which
      is called when a bullet prefixes a tactic, a suggest function
      suggesting the right bullet to use on a given proof, together
      with a name to identify the behavior. *)
  type behavior = {
    name : string;
    put : Proof.proof -> t -> Proof.proof;
    suggest: Proof.proof -> string option
  }

  (** A registered behavior can then be accessed in Coq
      through the command [Set Bullet Behavior "name"].

      Two modes are registered originally:
      * "Strict Subproofs":
        - If this bullet follows another one of its kind, defocuses then focuses
          (which fails if the focused subproof is not complete).
        - If it is the first bullet of its kind, then focuses a new subproof.
      * "None": bullets don't do anything *)
  val register_behavior : behavior -> unit

  (** Handles focusing/defocusing with bullets:
       *)
  val put : Proof.proof -> t -> Proof.proof
  val suggest : Proof.proof -> string option
end


(**********************************************************)
(*                                                        *)
(*                     Default goal selector              *)
(*                                                        *)
(**********************************************************)

val get_default_goal_selector : unit -> Vernacexpr.goal_selector

module V82 : sig
  val get_current_initial_conclusions : unit -> Names.Id.t *(Term.types list *
  Decl_kinds.goal_kind)
end

type state
val freeze : marshallable:[`Yes | `No | `Shallow] -> state
val unfreeze : state -> unit
val proof_of_state : state -> Proof.proof
