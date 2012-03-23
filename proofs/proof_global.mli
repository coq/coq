(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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

val there_is_a_proof : unit -> bool
val there_are_pending_proofs : unit -> bool
val check_no_pending_proof : unit -> unit

val get_current_proof_name : unit -> Names.identifier
val get_all_proof_names : unit -> Names.identifier list

val discard : Names.identifier Pp.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

(** [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
val set_proof_mode : string -> unit

exception NoCurrentProof
val give_me_the_proof : unit -> Proof.proof


(** [start_proof s str goals ~init_tac ~compute_guard hook] starts 
    a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism). *)
type lemma_possible_guards = int list list
val start_proof : Names.identifier -> 
                          Decl_kinds.goal_kind ->
                          (Environ.env * Term.types) list  ->
                          ?compute_guard:lemma_possible_guards -> 
                          unit Tacexpr.declaration_hook -> 
                          unit

val close_proof : unit -> 
                           Names.identifier * 
                          (Entries.definition_entry list * 
			    lemma_possible_guards * 
			    Decl_kinds.goal_kind * 
			    unit Tacexpr.declaration_hook)

exception NoSuchProof

(** Runs a tactic on the current proof. Raises [NoCurrentProof] is there is 
   no current proof. *)
val run_tactic : unit Proofview.tactic -> unit

(** Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : unit Proofview.tactic -> unit

(** Sets the section variables assumed by the proof *)
val set_used_variables : Names.identifier list -> unit
val get_used_variables : unit -> Sign.section_context option

(** Appends the endline tactic of the current proof to a tactic. *)
val with_end_tac : unit Proofview.tactic -> unit Proofview.tactic

(**********************************************************)
(*                                                                                                  *)
(*                              Utility functions                                          *)
(*                                                                                                  *)
(**********************************************************)

(** [maximal_unfocus k p] unfocuses [p] until [p] has at least a
    focused goal or that the last focus isn't of kind [k]. *)
val maximal_unfocus : 'a Proof.focus_kind -> Proof.proof -> unit

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet : sig
  type t = Vernacexpr.bullet

  (** A [behavior] is the data of a put function which
      is called when a bullet prefixes a tactic, together
      with a name to identify it. *)
  type behavior = {
    name : string;
    put : Proof.proof -> t -> unit
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
  val put : Proof.proof -> t -> unit
end

module V82 : sig
  val get_current_initial_conclusions : unit -> Names.identifier *(Term.types list * Decl_kinds.goal_kind * unit Tacexpr.declaration_hook)
end
