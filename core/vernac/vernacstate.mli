(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Parser : sig
  type t

  val init : unit -> t
  val cur_state : unit -> t

  val parse : t -> 'a Pcoq.Entry.t -> Pcoq.Parsable.t -> 'a

end

(** System State *)
module System : sig

  (** The system state includes the summary and the libobject  *)
  type t

  (** [protect f x] runs [f x] and discards changes in the system state  *)
  val protect : ('a -> 'b) -> 'a -> 'b

end

module LemmaStack : sig

  type t

  val pop : t -> Declare.Proof.t * t option
  val push : t option -> Declare.Proof.t -> t

  val map : f:(Declare.Proof.t -> Declare.Proof.t) -> t -> t
  val map_top : f:(Declare.Proof.t -> Declare.Proof.t) -> t -> t
  val with_top : t -> f:(Declare.Proof.t -> 'a ) -> 'a
  val get_top : t -> Declare.Proof.t

end

type t =
  { parsing : Parser.t
  (** parsing state [parsing state may not behave 100% functionally yet, beware] *)
  ; system  : System.t
  (** summary + libstack *)
  ; lemmas  : LemmaStack.t option
  (** proofs of lemmas currently opened *)
  ; program : Declare.OblState.t NeList.t
  (** program mode table. One per open module/section including the toplevel module. *)
  ; opaques : Opaques.Summary.t
  (** qed-terminated proofs *)
  ; shallow : bool
  (** is the state trimmed down (libstack) *)
  }

val freeze_interp_state : marshallable:bool -> t
val unfreeze_interp_state : t -> unit

(* WARNING: Do not use, it will go away in future releases *)
val invalidate_cache : unit -> unit

(** STM-specific state handling *)
module Stm : sig

  (** Proof state + meta/evar counters *)
  type pstate

  val pstate : t -> pstate
  val set_pstate : t -> pstate -> t

  (** Rest of the state, unfortunately this is used in low-level so we need to expose it *)
  type non_pstate = Summary.frozen * Lib.frozen
  val non_pstate : t -> non_pstate

  (** Checks if two states have the same Environ.env (physical eq) *)
  val same_env : t -> t -> bool

  (** Call [Lib.drop_objects] on the state *)
  val make_shallow : t -> t
end

(* Compatibility module: Do Not Use *)
module Declare : sig

  exception NoCurrentProof

  val there_are_pending_proofs : unit -> bool
  val get_open_goals : unit -> int

  val give_me_the_proof : unit -> Proof.t
  val give_me_the_proof_opt : unit -> Proof.t option
  val get_current_proof_name : unit -> Names.Id.t

  val map_proof : (Proof.t -> Proof.t) -> unit
  val with_current_proof :
      (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> 'a

  val return_proof : unit -> Declare.Proof.closed_proof_output
  val return_partial_proof : unit -> Declare.Proof.closed_proof_output

  val close_future_proof
    : feedback_id:Stateid.t
    -> Declare.Proof.closed_proof_output Future.computation
    -> Declare.Proof.proof_object

  val close_proof
    : opaque:Vernacexpr.opacity_flag
    -> keep_body_ucst_separate:bool
    -> Declare.Proof.proof_object

  val discard_all : unit -> unit
  val update_sigma_univs : UGraph.t -> unit

  val get_current_context : unit -> Evd.evar_map * Environ.env

  val get_all_proof_names : unit -> Names.Id.t list

  val copy_terminators : src:LemmaStack.t option -> tgt:LemmaStack.t option -> LemmaStack.t option

  (* Low-level stuff *)
  val get : unit -> LemmaStack.t option
  val get_program : unit -> Declare.OblState.t NeList.t
  val set : LemmaStack.t option * Declare.OblState.t NeList.t -> unit

  val get_pstate : unit -> Declare.Proof.t option

  val freeze : marshallable:bool -> LemmaStack.t option
  val unfreeze : LemmaStack.t -> unit

end
[@@ocaml.deprecated "This module is internal and should not be used, instead, thread the proof state"]
