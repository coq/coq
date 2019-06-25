(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Parser : sig
  type state

  val init : unit -> state
  val cur_state : unit -> state

  val parse : state -> 'a Pcoq.Entry.t -> Pcoq.Parsable.t -> 'a

end

type t =
  { parsing : Parser.state
  ; system  : States.state          (* summary + libstack *)
  ; lemmas  : Lemmas.Stack.t option (* proofs of lemmas currently opened *)
  ; shallow : bool                  (* is the state trimmed down (libstack) *)
  }

val freeze_interp_state : marshallable:bool -> t
val unfreeze_interp_state : t -> unit

val make_shallow : t -> t

(* WARNING: Do not use, it will go away in future releases *)
val invalidate_cache : unit -> unit

(* Compatibility module: Do Not Use *)
module Proof_global : sig

  exception NoCurrentProof

  val there_are_pending_proofs : unit -> bool
  val get_open_goals : unit -> int

  val give_me_the_proof : unit -> Proof.t
  val give_me_the_proof_opt : unit -> Proof.t option
  val get_current_proof_name : unit -> Names.Id.t

  val map_proof : (Proof.t -> Proof.t) -> unit
  val with_current_proof :
      (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> 'a

  val return_proof : ?allow_partial:bool -> unit -> Proof_global.closed_proof_output

  type closed_proof = Proof_global.proof_object * Lemmas.Info.t

  val close_future_proof :
    opaque:Proof_global.opacity_flag ->
    feedback_id:Stateid.t ->
    Proof_global.closed_proof_output Future.computation -> closed_proof

  val close_proof : opaque:Proof_global.opacity_flag -> keep_body_ucst_separate:bool -> Future.fix_exn -> closed_proof

  val discard_all : unit -> unit
  val update_global_env : unit -> unit

  val get_current_context : unit -> Evd.evar_map * Environ.env

  val get_all_proof_names : unit -> Names.Id.t list

  val copy_terminators : src:Lemmas.Stack.t option -> tgt:Lemmas.Stack.t option -> Lemmas.Stack.t option

  (* Handling of the imperative state *)
  type t = Lemmas.Stack.t

  (* Low-level stuff *)
  val get : unit -> t option
  val set : t option -> unit

  val get_pstate : unit -> Proof_global.t option

  val freeze : marshallable:bool -> t option
  val unfreeze : t -> unit

end
[@@ocaml.deprecated "This module is internal and should not be used, instead, thread the proof state"]
