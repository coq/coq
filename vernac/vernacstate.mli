(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  system  : States.state;          (* summary + libstack *)
  proof   : Proof_global.t option; (* proof state *)
  shallow : bool                   (* is the state trimmed down (libstack) *)
}

val freeze_interp_state : pstate:Proof_global.t option -> Summary.marshallable -> t
val unfreeze_interp_state : t -> unit

(* WARNING: Do not use, it will go away in future releases *)
val invalidate_cache : unit -> unit

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
val with_fail : st:t -> (unit -> Proof_global.t option) -> Proof_global.t option

module StmCompat : sig

  val freeze : Summary.marshallable -> t
  val unfreeze : t -> unit

  val with_fail : st:t -> (unit -> unit) -> unit

  open Proof_global
  exception NoCurrentProof

  val there_are_pending_proofs : unit -> bool
  val get_open_goals : unit -> int

  val set_terminator : proof_terminator -> unit
  val give_me_the_proof : unit -> Proof.t
  val get_current_proof_name : unit -> Names.Id.t

  val simple_with_current_proof :
      (unit Proofview.tactic -> Proof.t -> Proof.t) -> unit

  val with_current_proof :
      (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> 'a

  val install_state : t -> unit

  val return_proof : ?allow_partial:bool -> unit -> closed_proof_output

  val close_future_proof :
    feedback_id:Stateid.t ->
    closed_proof_output Future.computation -> closed_proof

  val close_proof : keep_body_ucst_separate:bool -> Future.fix_exn -> closed_proof

  val discard_all : unit -> unit
  val update_global_env : unit -> unit

  val get_current_context : unit -> Evd.evar_map * Environ.env

end
