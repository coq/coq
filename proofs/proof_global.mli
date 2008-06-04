(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(***********************************************************************)
(*                                                                     *)
(*      This module defines the global proof environment               *)
(*      Especially it keeps tracks of whether or not there is          *)
(*      a proof which is currently being edited.                       *)
(*                                                                     *)
(***********************************************************************)


val there_is_a_proof : unit -> bool
val check_no_pending_proof : unit -> unit

exception NoCurrentProof
val give_me_the_proof : unit -> Proof.proof

exception ProofInProgress
val start_a_new_proof : (Environ.env * Term.types * string option) list -> 
                        (Term.constr list -> Decl_kinds.proof_end -> unit) ->
                        unit

val discard : unit -> unit
val delete_current_proof : unit -> unit



(*arnaud: debugging ?*)
val pr_subgoals : (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds


val db_run_tactic_on : Environ.env -> int -> unit Proofview.tactic -> unit
