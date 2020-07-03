(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val psatz_Z : int -> unit Proofview.tactic -> unit Proofview.tactic
val psatz_Q : int -> unit Proofview.tactic -> unit Proofview.tactic
val psatz_R : int -> unit Proofview.tactic -> unit Proofview.tactic
val xlia : unit Proofview.tactic -> unit Proofview.tactic
val xnlia : unit Proofview.tactic -> unit Proofview.tactic
val nra : unit Proofview.tactic -> unit Proofview.tactic
val nqa : unit Proofview.tactic -> unit Proofview.tactic
val sos_Z : unit Proofview.tactic -> unit Proofview.tactic
val sos_Q : unit Proofview.tactic -> unit Proofview.tactic
val sos_R : unit Proofview.tactic -> unit Proofview.tactic
val lra_Q : unit Proofview.tactic -> unit Proofview.tactic
val lra_R : unit Proofview.tactic -> unit Proofview.tactic
val print_lia_profile : unit -> unit

(** {5 Use Micromega independently from tactics. } *)

val dump_proof_term : Micromega.zArithProof -> EConstr.t
(** [dump_proof_term] generates the Coq representation of a Micromega proof witness *)
