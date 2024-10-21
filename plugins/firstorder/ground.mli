(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val get_flags : unit -> Formula.flags

val ground_tac: flags:Formula.flags -> unit Proofview.tactic ->
  ((Sequent.t -> unit Proofview.tactic) -> unit Proofview.tactic) -> unit Proofview.tactic

