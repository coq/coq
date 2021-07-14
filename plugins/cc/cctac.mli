(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr

val proof_tac: Ccproof.proof -> unit Proofview.tactic

val cc_tactic : int -> constr list -> bool -> unit Proofview.tactic

val congruence_tac : int -> constr list -> unit Proofview.tactic

val simple_congruence_tac : int -> constr list -> unit Proofview.tactic

val f_equal : unit Proofview.tactic
