(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr

val proof_tac: Ccproof.proof -> unit Proofview.tactic

val cc_tactic : int -> constr list ->  unit Proofview.tactic

val cc_fail : unit Proofview.tactic

val congruence_tac : int -> constr list -> unit Proofview.tactic

val f_equal : unit Proofview.tactic
