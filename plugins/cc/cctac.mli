
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open EConstr

val proof_tac: Ccproof.proof -> unit Proofview.tactic

val cc_tactic : int -> constr list ->  unit Proofview.tactic

val cc_fail : unit Proofview.tactic

val congruence_tac : int -> constr list -> unit Proofview.tactic

val f_equal : unit Proofview.tactic
