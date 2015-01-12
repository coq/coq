(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val ground_tac:     Tacmach.tactic ->
  (Proof_type.goal Tacmach.sigma -> Sequent.t * Proof_type.goal Tacmach.sigma) -> Tacmach.tactic

