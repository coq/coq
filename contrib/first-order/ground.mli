(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
type goal = Tacticals.goal
type 'a sigma = 'a Tacticals.sigma
(* arnaud: /trucs factices *)

val ground_tac:     tactic ->
  (goal sigma -> Sequent.t) -> tactic

