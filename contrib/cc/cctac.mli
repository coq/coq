(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term 

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud: /trucs factices *)

val proof_tac: Ccproof.proof -> tactic

val cc_tactic : int -> constr list -> tactic

val cc_fail : tactic

val congruence_tac : int -> constr list -> tactic
