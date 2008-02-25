(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Rawterm

(* arnaud:trucs factices *)
type tactic = Tacticals.tactic
(* arnaud: /trucs factices *)

val h_discrHyp : quantified_hypothesis -> tactic
val h_injHyp : quantified_hypothesis -> tactic

val refine_tac : Goal.open_constr -> tactic

