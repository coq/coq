(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val discrHyp : Names.Id.t -> unit Proofview.tactic
val injHyp : Names.Id.t -> unit Proofview.tactic

(* val refine_tac : Evd.open_constr -> unit Proofview.tactic *)

val onSomeWithHoles : ('a option -> unit Proofview.tactic) -> 'a Evd.sigma option -> unit Proofview.tactic
