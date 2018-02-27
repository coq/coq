(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


val discrHyp : Names.Id.t -> unit Proofview.tactic
val injHyp : Names.Id.t -> unit Proofview.tactic

(* val refine_tac : Evd.open_constr -> unit Proofview.tactic *)

val onSomeWithHoles : ('a option -> unit Proofview.tactic) -> 'a Tacexpr.delayed_open option -> unit Proofview.tactic
