(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Proof_type

val h_discrHyp : Names.identifier -> tactic
val h_injHyp : Names.identifier -> tactic

val refine_tac : Evd.open_constr -> tactic

val onSomeWithHoles : ('a option -> tactic) -> 'a Evd.sigma option -> tactic
