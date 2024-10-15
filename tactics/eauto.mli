(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Hints
open Tactypes

val e_assumption : unit Proofview.tactic

val e_give_exact : ?flags:Unification.unify_flags -> constr -> unit Proofview.tactic

val gen_eauto : ?debug:debug -> ?depth:int -> delayed_open_constr list ->
  hint_db_name list option -> unit Proofview.tactic

val eauto_with_bases :
  ?debug:debug ->
  ?depth:int ->
  delayed_open_constr list -> hint_db list -> unit Proofview.tactic

val autounfold : hint_db_name list -> Locus.clause -> unit Proofview.tactic
val autounfold_tac : hint_db_name list option -> Locus.clause -> unit Proofview.tactic
val autounfold_one : hint_db_name list -> Locus.hyp_location option -> unit Proofview.tactic
