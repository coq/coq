(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Locus

val instantiate_tac : int -> Ltac_pretype.closed_glob_constr ->
  (Id.t * hyp_location_flag) option -> unit Proofview.tactic

val instantiate_tac_by_name : Id.t ->
  Ltac_pretype.closed_glob_constr -> unit Proofview.tactic

val let_evar : Name.t -> EConstr.types -> unit Proofview.tactic
