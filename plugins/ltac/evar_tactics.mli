(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tacexpr
open Locus

val instantiate_tac : int -> Tacinterp.interp_sign * Glob_term.glob_constr ->
  (Id.t * hyp_location_flag, unit) location -> unit Proofview.tactic

val instantiate_tac_by_name : Id.t ->
  Tacinterp.interp_sign * Glob_term.glob_constr -> unit Proofview.tactic

val let_evar : Name.t -> EConstr.types -> unit Proofview.tactic

val hget_evar : int -> unit Proofview.tactic
