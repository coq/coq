(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val functional_induction :
     bool
  -> EConstr.constr
  -> (EConstr.constr * EConstr.constr Tactypes.bindings) option
  -> Ltac_plugin.Tacexpr.or_and_intro_pattern option
  -> unit Proofview.tactic
