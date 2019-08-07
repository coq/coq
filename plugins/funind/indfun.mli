(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val functional_induction :
  bool ->
  EConstr.constr ->
  (EConstr.constr * EConstr.constr Tactypes.bindings) option ->
  Ltac_plugin.Tacexpr.or_and_intro_pattern option ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
