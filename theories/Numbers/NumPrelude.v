(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export Setoid Morphisms Morphisms_Prop.

Set Implicit Arguments.

(* The following tactic uses solve_proper to solve the goals
relating to well-definedness that are produced by applying induction.
We declare it to take the tactic that applies the induction theorem
and not the induction theorem itself because the tactic may, for
example, supply additional arguments, as does NZinduct_center in
NZBase.v *)

Ltac induction_maker n t :=
  try intros until n; pattern n; t; clear n; [solve_proper | ..].

