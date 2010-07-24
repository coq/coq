(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Raxioms.
Require Export LegacyField.
Import LegacyRing_theory.

Section LegacyRfield.

Open Scope R_scope.

Lemma RLegacyTheory : Ring_Theory Rplus Rmult 1 0 Ropp (fun x y:R => false).
  split.
  exact Rplus_comm.
  symmetry  in |- *; apply Rplus_assoc.
  exact Rmult_comm.
  symmetry  in |- *; apply Rmult_assoc.
  intro; apply Rplus_0_l.
  intro; apply Rmult_1_l.
  exact Rplus_opp_r.
  intros.
  rewrite Rmult_comm.
  rewrite (Rmult_comm n p).
  rewrite (Rmult_comm m p).
  apply Rmult_plus_distr_l.
  intros; contradiction.
Defined.

End LegacyRfield.

Add Legacy Field
R Rplus Rmult 1%R 0%R Ropp (fun x y:R => false) Rinv RLegacyTheory Rinv_l
  with minus := Rminus div := Rdiv.
