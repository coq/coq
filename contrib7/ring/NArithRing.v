(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the binary natural numbers *)

Require Export Ring.
Require Export ZArith_base.
Require NArith.
Require Eqdep_dec.

Definition Neq := [n,m:entier]
  Cases (Ncompare n m) of
    EGAL => true
  | _ => false
  end.

Lemma Neq_prop : (n,m:entier)(Is_true (Neq n m)) -> n=m.
  Intros n m H; Unfold Neq in H.
  Apply Ncompare_Eq_eq.
  NewDestruct (Ncompare n m); [Reflexivity | Contradiction | Contradiction ].
Save.

Definition NTheory : (Semi_Ring_Theory Nplus Nmult (Pos xH) Nul Neq).
  Split.
    Apply Nplus_comm.
    Apply Nplus_assoc.
    Apply Nmult_comm.
    Apply Nmult_assoc.
    Apply Nplus_0_l.
    Apply Nmult_1_l.
    Apply Nmult_0_l.
    Apply Nmult_plus_distr_r.
    Apply Nplus_reg_l.
    Apply Neq_prop.
Save.

Add Semi Ring entier Nplus Nmult (Pos xH) Nul Neq NTheory [Pos Nul xO xI xH].
