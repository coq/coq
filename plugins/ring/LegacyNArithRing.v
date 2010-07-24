(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the binary natural numbers *)

Require Import Bool.
Require Export LegacyRing.
Require Export ZArith_base.
Require Import NArith.
Require Import Eqdep_dec.

Unboxed Definition Neq (n m:N) :=
  match (n ?= m)%N with
  | Datatypes.Eq => true
  | _ => false
  end.

Lemma Neq_prop : forall n m:N, Is_true (Neq n m) -> n = m.
  intros n m H; unfold Neq in H.
  apply Ncompare_Eq_eq.
  destruct (n ?= m)%N; [ reflexivity | contradiction | contradiction ].
Qed.

Definition NTheory : Semi_Ring_Theory Nplus Nmult 1%N 0%N Neq.
  split.
    apply Nplus_comm.
    apply Nplus_assoc.
    apply Nmult_comm.
    apply Nmult_assoc.
    apply Nplus_0_l.
    apply Nmult_1_l.
    apply Nmult_0_l.
    apply Nmult_plus_distr_r.
(*    apply Nplus_reg_l.*)
    apply Neq_prop.
Qed.

Add Legacy Semi Ring
  N Nplus Nmult 1%N 0%N Neq NTheory [ Npos 0%N xO xI 1%positive ].
