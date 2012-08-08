(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Instantiation of the Ring tactic for the binary natural numbers *)

Require Import Bool.
Require Export LegacyRing.
Require Export ZArith_base.
Require Import NArith.
Require Import Eqdep_dec.

Definition Neq (n m:N) :=
  match (n ?= m)%N with
  | Datatypes.Eq => true
  | _ => false
  end.

Lemma Neq_prop : forall n m:N, Is_true (Neq n m) -> n = m.
  intros n m H; unfold Neq in H.
  apply N.compare_eq.
  destruct (n ?= m)%N; [ reflexivity | contradiction | contradiction ].
Qed.

Definition NTheory : Semi_Ring_Theory N.add N.mul 1%N 0%N Neq.
  split.
    apply N.add_comm.
    apply N.add_assoc.
    apply N.mul_comm.
    apply N.mul_assoc.
    apply N.add_0_l.
    apply N.mul_1_l.
    apply N.mul_0_l.
    apply N.mul_add_distr_r.
    apply Neq_prop.
Qed.

Add Legacy Semi Ring
  N N.add N.mul 1%N 0%N Neq NTheory [ Npos 0%N xO xI 1%positive ].
