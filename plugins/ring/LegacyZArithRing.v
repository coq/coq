(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Instantiation of the Ring tactic for the binary integers of ZArith *)

Require Export LegacyArithRing.
Require Export ZArith_base.
Require Import Eqdep_dec.
Require Import LegacyRing.

Unboxed Definition Zeq (x y:Z) :=
  match (x ?= y)%Z with
  | Datatypes.Eq => true
  | _ => false
  end.

Lemma Zeq_prop : forall x y:Z, Is_true (Zeq x y) -> x = y.
  intros x y H; unfold Zeq in H.
  apply Zcompare_Eq_eq.
  destruct (x ?= y)%Z; [ reflexivity | contradiction | contradiction ].
Qed.

Definition ZTheory : Ring_Theory Zplus Zmult 1%Z 0%Z Zopp Zeq.
  split; intros; eauto with zarith.
  apply Zeq_prop; assumption.
Qed.

(* NatConstants and NatTheory are defined in Ring_theory.v *)
Add Legacy Ring Z Zplus Zmult 1%Z 0%Z Zopp Zeq ZTheory
 [ Zpos Zneg 0%Z xO xI 1%positive ].
