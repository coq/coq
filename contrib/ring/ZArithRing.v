(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the binary integers of ZArith *)

Require Export ArithRing.
Require Export ZArith_base.
Require Import Eqdep_dec.

Definition Zeq (x y:Z) :=
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
  split; intros; apply eq2eqT; eauto with zarith.
  apply eqT2eq; apply Zeq_prop; assumption.
Qed.

(* NatConstants and NatTheory are defined in Ring_theory.v *)
Add Ring Z Zplus Zmult 1%Z 0%Z Zopp Zeq ZTheory
 [ Zpos Zneg 0%Z xO xI 1%positive ].