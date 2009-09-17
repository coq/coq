(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

Require Import Zmin Zmax.
Require Import BinInt Zorder.

Open Local Scope Z_scope.

(** Lattice properties of min and max on Z *)

(** Absorption *)

Lemma Zmin_max_absorption_r_r : forall n m, Zmax n (Zmin n m) = n.
Proof.
  intros; apply Zmin_case_strong; intro; apply Zmax_case_strong; intro;
    reflexivity || apply Zle_antisym; trivial.
Qed.

Lemma Zmax_min_absorption_r_r : forall n m, Zmin n (Zmax n m) = n.
Proof.
  intros; apply Zmax_case_strong; intro; apply Zmin_case_strong; intro;
    reflexivity || apply Zle_antisym; trivial.
Qed.

(** Distributivity *)

Lemma Zmax_min_distr_r :
  forall n m p, Zmax n (Zmin m p) = Zmin (Zmax n m) (Zmax n p).
Proof.
  intros.
  repeat apply Zmax_case_strong; repeat apply Zmin_case_strong; intros;
    reflexivity ||
      apply Zle_antisym; (assumption || eapply Zle_trans; eassumption).
Qed.

Lemma Zmin_max_distr_r :
  forall n m p, Zmin n (Zmax m p) = Zmax (Zmin n m) (Zmin n p).
Proof.
  intros.
  repeat apply Zmax_case_strong; repeat apply Zmin_case_strong; intros;
    reflexivity ||
      apply Zle_antisym; (assumption || eapply Zle_trans; eassumption).
Qed.

(** Modularity *)

Lemma Zmax_min_modular_r :
  forall n m p, Zmax n (Zmin m (Zmax n p)) = Zmin (Zmax n m) (Zmax n p).
Proof.
  intros; repeat apply Zmax_case_strong; repeat apply Zmin_case_strong; intros;
    reflexivity ||
      apply Zle_antisym; (assumption || eapply Zle_trans; eassumption).
Qed.

Lemma Zmin_max_modular_r :
  forall n m p, Zmin n (Zmax m (Zmin n p)) = Zmax (Zmin n m) (Zmin n p).
Proof.
  intros; repeat apply Zmax_case_strong; repeat apply Zmin_case_strong; intros;
    reflexivity ||
      apply Zle_antisym; (assumption || eapply Zle_trans; eassumption).
Qed.

(** Disassociativity *)

Lemma max_min_disassoc : forall n m p, Zmin n (Zmax m p) <= Zmax (Zmin n m) p.
Proof.
  intros; repeat apply Zmax_case_strong; repeat apply Zmin_case_strong; intros;
    apply Zle_refl || (assumption || eapply Zle_trans; eassumption).
Qed.

