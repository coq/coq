(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

Require Import Arith.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.

Open Local Scope Z_scope.

(**********************************************************************)
(** *** Maximum of two binary integer numbers *)

Definition Zmax m n :=
   match m ?= n with
    | Eq | Gt => m
    | Lt => n
    end.

(** Characterization of maximum on binary integer numbers *)

Lemma Zmax_case : forall (n m:Z) (P:Z -> Type), P n -> P m -> P (Zmax n m).
Proof.
intros n m P H1 H2; unfold Zmax in |- *; case (n ?= m); auto with arith.
Qed.

Lemma Zmax_case_strong : forall (n m:Z) (P:Z -> Type), 
  (m<=n -> P n) -> (n<=m -> P m) -> P (Zmax n m).
Proof.
intros n m P H1 H2; unfold Zmax, Zle, Zge in *.
rewrite <- (Zcompare_antisym n m) in H1.
destruct (n ?= m); (apply H1|| apply H2); discriminate. 
Qed.

(** Least upper bound properties of max *)

Lemma Zle_max_l : forall n m:Z, n <= Zmax n m.
Proof.
intros; apply Zmax_case_strong; auto with zarith.
Qed.

Notation Zmax1 := Zle_max_l (only parsing).

Lemma Zle_max_r : forall n m:Z, m <= Zmax n m.
Proof.
intros; apply Zmax_case_strong; auto with zarith.
Qed.

Notation Zmax2 := Zle_max_r (only parsing).

Lemma Zmax_lub : forall n m p:Z, n <= p -> m <= p -> Zmax n m <= p.
Proof.
intros; apply Zmax_case; assumption.
Qed.

(** Semi-lattice properties of max *)

Lemma Zmax_idempotent : forall n:Z, Zmax n n = n.
Proof.
intros; apply Zmax_case; auto.
Qed.

Lemma Zmax_comm : forall n m:Z, Zmax n m = Zmax m n.
Proof.
intros; do 2 apply Zmax_case_strong; intros; 
  apply Zle_antisym; auto with zarith.
Qed.

Lemma Zmax_assoc : forall n m p:Z, Zmax n (Zmax m p) = Zmax (Zmax n m) p.
Proof.
intros n m p; repeat apply Zmax_case_strong; intros; 
  reflexivity || (try apply Zle_antisym); eauto with zarith.
Qed.

(** Additional properties of max *)

Lemma Zmax_irreducible_inf : forall n m:Z, Zmax n m = n \/ Zmax n m = m.
Proof.
intros; apply Zmax_case; auto.
Qed.

Lemma Zmax_le_prime_inf : forall n m p:Z, p <= Zmax n m -> p <= n \/ p <= m.
Proof.
intros n m p; apply Zmax_case; auto.
Qed.

(** Operations preserving max *)

Lemma Zsucc_max_distr : 
  forall n m:Z, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m).
Proof.
intros n m; unfold Zmax in |- *; rewrite (Zcompare_succ_compat n m);
 elim_compare n m; intros E; rewrite E; auto with arith.
Qed.

Lemma Zplus_max_distr_r : forall n m p:Z, Zmax (n + p) (m + p) = Zmax n m + p.
Proof.
intros x y n; unfold Zmax in |- *.
rewrite (Zplus_comm x n); rewrite (Zplus_comm y n);
 rewrite (Zcompare_plus_compat x y n).
case (x ?= y); apply Zplus_comm.
Qed.
