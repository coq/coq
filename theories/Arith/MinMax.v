(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders NPeano.

(** The Definition of maximum and minimum of two natural numbers
    is now in NPeano, as well as generic properties. *)

(** * Properties specific to the [nat] domain *)

(** Simplifications *)

Lemma max_0_l : forall n, max 0 n = n.
Proof. reflexivity. Qed.

Lemma max_0_r : forall n, max n 0 = n.
Proof. destruct n; auto. Qed.

Lemma min_0_l : forall n, min 0 n = 0.
Proof. reflexivity. Qed.

Lemma min_0_r : forall n, min n 0 = 0.
Proof. destruct n; auto. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
Proof. auto. Qed.

Lemma succ_min_distr : forall n m, S (min n m) = min (S n) (S m).
Proof. auto. Qed.

Lemma plus_max_distr_l : forall n m p, max (p + n) (p + m) = p + max n m.
Proof.
intros. apply Nat.max_monotone. repeat red; auto with arith.
Qed.

Lemma plus_max_distr_r : forall n m p, max (n + p) (m + p) = max n m + p.
Proof.
intros. apply Nat.max_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Lemma plus_min_distr_l : forall n m p, min (p + n) (p + m) = p + min n m.
Proof.
intros. apply Nat.min_monotone. repeat red; auto with arith.
Qed.

Lemma plus_min_distr_r : forall n m p, min (n + p) (m + p) = min n m + p.
Proof.
intros. apply Nat.min_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Hint Resolve
 Nat.max_l Nat.max_r Nat.le_max_l Nat.le_max_r
 Nat.min_l Nat.min_r Nat.le_min_l Nat.le_min_r : arith v62.
