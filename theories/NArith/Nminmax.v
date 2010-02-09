(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders BinNat Nnat NBinary.

(** * Maximum and Minimum of two [N] numbers *)

Local Open Scope N_scope.

(** Generic properties of min and max are already in [NBinary.N].
    We add here the ones specific to N. *)

Module Type Nextend (N:NBinary.N).

(** Simplifications *)

Lemma max_0_l : forall n, Nmax 0 n = n.
Proof.
 intros. unfold Nmax. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma max_0_r : forall n, Nmax n 0 = n.
Proof. intros. rewrite N.max_comm. apply max_0_l. Qed.

Lemma min_0_l : forall n, Nmin 0 n = 0.
Proof.
 intros. unfold Nmin. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma min_0_r : forall n, Nmin n 0 = 0.
Proof. intros. rewrite N.min_comm. apply min_0_l. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr :
 forall n m, Nsucc (Nmax n m) = Nmax (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply N.max_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma succ_min_distr : forall n m, Nsucc (Nmin n m) = Nmin (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply N.min_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma add_max_distr_l : forall n m p, Nmax (p + n) (p + m) = p + Nmax n m.
Proof.
 intros. apply N.max_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma add_max_distr_r : forall n m p, Nmax (n + p) (m + p) = Nmax n m + p.
Proof.
 intros. rewrite (N.add_comm n p), (N.add_comm m p), (N.add_comm _ p).
 apply add_max_distr_l.
Qed.

Lemma add_min_distr_l : forall n m p, Nmin (p + n) (p + m) = p + Nmin n m.
Proof.
 intros. apply N.min_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma add_min_distr_r : forall n m p, Nmin (n + p) (m + p) = Nmin n m + p.
Proof.
 intros. rewrite (N.add_comm n p), (N.add_comm m p), (N.add_comm _ p).
 apply add_min_distr_l.
Qed.

End Nextend.