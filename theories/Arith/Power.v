(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id:$ *)

(** Power function on [nat] *)

(** From Laurent Théry, INRIA *)

Require Import Plus.
Require Import Mult.
Require Import Lt.
Require Import Le.
Require Import Compare_dec.

(** [power n m], written [n^m] computes [n] to the power [m] *)

Fixpoint power n m {struct m} :=
  match m with
  | O => 1
  | S m' => n * n ^ m'
  end

where "n ^ m" := (power n m) : nat_scope.

Theorem power_1 : forall n : nat, n ^ 1 = n.
Proof.
simpl in |- *; intros x; rewrite mult_1_r; auto.
Qed.
Hint Rewrite power_1: arith2.

Lemma power_lt_0 : forall n m : nat, 0 < n -> 0 < n ^ m.
Proof.
induction m; simpl in |- *; auto with arith2.
Qed.
Hint Resolve power_lt_0: arith2.
 
Lemma power_le : forall n m : nat, 0 < m -> n <= n ^ m.
Proof.
intros x n; case n; simpl in |- *; auto.
intros H'; inversion H'.
intros n'; case x; intros; auto.
apply mult_le_r; auto.
apply power_lt_0; auto with arith.
Qed.
Hint Resolve power_le: arith2.

Lemma power_mult :
 forall n m p : nat, n ^ m * n ^ p = n ^ (m + p).
Proof.
intros; induction m as [ | m IHm]; simpl in |- *; auto.
rewrite mult_assoc_reverse; rewrite IHm; auto.
Qed.
Hint Rewrite <- power_mult: arith2.
 
Lemma power_power : forall n m p : nat, (n ^ m) ^ p = n ^ (m * p).
Proof.
induction p as [ | p IHp]; simpl in |- *; auto.
rewrite mult_comm; simpl in |- *; auto.
rewrite mult_comm with (m := S p); simpl in |- *;
 rewrite (mult_comm p); rewrite IHp; apply power_mult.
Qed.
Hint Rewrite -> power_power: arith2.
 
Lemma power_of_1 : forall n : nat, 1 ^ n = 1.
Proof.
induction n as [ | n IHn]; simpl in |- *; auto.
rewrite IHn; auto.
Qed.
Hint Rewrite -> power_of_1: arith2.
 
Lemma power_of_0 : forall n : nat, 0 < n -> 0 ^ n = 0.
Proof.
simple induction n.
inversion 1.
intros; simpl in |- *; auto.
Qed.
Hint Rewrite <- power_of_0 using progress (auto with arith2) : arith2.

Theorem power_lt_mono :
 forall n m p : nat, 1 < n -> m < p -> n ^ m < n ^ p.
Proof.
intros r p q H H0; elim H0; simpl in |- *; intros; auto with arith;
 pattern (r ^ p) at 1 in |- *; replace (r ^ p) with (1 * r ^ p);
 auto with arith.
repeat rewrite (fun x y z => mult_comm x (power y z)); auto with arith.
apply mult_lt_compat_l; auto with arith.
apply power_lt_0; auto with arith.
apply mult_lt_compat; auto with arith.
Qed.
Hint Resolve power_lt_mono : arith2.

Theorem power_le_mono :
 forall n m p : nat, 0 < n -> m <= p -> n ^ m <= n ^ p.
Proof.
intros p q r H; inversion H; auto with arith.
repeat rewrite power_of_1; auto with arith.
intros H2; case (le_lt_or_eq _ _ H2); auto; intros H3.
apply lt_le_weak; apply power_lt_mono; auto with arith.
rewrite H3; auto.
Qed.
Hint Resolve power_le_mono : arith2.

Theorem power_le_mono_inv :
 forall n m p : nat, 1 < n -> n ^ m <= n ^ p -> m <= p.
Proof.
intros p q r H H0; apply not_lt_le;intro.
apply (le_not_lt _ _ H0); apply power_lt_mono; auto with arith.
Qed.
 
Theorem power_id_lt : forall n m : nat, 1 < m -> n < m ^ n.
Proof.
intros p q; elim p; simpl in |- *; auto with arith.
intros p1; case p1; simpl in |- *; auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros n H H1; apply le_lt_trans with (q * S n); auto with arith arith2.
apply le_trans with (2 * S n); auto with arith.
simpl in |- *; auto with arith.
repeat (rewrite <- plus_n_Sm; simpl in |- *); auto with arith.
repeat rewrite (fun x => mult_comm x (S n));
 apply (fun m n p : nat => mult_le_compat_l p n m); 
 auto with arith.
Qed.
Hint Resolve power_id_lt : arith2.
 
Theorem power_lt_mono_inv1 :
 forall n m p : nat, 0 < n -> n ^ m < n ^ p -> m < p.
Proof.
intros p q r Hr H; apply not_le_lt; intro.
generalize H; apply le_not_lt. apply power_le_mono; auto with arith.
Qed.
 
Theorem power_lt_mono_inv2 :
 forall n m p : nat, 0 < p -> n ^ m < n ^ p -> m < p.
Proof.
intros n p q H1 H2; apply power_lt_mono_inv1 with (n := n); auto.
generalize H1 H2; case n; simpl in |- *; auto with arith.
case q; simpl in |- *; auto with arith.
case p; simpl in |- *; auto with arith.
Qed.
