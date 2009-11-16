(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Order on natural numbers. [le] is defined in [Init/Peano.v] as:
<<
Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.
>>
 *)

Open Local Scope nat_scope.

Implicit Types m n p : nat.

(** * [le] is a pre-order *)

(** Reflexivity *)
Theorem le_refl : forall n, n <= n.
Proof.
  exact le_n.
Qed.

(** Transitivity *)
Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  induction 2; auto.
Qed.
Hint Resolve le_trans: arith v62.

(** * Properties of [le] w.r.t. successor, predecessor and 0 *)

(** Comparison to 0 *)

Theorem le_0_n : forall n, 0 <= n.
Proof.
  induction n; auto.
Qed.

Theorem le_Sn_0 : forall n, ~ S n <= 0.
Proof.
  red in |- *; intros n H.
  change (IsSucc 0) in |- *; elim H; simpl in |- *; auto with arith.
Qed.

Hint Resolve le_0_n le_Sn_0: arith v62.

Theorem le_n_0_eq : forall n, n <= 0 -> 0 = n.
Proof.
  induction n; auto with arith.
  intro; contradiction le_Sn_0 with n.
Qed.
Hint Immediate le_n_0_eq: arith v62.


(** [le] and successor *)

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  induction 1; auto.
Qed.

Theorem le_n_Sn : forall n, n <= S n.
Proof.
  auto.
Qed.

Hint Resolve le_n_S le_n_Sn : arith v62.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H; apply le_trans with (S n); auto with arith.
Qed.
Hint Immediate le_Sn_le: arith v62.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H; change (pred (S n) <= pred (S m)) in |- *.
  destruct H; simpl; auto with arith.
Qed.
Hint Immediate le_S_n: arith v62.

Theorem le_Sn_n : forall n, ~ S n <= n.
Proof.
  induction n; auto with arith.
Qed.
Hint Resolve le_Sn_n: arith v62.

(** [le] and predecessor *)

Theorem le_pred_n : forall n, pred n <= n.
Proof.
  induction n; auto with arith.
Qed.
Hint Resolve le_pred_n: arith v62.

Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Proof.
  destruct n; simpl; auto with arith.
  destruct m; simpl; auto with arith.
Qed.


(** * [le] is a order on [nat] *)
(** Antisymmetry *)

Theorem le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
  intros n m H; destruct H as [|m' H]; auto with arith.
  intros H1.
  absurd (S m' <= m'); auto with arith.
  apply le_trans with n; auto with arith.
Qed.
Hint Immediate le_antisym: arith v62.


(** * A different elimination principle for the order on natural numbers *)

Lemma le_elim_rel :
 forall P:nat -> nat -> Prop,
   (forall p, P 0 p) ->
   (forall p (q:nat), p <= q -> P p q -> P (S p) (S q)) ->
   forall n m, n <= m -> P n m.
Proof.
  induction n; auto with arith.
  intros m Le.
  elim Le; auto with arith.
Qed.

(* begin hide *)
Notation le_O_n := le_0_n (only parsing).
Notation le_Sn_O := le_Sn_0 (only parsing).
Notation le_n_O_eq := le_n_0_eq (only parsing).
(* end hide *)
