(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Le.

Open Local Scope nat_scope.

Implicit Types m n : nat.

(** * maximum of two natural numbers *)

Fixpoint max n m {struct n} : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

(** * Simplifications of [max] *)

Lemma max_SS : forall n m, S (max n m) = max (S n) (S m).
Proof.
  auto with arith.
Qed.

Theorem max_assoc : forall m n p : nat, max m (max n p) = max (max m n) p.
Proof.
  induction m; destruct n; destruct p; trivial.
  simpl.
  auto using IHm.
Qed.

Lemma max_comm : forall n m, max n m = max m n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

(** * [max] and [le] *)

Lemma max_l : forall n m, m <= n -> max n m = n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma max_r : forall n m, n <= m -> max n m = m.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma le_max_l : forall n m, n <= max n m.
Proof.
  induction n; intros; simpl in |- *; auto with arith.
  elim m; intros; simpl in |- *; auto with arith.
Qed.

Lemma le_max_r : forall n m, m <= max n m.
Proof.
  induction n; simpl in |- *; auto with arith.
  induction m; simpl in |- *; auto with arith.
Qed.
Hint Resolve max_r max_l le_max_l le_max_r: arith v62.


(** * [max n m] is equal to [n] or [m] *)

Lemma max_dec : forall n m, {max n m = n} + {max n m = m}.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
  elim (IHn m); intro H; elim H; auto.
Defined.

Lemma max_case : forall n m (P:nat -> Type), P n -> P m -> P (max n m).
Proof.
  induction n; simpl in |- *; auto with arith.
  induction m; intros; simpl in |- *; auto with arith.
  pattern (max n m) in |- *; apply IHn; auto with arith.
Defined.

Notation max_case2 := max_case (only parsing).
