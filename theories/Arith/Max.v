(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Le Plus.

Open Local Scope nat_scope.

Implicit Types m n : nat.

(** * Maximum of two natural numbers *)

Fixpoint max n m {struct n} : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

(** * Inductive characterization of [max] *)

Lemma max_case_strong : forall n m (P:nat -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (max n m).
Proof.
  induction n; destruct m; simpl in *; auto with arith.
  intros P H1 H2; apply IHn; intro; [apply H1|apply H2]; auto with arith.
Qed.

(** Propositional characterization of [max] *)

Lemma max_spec : forall n m, m <= n /\ max n m = n \/ n <= m /\ max n m = m.
Proof.
  intros n m; apply max_case_strong; auto.
Qed.

(** * [max n m] is equal to [n] or [m] *)

Lemma max_dec : forall n m, {max n m = n} + {max n m = m}.
Proof.
  induction n; destruct m; simpl; auto.
  destruct (IHn m) as [-> | ->]; auto.
Defined.

(** [max n m] is equal to [n] or [m], alternative formulation *)

Lemma max_case : forall n m (P:nat -> Type), P n -> P m -> P (max n m).
Proof.
  intros n m; destruct (max_dec n m) as [-> | ->]; auto.
Defined.

(** * Compatibility properties of [max] *)

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
Proof.
  auto.
Qed.

Lemma plus_max_distr_l : forall n m p, max (p + n) (p + m) = p + max n m.
Proof.
  induction p; simpl; auto.
Qed.

Lemma plus_max_distr_r : forall n m p, max (n + p) (m + p) = max n m + p.
Proof.
  intros n m p; repeat rewrite (plus_comm _ p).
  apply plus_max_distr_l.
Qed.

(** * Semi-lattice algebraic properties of [max] *)

Lemma max_idempotent : forall n, max n n = n.
Proof.
  intros; apply max_case; auto.
Qed.

Lemma max_assoc : forall m n p : nat, max m (max n p) = max (max m n) p.
Proof.
  induction m; destruct n; destruct p; trivial.
  simpl; auto.
Qed.

Lemma max_comm : forall n m, max n m = max m n.
Proof.
  induction n; destruct m; simpl; auto.
Qed.

(** * Least-upper bound properties of [max] *)

Lemma max_l : forall n m, m <= n -> max n m = n.
Proof.
  induction n; destruct m; simpl; auto with arith.
Qed.

Lemma max_r : forall n m, n <= m -> max n m = m.
Proof.
  induction n; destruct m; simpl; auto with arith.
Qed.

Lemma le_max_l : forall n m, n <= max n m.
Proof.
  induction n; simpl; auto with arith.
  destruct m; simpl; auto with arith.
Qed.

Lemma le_max_r : forall n m, m <= max n m.
Proof.
  induction n; simpl; auto with arith.
  induction m; simpl; auto with arith.
Qed.
Hint Resolve max_r max_l le_max_l le_max_r: arith v62.

Lemma max_lub_l : forall n m p, max n m <= p -> n <= p.
Proof.
intros n m p; eapply le_trans. apply le_max_l.
Qed.

Lemma max_lub_r : forall n m p, max n m <= p -> m <= p.
Proof.
intros n m p; eapply le_trans. apply le_max_r.
Qed.

Lemma max_lub : forall n m p, n <= p -> m <= p -> max n m <= p.
Proof.
  intros n m p; apply max_case; auto.
Qed.

(* begin hide *)
(* Compatibility *)
Notation max_case2 := max_case (only parsing).
Notation max_SS := succ_max_distr (only parsing).
(* end hide *)
