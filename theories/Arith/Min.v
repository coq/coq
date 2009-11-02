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

Implicit Types m n p : nat.

(** * minimum of two natural numbers *)

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(** * Simplifications of [min] *)

Lemma min_0_l : forall n : nat, min 0 n = 0.
Proof.
  trivial.
Qed.

Lemma min_0_r : forall n : nat, min n 0 = 0.
Proof.
  destruct n; trivial.
Qed.

Lemma min_SS : forall n m, S (min n m) = min (S n) (S m).
Proof.
  auto with arith.
Qed.

(** * [min n m] is equal to [n] or [m] *)

Lemma min_dec : forall n m, {min n m = n} + {min n m = m}.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
  elim (IHn m); intro H; elim H; auto.
Qed.

Lemma min_case : forall n m (P:nat -> Type), P n -> P m -> P (min n m).
Proof.
  induction n; simpl in |- *; auto with arith.
  induction m; intros; simpl in |- *; auto with arith.
  pattern (min n m) in |- *; apply IHn; auto with arith.
Qed.

(** * Semi-lattice algebraic properties of [min] *)

Lemma min_idempotent : forall n, min n n = n.
Proof.
  induction n; simpl; [|rewrite IHn]; trivial.
Qed.

Lemma min_assoc : forall m n p : nat, min m (min n p) = min (min m n) p.
Proof.
  induction m; destruct n; destruct p; trivial.
  simpl.
  auto using (IHm n p).
Qed.

Lemma min_comm : forall n m, min n m = min m n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

(** * Least-upper bound properties of [min] *)

Lemma min_l : forall n m, n <= m -> min n m = n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma min_r : forall n m, m <= n -> min n m = m.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma le_min_l : forall n m, min n m <= n.
Proof.
  induction n; intros; simpl in |- *; auto with arith.
  elim m; intros; simpl in |- *; auto with arith.
Qed.

Lemma le_min_r : forall n m, min n m <= m.
Proof.
  induction n; simpl in |- *; auto with arith.
  induction m; simpl in |- *; auto with arith.
Qed.
Hint Resolve min_l min_r le_min_l le_min_r: arith v62.

Lemma min_glb_l : forall n m p, p <= min n m -> p <= n.
Proof.
intros; eapply le_trans; [eassumption|apply le_min_l].
Qed.

Lemma min_glb_r : forall n m p, p <= min n m -> p <= m.
Proof.
intros; eapply le_trans; [eassumption|apply le_min_r].
Qed.

Lemma min_glb : forall n m p, p <= n -> p <= m -> p <= min n m.
Proof.
  intros n m p; apply min_case; auto.
Qed.

Notation min_case2 := min_case (only parsing).

