(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Arith.

Open Local Scope nat_scope.

Implicit Types m n : nat.

(** minimum of two natural numbers *)

Fixpoint min n m {struct n} : nat :=
  match n, m with
  | O, _ => 0
  | S n', O => 0
  | S n', S m' => S (min n' m')
  end.

(** Simplifications of [min] *)

Lemma min_SS : forall n m, S (min n m) = min (S n) (S m).
Proof.
auto with arith.
Qed.

Lemma min_comm : forall n m, min n m = min m n.
Proof.
induction n; induction m; simpl in |- *; auto with arith.
Qed.

(** [min] and [le] *)

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

(** [min n m] is equal to [n] or [m] *)

Lemma min_dec : forall n m, {min n m = n} + {min n m = m}.
Proof.
induction n; induction m; simpl in |- *; auto with arith.
elim (IHn m); intro H; elim H; auto.
Qed.

Lemma min_case : forall n m (P:nat -> Set), P n -> P m -> P (min n m).
Proof.
induction n; simpl in |- *; auto with arith.
induction m; intros; simpl in |- *; auto with arith.
pattern (min n m) in |- *; apply IHn; auto with arith.
Qed.

Lemma min_case2 : forall n m (P:nat -> Prop), P n -> P m -> P (min n m).
Proof.
induction n; simpl in |- *; auto with arith.
induction m; intros; simpl in |- *; auto with arith.
pattern (min n m) in |- *; apply IHn; auto with arith.
Qed.