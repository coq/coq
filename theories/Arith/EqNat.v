(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Equality on natural numbers *)

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Fixpoint eq_nat n m {struct n} : Prop :=
  match n, m with
  | O, O => True
  | O, S _ => False
  | S _, O => False
  | S n1, S m1 => eq_nat n1 m1
  end.

Theorem eq_nat_refl : forall n, eq_nat n n.
induction n; simpl in |- *; auto.
Qed.
Hint Resolve eq_nat_refl: arith v62.

Theorem eq_eq_nat : forall n m, n = m -> eq_nat n m.
induction 1; trivial with arith.
Qed.
Hint Immediate eq_eq_nat: arith v62.

Theorem eq_nat_eq : forall n m, eq_nat n m -> n = m.
induction n; induction m; simpl in |- *; contradiction || auto with arith.
Qed.
Hint Immediate eq_nat_eq: arith v62.

Theorem eq_nat_elim :
 forall n (P:nat -> Prop), P n -> forall m, eq_nat n m -> P m.
intros; replace m with n; auto with arith.
Qed.

Theorem eq_nat_decide : forall n m, {eq_nat n m} + {~ eq_nat n m}.
induction n.
destruct m as [| n].
auto with arith.
intros; right; red in |- *; trivial with arith.
destruct m as [| n0].
right; red in |- *; auto with arith.
intros.
simpl in |- *.
apply IHn.
Defined.

Fixpoint beq_nat n m {struct n} : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n1, S m1 => beq_nat n1 m1
  end.

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.

Definition beq_nat_eq : forall x y, true = beq_nat x y -> x = y.
Proof.
  double induction x y; simpl in |- *.
    reflexivity.
    intros; discriminate H0.
    intros; discriminate H0.
    intros; case (H0 _ H1); reflexivity.
Defined.
