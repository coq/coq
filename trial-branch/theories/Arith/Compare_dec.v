(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Definition zerop n : {n = 0} + {0 < n}.
  destruct n; auto with arith.
Defined.

Definition lt_eq_lt_dec n m : {n < m} + {n = m} + {m < n}.
  induction n; simple destruct m; auto with arith.
  intros m0; elim (IHn m0); auto with arith.
  induction 1; auto with arith.
Defined.

Definition gt_eq_gt_dec n m : {m > n} + {n = m} + {n > m}.
  exact lt_eq_lt_dec.
Defined.

Definition le_lt_dec n m : {n <= m} + {m < n}.
  induction n.
  auto with arith.
  destruct m.
  auto with arith.
  elim (IHn m); auto with arith.
Defined.

Definition le_le_S_dec n m : {n <= m} + {S m <= n}.
  exact le_lt_dec.
Defined.

Definition le_ge_dec n m : {n <= m} + {n >= m}.
  intros; elim (le_lt_dec n m); auto with arith.
Defined.

Definition le_gt_dec n m : {n <= m} + {n > m}.
  exact le_lt_dec.
Defined.

Definition le_lt_eq_dec n m : n <= m -> {n < m} + {n = m}.
  intros; elim (lt_eq_lt_dec n m); auto with arith.
  intros; absurd (m < n); auto with arith.
Defined.

(** Proofs of decidability *)

Theorem dec_le : forall n m, decidable (n <= m).
Proof.
  intros x y; unfold decidable in |- *; elim (le_gt_dec x y);
    [ auto with arith | intro; right; apply gt_not_le; assumption ].
Qed.

Theorem dec_lt : forall n m, decidable (n < m).
Proof.
  intros x y; unfold lt in |- *; apply dec_le.
Qed.

Theorem dec_gt : forall n m, decidable (n > m).
Proof.
  intros x y; unfold gt in |- *; apply dec_lt.
Qed.

Theorem dec_ge : forall n m, decidable (n >= m).
Proof.
  intros x y; unfold ge in |- *; apply dec_le.
Qed.

Theorem not_eq : forall n m, n <> m -> n < m \/ m < n.
Proof.
  intros x y H; elim (lt_eq_lt_dec x y);
    [ intros H1; elim H1;
      [ auto with arith | intros H2; absurd (x = y); assumption ]
      | auto with arith ].
Qed.


Theorem not_le : forall n m, ~ n <= m -> n > m.
Proof.
  intros x y H; elim (le_gt_dec x y);
    [ intros H1; absurd (x <= y); assumption | trivial with arith ].
Qed.

Theorem not_gt : forall n m, ~ n > m -> n <= m.
Proof.
  intros x y H; elim (le_gt_dec x y);
    [ trivial with arith | intros H1; absurd (x > y); assumption ].
Qed.

Theorem not_ge : forall n m, ~ n >= m -> n < m.
Proof.
  intros x y H; exact (not_le y x H).
Qed.

Theorem not_lt : forall n m, ~ n < m -> n >= m.
Proof.
  intros x y H; exact (not_gt y x H). 
Qed.


(** A ternary comparison function in the spirit of [Zcompare]. *)

Definition nat_compare (n m:nat) :=
  match lt_eq_lt_dec n m with 
    | inleft (left _) => Lt
    | inleft (right _) => Eq
    | inright _ => Gt
  end.

Lemma nat_compare_S : forall n m, nat_compare (S n) (S m) = nat_compare n m.
Proof.
  unfold nat_compare; intros.
  simpl; destruct (lt_eq_lt_dec n m) as [[H|H]|H]; simpl; auto.
Qed.

Lemma nat_compare_eq : forall n m, nat_compare n m = Eq -> n = m.
Proof.
  induction n; destruct m; simpl; auto.
  unfold nat_compare; destruct (lt_eq_lt_dec 0 (S m)) as [[H|H]|H]; 
    auto; intros; try discriminate.
  unfold nat_compare; destruct (lt_eq_lt_dec (S n) 0) as [[H|H]|H]; 
    auto; intros; try discriminate.
  rewrite nat_compare_S; auto.
Qed.

Lemma nat_compare_lt : forall n m, n<m <-> nat_compare n m = Lt.
Proof.
  induction n; destruct m; simpl.
  unfold nat_compare; simpl; intuition; [inversion H | discriminate H].
  split; auto with arith.
  split; [inversion 1 |].
  unfold nat_compare; destruct (lt_eq_lt_dec (S n) 0) as [[H|H]|H]; 
    auto; intros; try discriminate.
  rewrite nat_compare_S.
  generalize (IHn m); clear IHn; intuition.
Qed.

Lemma nat_compare_gt : forall n m, n>m <-> nat_compare n m = Gt.
Proof.
  induction n; destruct m; simpl.
  unfold nat_compare; simpl; intuition; [inversion H | discriminate H].
  split; [inversion 1 |].
  unfold nat_compare; destruct (lt_eq_lt_dec 0 (S m)) as [[H|H]|H]; 
    auto; intros; try discriminate.
  split; auto with arith.
  rewrite nat_compare_S.
  generalize (IHn m); clear IHn; intuition.
Qed.

Lemma nat_compare_le : forall n m, n<=m <-> nat_compare n m <> Gt.
Proof.
  split.
  intros.
  intro.
  destruct (nat_compare_gt n m).
  generalize (le_lt_trans _ _ _ H (H2 H0)).
  exact (lt_irrefl n).
  intros.
  apply not_gt.
  contradict H.
  destruct (nat_compare_gt n m); auto.
Qed.  

Lemma nat_compare_ge : forall n m, n>=m <-> nat_compare n m <> Lt.
Proof.
  split.
  intros.
  intro.
  destruct (nat_compare_lt n m).
  generalize (le_lt_trans _ _ _ H (H2 H0)).
  exact (lt_irrefl m).
  intros.
  apply not_lt.
  contradict H.
  destruct (nat_compare_lt n m); auto.
Qed.  

(** A boolean version of [le] over [nat]. *)

Fixpoint leb (m:nat) : nat -> bool :=
  match m with
    | O => fun _:nat => true
    | S m' =>
      fun n:nat => match n with
                     | O => false
                     | S n' => leb m' n'
                   end
  end.

Lemma leb_correct : forall m n:nat, m <= n -> leb m n = true.
Proof.
  induction m as [| m IHm]. trivial.
  destruct n. intro H. elim (le_Sn_O _ H).
  intros. simpl in |- *. apply IHm. apply le_S_n. assumption.
Qed.

Lemma leb_complete : forall m n:nat, leb m n = true -> m <= n.
Proof.
  induction m. trivial with arith.
  destruct n. intro H. discriminate H.
  auto with arith.
Qed.

Lemma leb_correct_conv : forall m n:nat, m < n -> leb n m = false.
Proof.
  intros. 
  generalize (leb_complete n m).
  destruct (leb n m); auto.
  intros.
  elim (lt_irrefl _ (lt_le_trans _ _ _ H (H0 (refl_equal true)))).
Qed.

Lemma leb_complete_conv : forall m n:nat, leb n m = false -> m < n.
Proof.
  intros. elim (le_or_lt n m). intro. conditional trivial rewrite leb_correct in H. discriminate H.
  trivial.
Qed.

Lemma leb_compare : forall n m, leb n m = true <-> nat_compare n m <> Gt.
Proof.
 induction n; destruct m; simpl.
 unfold nat_compare; simpl.
 intuition; discriminate.
 split; auto with arith.
 unfold nat_compare; destruct (lt_eq_lt_dec 0 (S m)) as [[H|H]|H]; 
  intuition; try discriminate.
 inversion H.
 split; try (intros; discriminate).
 unfold nat_compare; destruct (lt_eq_lt_dec (S n) 0) as [[H|H]|H]; 
  intuition; try discriminate.
 inversion H.
 rewrite nat_compare_S; auto.
Qed. 

