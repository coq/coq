(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Definition zerop n : {n = 0} + {0 < n}.
Proof.
  destruct n; auto with arith.
Defined.

Definition lt_eq_lt_dec n m : {n < m} + {n = m} + {m < n}.
Proof.
  induction n; destruct m; auto with arith.
  destruct (IHn m) as [H|H]; auto with arith.
  destruct H; auto with arith.
Defined.

Definition gt_eq_gt_dec n m : {m > n} + {n = m} + {n > m}.
Proof.
  intros; apply lt_eq_lt_dec; assumption.
Defined.

Definition le_lt_dec n m : {n <= m} + {m < n}.
Proof.
  induction n.
  auto with arith.
  destruct m.
  auto with arith.
  elim (IHn m); auto with arith.
Defined.

Definition le_le_S_dec n m : {n <= m} + {S m <= n}.
Proof.
  intros; exact (le_lt_dec n m).
Defined.

Definition le_ge_dec n m : {n <= m} + {n >= m}.
Proof.
  intros; elim (le_lt_dec n m); auto with arith.
Defined.

Definition le_gt_dec n m : {n <= m} + {n > m}.
Proof.
  intros; exact (le_lt_dec n m).
Defined.

Definition le_lt_eq_dec n m : n <= m -> {n < m} + {n = m}.
Proof.
  intros; destruct (lt_eq_lt_dec n m); auto with arith.
  intros; absurd (m < n); auto with arith.
Defined.

Theorem le_dec : forall n m, {n <= m} + {~ n <= m}.
Proof.
  intros n m. destruct (le_gt_dec n m).
   auto with arith.
   right. apply gt_not_le. assumption.
Defined.

Theorem lt_dec : forall n m, {n < m} + {~ n < m}.
Proof.
  intros; apply le_dec.
Defined.

Theorem gt_dec : forall n m, {n > m} + {~ n > m}.
Proof.
  intros; apply lt_dec.
Defined.

Theorem ge_dec : forall n m, {n >= m} + {~ n >= m}.
Proof.
  intros; apply le_dec.
Defined.

(** Proofs of decidability *)

Theorem dec_le : forall n m, decidable (n <= m).
Proof.
  intros n m; destruct (le_dec n m); unfold decidable; auto.
Qed.

Theorem dec_lt : forall n m, decidable (n < m).
Proof.
  intros; apply dec_le.
Qed.

Theorem dec_gt : forall n m, decidable (n > m).
Proof.
  intros; apply dec_lt.
Qed.

Theorem dec_ge : forall n m, decidable (n >= m).
Proof.
  intros; apply dec_le.
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

Fixpoint nat_compare n m :=
  match n, m with
   | O, O => Eq
   | O, S _ => Lt
   | S _, O => Gt
   | S n', S m' => nat_compare n' m'
  end.

Lemma nat_compare_S : forall n m, nat_compare (S n) (S m) = nat_compare n m.
Proof.
 reflexivity.
Qed.

Lemma nat_compare_eq_iff : forall n m, nat_compare n m = Eq <-> n = m.
Proof.
  induction n; destruct m; simpl; split; auto; try discriminate;
   destruct (IHn m); auto.
Qed.

Lemma nat_compare_eq : forall n m, nat_compare n m = Eq -> n = m.
Proof.
  intros; apply -> nat_compare_eq_iff; auto.
Qed.

Lemma nat_compare_lt : forall n m, n<m <-> nat_compare n m = Lt.
Proof.
  induction n; destruct m; simpl; split; auto with arith;
   try solve [inversion 1].
  destruct (IHn m); auto with arith.
  destruct (IHn m); auto with arith.
Qed.

Lemma nat_compare_gt : forall n m, n>m <-> nat_compare n m = Gt.
Proof.
  induction n; destruct m; simpl; split; auto with arith;
   try solve [inversion 1].
  destruct (IHn m); auto with arith.
  destruct (IHn m); auto with arith.
Qed.

Lemma nat_compare_le : forall n m, n<=m <-> nat_compare n m <> Gt.
Proof.
  split.
  intros LE; contradict LE.
   apply lt_not_le. apply <- nat_compare_gt; auto.
  intros NGT. apply not_lt. contradict NGT.
   apply -> nat_compare_gt; auto.
Qed.

Lemma nat_compare_ge : forall n m, n>=m <-> nat_compare n m <> Lt.
Proof.
  split.
  intros GE; contradict GE.
   apply lt_not_le. apply <- nat_compare_lt; auto.
  intros NLT. apply not_lt. contradict NLT.
   apply -> nat_compare_lt; auto.
Qed.

Lemma nat_compare_spec : forall x y, CompSpec eq lt x y (nat_compare x y).
Proof.
 intros.
 destruct (nat_compare x y) as [ ]_eqn; constructor.
 apply nat_compare_eq; auto.
 apply <- nat_compare_lt; auto.
 apply <- nat_compare_gt; auto.
Qed.


(** Some projections of the above equivalences. *)

Lemma nat_compare_Lt_lt : forall n m, nat_compare n m = Lt -> n<m.
Proof.
  intros; apply <- nat_compare_lt; auto.
Qed.

Lemma nat_compare_Gt_gt : forall n m, nat_compare n m = Gt -> n>m.
Proof.
  intros; apply <- nat_compare_gt; auto.
Qed.

(** A previous definition of [nat_compare] in terms of [lt_eq_lt_dec].
    The new version avoids the creation of proof parts. *)

Definition nat_compare_alt (n m:nat) :=
  match lt_eq_lt_dec n m with
    | inleft (left _) => Lt
    | inleft (right _) => Eq
    | inright _ => Gt
  end.

Lemma nat_compare_equiv: forall n m,
 nat_compare n m = nat_compare_alt n m.
Proof.
  intros; unfold nat_compare_alt; destruct lt_eq_lt_dec as [[LT|EQ]|GT].
  apply -> nat_compare_lt; auto.
  apply <- nat_compare_eq_iff; auto.
  apply -> nat_compare_gt; auto.
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

Lemma leb_correct : forall m n, m <= n -> leb m n = true.
Proof.
  induction m as [| m IHm]. trivial.
  destruct n. intro H. elim (le_Sn_O _ H).
  intros. simpl in |- *. apply IHm. apply le_S_n. assumption.
Qed.

Lemma leb_complete : forall m n, leb m n = true -> m <= n.
Proof.
  induction m. trivial with arith.
  destruct n. intro H. discriminate H.
  auto with arith.
Qed.

Lemma leb_iff : forall m n, leb m n = true <-> m <= n.
Proof.
  split; auto using leb_correct, leb_complete.
Qed.

Lemma leb_correct_conv : forall m n, m < n -> leb n m = false.
Proof.
  intros.
  generalize (leb_complete n m).
  destruct (leb n m); auto.
  intros; elim (lt_not_le m n); auto.
Qed.

Lemma leb_complete_conv : forall m n, leb n m = false -> m < n.
Proof.
  intros m n EQ. apply not_le.
  intro LE. apply leb_correct in LE. rewrite LE in EQ; discriminate.
Qed.

Lemma leb_iff_conv : forall m n, leb n m = false <-> m < n.
Proof.
  split; auto using leb_complete_conv, leb_correct_conv.
Qed.

Lemma leb_compare : forall n m, leb n m = true <-> nat_compare n m <> Gt.
Proof.
 split; intros.
 apply -> nat_compare_le. auto using leb_complete.
 apply leb_correct. apply <- nat_compare_le; auto.
Qed.

