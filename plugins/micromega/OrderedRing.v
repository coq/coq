(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import Setoid.
Require Import Ring.

(** Generic properties of ordered rings on a setoid equality *)

Set Implicit Arguments.

Module Import OrderedRingSyntax.
Export RingSyntax.

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x [=] y" (at level 70, no associativity).
Reserved Notation "x [~=] y" (at level 70, no associativity).
Reserved Notation "x [<] y" (at level 70, no associativity).
Reserved Notation "x [<=] y" (at level 70, no associativity).
End OrderedRingSyntax.

Section DEFINITIONS.

Variable R : Type.
Variable (rO rI : R) (rplus rtimes rminus: R -> R -> R) (ropp : R -> R).
Variable req rle rlt : R -> R -> Prop.
Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).

Record SOR : Type := mk_SOR_theory {
  SORsetoid : Setoid_Theory R req;
  SORplus_wd : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 + y1 == x2 + y2;
  SORtimes_wd : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 * y1 == x2 * y2;
  SORopp_wd : forall x1 x2, x1 == x2 ->  -x1 == -x2;
  SORle_wd : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> (x1 <= y1 <-> x2 <= y2);
  SORlt_wd : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> (x1 < y1 <-> x2 < y2);
  SORrt : ring_theory rO rI rplus rtimes rminus ropp req;
  SORle_refl : forall n : R, n <= n;
  SORle_antisymm : forall n m : R, n <= m -> m <= n -> n == m;
  SORle_trans : forall n m p : R, n <= m -> m <= p -> n <= p;
  SORlt_le_neq : forall n m : R, n < m <-> n <= m /\ n ~= m;
  SORlt_trichotomy : forall n m : R,  n < m \/ n == m \/ m < n;
  SORplus_le_mono_l : forall n m p : R, n <= m -> p + n <= p + m;
  SORtimes_pos_pos : forall n m : R, 0 < n -> 0 < m -> 0 < n * m;
  SORneq_0_1 : 0 ~= 1
}.

(* We cannot use Relation_Definitions.order.ord_antisym and
Relations_1.Antisymmetric because they refer to Leibniz equality *)

End DEFINITIONS.

Section STRICT_ORDERED_RING.

Variable R : Type.
Variable (rO rI : R) (rplus rtimes rminus: R -> R -> R) (ropp : R -> R).
Variable req rle rlt : R -> R -> Prop.

Variable sor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).


Add Relation R req
  reflexivity proved by sor.(SORsetoid).(@Equivalence_Reflexive _ _)
  symmetry proved by sor.(SORsetoid).(@Equivalence_Symmetric _ _)
  transitivity proved by sor.(SORsetoid).(@Equivalence_Transitive _ _)
as sor_setoid.


Add Morphism rplus with signature req ==> req ==> req as rplus_morph.
Proof.
exact sor.(SORplus_wd).
Qed.
Add Morphism rtimes with signature req ==> req ==> req as rtimes_morph.
Proof.
exact sor.(SORtimes_wd).
Qed.
Add Morphism ropp with signature req ==> req as ropp_morph.
Proof.
exact sor.(SORopp_wd).
Qed.
Add Morphism rle with signature req ==> req ==> iff as rle_morph.
Proof.
exact sor.(SORle_wd).
Qed.
Add Morphism rlt with signature req ==> req ==> iff as rlt_morph.
Proof.
exact sor.(SORlt_wd).
Qed.

Add Ring SOR : sor.(SORrt).

Add Morphism rminus with signature req ==> req ==> req as rminus_morph.
Proof.
intros x1 x2 H1 y1 y2 H2.
rewrite (sor.(SORrt).(Rsub_def) x1 y1).
rewrite (sor.(SORrt).(Rsub_def) x2 y2).
rewrite H1; now rewrite H2.
Qed.

Theorem Rneq_symm : forall n m : R, n ~= m -> m ~= n.
Proof.
intros n m H1 H2; rewrite H2 in H1; now apply H1.
Qed.

(* Propeties of plus, minus and opp *)

Theorem Rplus_0_l : forall n : R, 0 + n == n.
Proof.
intro; ring.
Qed.

Theorem Rplus_0_r : forall n : R, n + 0 == n.
Proof.
intro; ring.
Qed.

Theorem Rtimes_0_r : forall n : R, n * 0 == 0.
Proof.
intro; ring.
Qed.

Theorem Rplus_comm : forall n m : R, n + m == m + n.
Proof.
intros; ring.
Qed.

Theorem Rtimes_0_l : forall n : R, 0 * n == 0.
Proof.
intro; ring.
Qed.

Theorem Rtimes_comm : forall n m : R, n * m == m * n.
Proof.
intros; ring.
Qed.

Theorem Rminus_eq_0 : forall n m : R, n - m == 0 <-> n == m.
Proof.
intros n m.
split; intro H. setoid_replace n with ((n - m) + m) by ring. rewrite H.
now rewrite Rplus_0_l.
rewrite H; ring.
Qed.

Theorem Rplus_cancel_l : forall n m p : R, p + n == p + m <-> n == m.
Proof.
intros n m p; split; intro H.
setoid_replace n with (- p + (p + n)) by ring.
setoid_replace m with (- p + (p + m)) by ring. now rewrite H.
now rewrite H.
Qed.

(* Relations *)

Theorem Rle_refl : forall n : R, n <= n.
Proof sor.(SORle_refl).

Theorem Rle_antisymm : forall n m : R, n <= m -> m <= n -> n == m.
Proof sor.(SORle_antisymm).

Theorem Rle_trans : forall n m p : R, n <= m -> m <= p -> n <= p.
Proof sor.(SORle_trans).

Theorem Rlt_trichotomy : forall n m : R,  n < m \/ n == m \/ m < n.
Proof sor.(SORlt_trichotomy).

Theorem Rlt_le_neq : forall n m : R, n < m <-> n <= m /\ n ~= m.
Proof sor.(SORlt_le_neq).

Theorem Rneq_0_1 : 0 ~= 1.
Proof sor.(SORneq_0_1).

Theorem Req_em : forall n m : R, n == m \/ n ~= m.
Proof.
intros n m. destruct (Rlt_trichotomy n m) as [H | [H | H]]; try rewrite Rlt_le_neq in H.
right; now destruct H.
now left.
right; apply Rneq_symm; now destruct H.
Qed.

Theorem Req_dne : forall n m : R, ~ ~ n == m <-> n == m.
Proof.
intros n m; destruct (Req_em n m) as [H | H].
split; auto.
split. intro H1; false_hyp H H1. auto.
Qed.

Theorem Rle_lt_eq : forall n m : R, n <= m <-> n < m \/ n == m.
Proof.
intros n m; rewrite Rlt_le_neq.
split; [intro H | intros [[H1 H2] | H]].
destruct (Req_em n m) as [H1 | H1]. now right. left; now split.
assumption.
rewrite H; apply Rle_refl.
Qed.

Ltac le_less := rewrite Rle_lt_eq; left; try assumption.
Ltac le_equal := rewrite Rle_lt_eq; right; try reflexivity; try assumption.
Ltac le_elim H := rewrite Rle_lt_eq in H; destruct H as [H | H].

Theorem Rlt_trans : forall n m p : R, n < m -> m < p -> n < p.
Proof.
intros n m p; repeat rewrite Rlt_le_neq; intros [H1 H2] [H3 H4]; split.
now apply Rle_trans with m.
intro H. rewrite H in H1. pose proof (Rle_antisymm H3 H1). now apply H4.
Qed.

Theorem Rle_lt_trans : forall n m p : R, n <= m -> m < p -> n < p.
Proof.
intros n m p H1 H2; le_elim H1.
now apply Rlt_trans with (m := m). now rewrite H1.
Qed.

Theorem Rlt_le_trans : forall n m p : R, n < m -> m <= p -> n < p.
Proof.
intros n m p H1 H2; le_elim H2.
now apply Rlt_trans with (m := m). now rewrite <- H2.
Qed.

Theorem Rle_gt_cases : forall n m : R, n <= m \/ m < n.
Proof.
intros n m; destruct (Rlt_trichotomy n m) as [H | [H | H]].
left; now le_less. left; now le_equal. now right.
Qed.

Theorem Rlt_neq : forall n m : R, n < m -> n ~= m.
Proof.
intros n m; rewrite Rlt_le_neq; now intros [_ H].
Qed.

Theorem Rle_ngt : forall n m : R, n <= m <-> ~ m < n.
Proof.
intros n m; split.
intros H H1; assert (H2 : n < n) by now apply Rle_lt_trans with m. now apply (Rlt_neq H2).
intro H. destruct (Rle_gt_cases n m) as [H1 | H1]. assumption. false_hyp H1 H.
Qed.

Theorem Rlt_nge : forall n m : R, n < m <-> ~ m <= n.
Proof.
intros n m; split.
intros H H1; assert (H2 : n < n) by now apply Rlt_le_trans with m. now apply (Rlt_neq H2).
intro H. destruct (Rle_gt_cases m n) as [H1 | H1]. false_hyp H1 H. assumption.
Qed.

(* Plus, minus and order *)

Theorem Rplus_le_mono_l : forall n m p : R, n <= m <-> p + n <= p + m.
Proof.
intros n m p; split.
apply sor.(SORplus_le_mono_l).
intro H. apply (sor.(SORplus_le_mono_l) (p + n) (p + m) (- p)) in H.
setoid_replace (- p + (p + n)) with n in H by ring.
setoid_replace (- p + (p + m)) with m in H by ring. assumption.
Qed.

Theorem Rplus_le_mono_r : forall n m p : R, n <= m <-> n + p <= m + p.
Proof.
intros n m p; rewrite (Rplus_comm n p); rewrite (Rplus_comm m p).
apply Rplus_le_mono_l.
Qed.

Theorem Rplus_lt_mono_l : forall n m p : R, n < m <-> p + n < p + m.
Proof.
intros n m p; do 2 rewrite Rlt_le_neq. rewrite Rplus_cancel_l.
now rewrite <- Rplus_le_mono_l.
Qed.

Theorem Rplus_lt_mono_r : forall n m p : R, n < m <-> n + p < m + p.
Proof.
intros n m p.
rewrite (Rplus_comm n p); rewrite (Rplus_comm m p); apply Rplus_lt_mono_l.
Qed.

Theorem Rplus_lt_mono : forall n m p q : R, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply Rlt_trans with (m + p); [now apply -> Rplus_lt_mono_r | now apply -> Rplus_lt_mono_l].
Qed.

Theorem Rplus_le_mono : forall n m p q : R, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply Rle_trans with (m + p); [now apply -> Rplus_le_mono_r | now apply -> Rplus_le_mono_l].
Qed.

Theorem Rplus_lt_le_mono : forall n m p q : R, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply Rlt_le_trans with (m + p); [now apply -> Rplus_lt_mono_r | now apply -> Rplus_le_mono_l].
Qed.

Theorem Rplus_le_lt_mono : forall n m p q : R, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply Rle_lt_trans with (m + p); [now apply -> Rplus_le_mono_r | now apply -> Rplus_lt_mono_l].
Qed.

Theorem Rplus_pos_pos : forall n m : R, 0 < n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (Rplus_0_l 0). now apply Rplus_lt_mono.
Qed.

Theorem Rplus_pos_nonneg : forall n m : R, 0 < n -> 0 <= m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (Rplus_0_l 0). now apply Rplus_lt_le_mono.
Qed.

Theorem Rplus_nonneg_pos : forall n m : R, 0 <= n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (Rplus_0_l 0). now apply Rplus_le_lt_mono.
Qed.

Theorem Rplus_nonneg_nonneg : forall n m : R, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
intros n m H1 H2. rewrite <- (Rplus_0_l 0). now apply Rplus_le_mono.
Qed.

Theorem Rle_le_minus : forall n m : R, n <= m <-> 0 <= m - n.
Proof.
intros n m. rewrite (@Rplus_le_mono_r n m (- n)).
setoid_replace (n + - n) with 0 by ring.
now setoid_replace (m + - n) with (m - n) by ring.
Qed.

Theorem Rlt_lt_minus : forall n m : R, n < m <-> 0 < m - n.
Proof.
intros n m. rewrite (@Rplus_lt_mono_r n m (- n)).
setoid_replace (n + - n) with 0 by ring.
now setoid_replace (m + - n) with (m - n) by ring.
Qed.

Theorem Ropp_lt_mono : forall n m : R, n < m <-> - m < - n.
Proof.
intros n m. split; intro H.
apply -> (@Rplus_lt_mono_l n m (- n - m)) in H.
setoid_replace (- n - m + n) with (- m) in H by ring.
now setoid_replace (- n - m + m) with (- n) in H by ring.
apply -> (@Rplus_lt_mono_l (- m) (- n) (n + m)) in H.
setoid_replace (n + m + - m) with n in H by ring.
now setoid_replace (n + m + - n) with m in H by ring.
Qed.

Theorem Ropp_pos_neg : forall n : R, 0 < - n <-> n < 0.
Proof.
intro n; rewrite (Ropp_lt_mono n 0). now setoid_replace (- 0) with 0 by ring.
Qed.

(* Times and order *)

Theorem Rtimes_pos_pos : forall n m : R, 0 < n -> 0 < m -> 0 < n * m.
Proof sor.(SORtimes_pos_pos).

Theorem Rtimes_nonneg_nonneg : forall n m : R, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
intros n m H1 H2.
le_elim H1. le_elim H2.
le_less; now apply Rtimes_pos_pos.
rewrite <- H2; rewrite Rtimes_0_r; le_equal.
rewrite <- H1; rewrite Rtimes_0_l; le_equal.
Qed.

Theorem Rtimes_pos_neg : forall n m : R, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m H1 H2. apply -> Ropp_pos_neg.
setoid_replace (- (n * m)) with (n * (- m)) by ring.
apply Rtimes_pos_pos. assumption. now apply <- Ropp_pos_neg.
Qed.

Theorem Rtimes_neg_neg : forall n m : R, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2.
setoid_replace (n * m) with ((- n) * (- m)) by ring.
apply Rtimes_pos_pos; now apply <- Ropp_pos_neg.
Qed.

Theorem Rtimes_square_nonneg : forall n : R, 0 <= n * n.
Proof.
intro n; destruct (Rlt_trichotomy 0 n) as [H | [H | H]].
le_less; now apply Rtimes_pos_pos.
rewrite <- H, Rtimes_0_l; le_equal.
le_less; now apply Rtimes_neg_neg.
Qed.

Theorem Rtimes_neq_0 : forall n m : R, n ~= 0 /\ m ~= 0 -> n * m ~= 0.
Proof.
intros n m [H1 H2].
destruct (Rlt_trichotomy n 0) as [H3 | [H3 | H3]];
destruct (Rlt_trichotomy m 0) as [H4 | [H4 | H4]];
try (false_hyp H3 H1); try (false_hyp H4 H2).
apply Rneq_symm. apply Rlt_neq. now apply Rtimes_neg_neg.
apply Rlt_neq. rewrite Rtimes_comm. now apply Rtimes_pos_neg.
apply Rlt_neq. now apply Rtimes_pos_neg.
apply Rneq_symm. apply Rlt_neq. now apply Rtimes_pos_pos.
Qed.

(* The following theorems are used to build a morphism from Z to R and
prove its properties in ZCoeff.v. They are not used in RingMicromega.v. *)

(* Surprisingly, multilication is needed to prove the following theorem *)

Theorem Ropp_neg_pos : forall n : R, - n < 0 <-> 0 < n.
Proof.
intro n; setoid_replace n with (- - n) by ring. rewrite Ropp_pos_neg.
now setoid_replace (- - n) with n by ring.
Qed.

Theorem Rlt_0_1 : 0 < 1.
Proof.
apply <- Rlt_le_neq. split.
setoid_replace 1 with (1 * 1) by ring. apply Rtimes_square_nonneg.
apply Rneq_0_1.
Qed.

Theorem Rlt_succ_r : forall n : R, n < 1 + n.
Proof.
intro n. rewrite <- (Rplus_0_l n); setoid_replace (1 + (0 + n)) with (1 + n) by ring.
apply -> Rplus_lt_mono_r. apply Rlt_0_1.
Qed.

Theorem Rlt_lt_succ : forall n m : R, n < m -> n < 1 + m.
Proof.
intros n m H; apply Rlt_trans with m. assumption. apply Rlt_succ_r.
Qed.

(*Theorem Rtimes_lt_mono_pos_l : forall n m p : R, 0 < p -> n < m -> p * n < p * m.
Proof.
intros n m p H1 H2. apply <- Rlt_lt_minus.
setoid_replace (p * m - p * n) with (p * (m - n)) by ring.
apply Rtimes_pos_pos. assumption. now apply -> Rlt_lt_minus.
Qed.*)

End STRICT_ORDERED_RING.

