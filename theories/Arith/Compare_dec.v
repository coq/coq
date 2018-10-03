(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Le Lt Gt Decidable PeanoNat.

Local Open Scope nat_scope.

Implicit Types m n x y : nat.

Definition zerop n : {n = 0} + {0 < n}.
Proof.
  destruct n; auto with arith.
Defined.

Definition lt_eq_lt_dec n m : {n < m} + {n = m} + {m < n}.
Proof.
  induction n in m |- *; destruct m; auto with arith.
  destruct (IHn m) as [H|H]; auto with arith.
  destruct H; auto with arith.
Defined.

Definition gt_eq_gt_dec n m : {m > n} + {n = m} + {n > m}.
Proof.
  now apply lt_eq_lt_dec.
Defined.

Definition le_lt_dec n m : {n <= m} + {m < n}.
Proof.
  induction n in m |- *.
  - left; auto with arith.
  - destruct m.
    + right; auto with arith.
    + elim (IHn m); [left|right]; auto with arith.
Defined.

Definition le_le_S_dec n m : {n <= m} + {S m <= n}.
Proof.
  exact (le_lt_dec n m).
Defined.

Definition le_ge_dec n m : {n <= m} + {n >= m}.
Proof.
  elim (le_lt_dec n m); auto with arith.
Defined.

Definition le_gt_dec n m : {n <= m} + {n > m}.
Proof.
  exact (le_lt_dec n m).
Defined.

Definition le_lt_eq_dec n m : n <= m -> {n < m} + {n = m}.
Proof.
  intros; destruct (lt_eq_lt_dec n m); auto with arith.
  intros; absurd (m < n); auto with arith.
Defined.

Theorem le_dec n m : {n <= m} + {~ n <= m}.
Proof.
  destruct (le_gt_dec n m).
  - now left.
  - right. now apply gt_not_le.
Defined.

Theorem lt_dec n m : {n < m} + {~ n < m}.
Proof.
  apply le_dec.
Defined.

Theorem gt_dec n m : {n > m} + {~ n > m}.
Proof.
  apply lt_dec.
Defined.

Theorem ge_dec n m : {n >= m} + {~ n >= m}.
Proof.
  apply le_dec.
Defined.

(** Proofs of decidability *)

Theorem dec_le n m : decidable (n <= m).
Proof.
  apply Nat.le_decidable.
Qed.

Theorem dec_lt n m : decidable (n < m).
Proof.
  apply Nat.lt_decidable.
Qed.

Theorem dec_gt n m : decidable (n > m).
Proof.
  apply Nat.lt_decidable.
Qed.

Theorem dec_ge n m : decidable (n >= m).
Proof.
  apply Nat.le_decidable.
Qed.

Theorem not_eq n m : n <> m -> n < m \/ m < n.
Proof.
  apply Nat.lt_gt_cases.
Qed.

Theorem not_le n m : ~ n <= m -> n > m.
Proof.
  apply Nat.nle_gt.
Qed.

Theorem not_gt n m : ~ n > m -> n <= m.
Proof.
  apply Nat.nlt_ge.
Qed.

Theorem not_ge n m : ~ n >= m -> n < m.
Proof.
  apply Nat.nle_gt.
Qed.

Theorem not_lt n m : ~ n < m -> n >= m.
Proof.
  apply Nat.nlt_ge.
Qed.


(** A ternary comparison function in the spirit of [Z.compare].
    See now [Nat.compare] and its properties.
    In scope [nat_scope], the notation for [Nat.compare] is "?=" *)

Notation nat_compare := Nat.compare (compat "8.7").

Notation nat_compare_spec := Nat.compare_spec (compat "8.7").
Notation nat_compare_eq_iff := Nat.compare_eq_iff (compat "8.7").
Notation nat_compare_S := Nat.compare_succ (only parsing).

Lemma nat_compare_lt n m : n<m <-> (n ?= m) = Lt.
Proof.
 symmetry. apply Nat.compare_lt_iff.
Qed.

Lemma nat_compare_gt n m : n>m <-> (n ?= m) = Gt.
Proof.
 symmetry. apply Nat.compare_gt_iff.
Qed.

Lemma nat_compare_le n m : n<=m <-> (n ?= m) <> Gt.
Proof.
 symmetry. apply Nat.compare_le_iff.
Qed.

Lemma nat_compare_ge n m : n>=m <-> (n ?= m) <> Lt.
Proof.
 symmetry. apply Nat.compare_ge_iff.
Qed.

(** Some projections of the above equivalences. *)

Lemma nat_compare_eq n m : (n ?= m) = Eq -> n = m.
Proof.
  apply Nat.compare_eq_iff.
Qed.

Lemma nat_compare_Lt_lt n m : (n ?= m) = Lt -> n<m.
Proof.
  apply Nat.compare_lt_iff.
Qed.

Lemma nat_compare_Gt_gt n m : (n ?= m) = Gt -> n>m.
Proof.
  apply Nat.compare_gt_iff.
Qed.

(** A previous definition of [nat_compare] in terms of [lt_eq_lt_dec].
    The new version avoids the creation of proof parts. *)

Definition nat_compare_alt (n m:nat) :=
  match lt_eq_lt_dec n m with
    | inleft (left _) => Lt
    | inleft (right _) => Eq
    | inright _ => Gt
  end.

Lemma nat_compare_equiv n m : (n ?= m) = nat_compare_alt n m.
Proof.
  unfold nat_compare_alt; destruct lt_eq_lt_dec as [[|]|].
  - now apply Nat.compare_lt_iff.
  - now apply Nat.compare_eq_iff.
  - now apply Nat.compare_gt_iff.
Qed.

(** A boolean version of [le] over [nat].
    See now [Nat.leb] and its properties.
    In scope [nat_scope], the notation for [Nat.leb] is "<=?" *)

Notation leb := Nat.leb (only parsing).

Notation leb_iff := Nat.leb_le (only parsing).

Lemma leb_iff_conv m n : (n <=? m) = false <-> m < n.
Proof.
 rewrite Nat.leb_nle. apply Nat.nle_gt.
Qed.

Lemma leb_correct m n : m <= n -> (m <=? n) = true.
Proof.
 apply Nat.leb_le.
Qed.

Lemma leb_complete m n : (m <=? n) = true -> m <= n.
Proof.
 apply Nat.leb_le.
Qed.

Lemma leb_correct_conv m n : m < n -> (n <=? m) = false.
Proof.
 apply leb_iff_conv.
Qed.

Lemma leb_complete_conv m n : (n <=? m) = false -> m < n.
Proof.
 apply leb_iff_conv.
Qed.

Lemma leb_compare n m : (n <=? m) = true <-> (n ?= m) <> Gt.
Proof.
 rewrite Nat.compare_le_iff. apply Nat.leb_le.
Qed.
