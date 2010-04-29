(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Import BinPos.
Require Import BinInt.
Require Import Arith_base.
Require Import Decidable.
Require Import Zcompare.

Open Local Scope Z_scope.

Implicit Types x y z : Z.

(*********************************************************)
(** Properties of the order relations on binary integers *)

(** * Trichotomy *)

Theorem Ztrichotomy_inf : forall n m:Z, {n < m} + {n = m} + {n > m}.
Proof.
  unfold Zgt, Zlt in |- *; intros m n; assert (H := refl_equal (m ?= n)).
  set (x := m ?= n) in H at 2 |- *.
  destruct x;
    [ left; right; rewrite Zcompare_Eq_eq with (1 := H) | left; left | right ];
    reflexivity.
Qed.

Theorem Ztrichotomy : forall n m:Z, n < m \/ n = m \/ n > m.
Proof.
  intros m n; destruct (Ztrichotomy_inf m n) as [[Hlt| Heq]| Hgt];
    [ left | right; left | right; right ]; assumption.
Qed.

(**********************************************************************)
(** * Decidability of equality and order on Z *)

Theorem dec_eq : forall n m:Z, decidable (n = m).
Proof.
  intros x y; unfold decidable in |- *; elim (Zcompare_Eq_iff_eq x y);
    intros H1 H2; elim (Dcompare (x ?= y));
      [ tauto
	| intros H3; right; unfold not in |- *; intros H4; elim H3; rewrite (H2 H4);
	  intros H5; discriminate H5 ].
Qed.

Theorem dec_Zne : forall n m:Z, decidable (Zne n m).
Proof.
  intros x y; unfold decidable, Zne in |- *; elim (Zcompare_Eq_iff_eq x y).
  intros H1 H2; elim (Dcompare (x ?= y));
    [ right; rewrite H1; auto
      | left; unfold not in |- *; intro; absurd ((x ?= y) = Eq);
	[ elim H; intros HR; rewrite HR; discriminate | auto ] ].
Qed.

Theorem dec_Zle : forall n m:Z, decidable (n <= m).
Proof.
  intros x y; unfold decidable, Zle in |- *; elim (x ?= y);
    [ left; discriminate
      | left; discriminate
      | right; unfold not in |- *; intros H; apply H; trivial with arith ].
Qed.

Theorem dec_Zgt : forall n m:Z, decidable (n > m).
Proof.
  intros x y; unfold decidable, Zgt in |- *; elim (x ?= y);
    [ right; discriminate | right; discriminate | auto with arith ].
Qed.

Theorem dec_Zge : forall n m:Z, decidable (n >= m).
Proof.
  intros x y; unfold decidable, Zge in |- *; elim (x ?= y);
    [ left; discriminate
      | right; unfold not in |- *; intros H; apply H; trivial with arith
      | left; discriminate ].
Qed.

Theorem dec_Zlt : forall n m:Z, decidable (n < m).
Proof.
  intros x y; unfold decidable, Zlt in |- *; elim (x ?= y);
    [ right; discriminate | auto with arith | right; discriminate ].
Qed.

Theorem not_Zeq : forall n m:Z, n <> m -> n < m \/ m < n.
Proof.
  intros x y; elim (Dcompare (x ?= y));
    [ intros H1 H2; absurd (x = y);
      [ assumption | elim (Zcompare_Eq_iff_eq x y); auto with arith ]
      | unfold Zlt in |- *; intros H; elim H; intros H1;
	[ auto with arith
	  | right; elim (Zcompare_Gt_Lt_antisym x y); auto with arith ] ].
Qed.

(** * Relating strict and large orders *)

Lemma Zgt_lt : forall n m:Z, n > m -> m < n.
Proof.
  unfold Zgt, Zlt in |- *; intros m n H; elim (Zcompare_Gt_Lt_antisym m n);
    auto with arith.
Qed.

Lemma Zlt_gt : forall n m:Z, n < m -> m > n.
Proof.
  unfold Zgt, Zlt in |- *; intros m n H; elim (Zcompare_Gt_Lt_antisym n m);
    auto with arith.
Qed.

Lemma Zge_le : forall n m:Z, n >= m -> m <= n.
Proof.
  intros m n; change (~ m < n -> ~ n > m) in |- *; unfold not in |- *;
    intros H1 H2; apply H1; apply Zgt_lt; assumption.
Qed.

Lemma Zle_ge : forall n m:Z, n <= m -> m >= n.
Proof.
  intros m n; change (~ m > n -> ~ n < m) in |- *; unfold not in |- *;
    intros H1 H2; apply H1; apply Zlt_gt; assumption.
Qed.

Lemma Zle_not_gt : forall n m:Z, n <= m -> ~ n > m.
Proof.
  trivial.
Qed.

Lemma Zgt_not_le : forall n m:Z, n > m -> ~ n <= m.
Proof.
  intros n m H1 H2; apply H2; assumption.
Qed.

Lemma Zle_not_lt : forall n m:Z, n <= m -> ~ m < n.
Proof.
  intros n m H1 H2.
  assert (H3 := Zlt_gt _ _ H2).
  apply Zle_not_gt with n m; assumption.
Qed.

Lemma Zlt_not_le : forall n m:Z, n < m -> ~ m <= n.
Proof.
  intros n m H1 H2.
  apply Zle_not_lt with m n; assumption.
Qed.

Lemma Znot_ge_lt : forall n m:Z, ~ n >= m -> n < m.
Proof.
  unfold Zge, Zlt in |- *; intros x y H; apply dec_not_not;
    [ exact (dec_Zlt x y) | assumption ].
Qed.

Lemma Znot_lt_ge : forall n m:Z, ~ n < m -> n >= m.
Proof.
  unfold Zlt, Zge in |- *; auto with arith.
Qed.

Lemma Znot_gt_le : forall n m:Z, ~ n > m -> n <= m.
Proof.
  trivial.
Qed.

Lemma Znot_le_gt : forall n m:Z, ~ n <= m -> n > m.
Proof.
  unfold Zle, Zgt in |- *; intros x y H; apply dec_not_not;
    [ exact (dec_Zgt x y) | assumption ].
Qed.

Lemma Zge_iff_le : forall n m:Z, n >= m <-> m <= n.
Proof.
  intros x y; intros. split. intro. apply Zge_le. assumption.
  intro. apply Zle_ge. assumption.
Qed.

Lemma Zgt_iff_lt : forall n m:Z, n > m <-> m < n.
Proof.
  intros x y. split. intro. apply Zgt_lt. assumption.
  intro. apply Zlt_gt. assumption.
Qed.

(** * Equivalence and order properties *)

(** Reflexivity *)

Lemma Zle_refl : forall n:Z, n <= n.
Proof.
  intros n; unfold Zle in |- *; rewrite (Zcompare_refl n); discriminate.
Qed.

Lemma Zeq_le : forall n m:Z, n = m -> n <= m.
Proof.
  intros; rewrite H; apply Zle_refl.
Qed.

Hint Resolve Zle_refl: zarith.

(** Antisymmetry *)

Lemma Zle_antisym : forall n m:Z, n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2; destruct (Ztrichotomy n m) as [Hlt| [Heq| Hgt]].
  absurd (m > n); [ apply Zle_not_gt | apply Zlt_gt ]; assumption.
  assumption.
  absurd (n > m); [ apply Zle_not_gt | idtac ]; assumption.
Qed.

(** Asymmetry *)

Lemma Zgt_asym : forall n m:Z, n > m -> ~ m > n.
Proof.
  unfold Zgt in |- *; intros n m H; elim (Zcompare_Gt_Lt_antisym n m);
    intros H1 H2; rewrite H1; [ discriminate | assumption ].
Qed.

Lemma Zlt_asym : forall n m:Z, n < m -> ~ m < n.
Proof.
  intros n m H H1; assert (H2 : m > n). apply Zlt_gt; assumption.
  assert (H3 : n > m). apply Zlt_gt; assumption.
  apply Zgt_asym with m n; assumption.
Qed.

(** Irreflexivity *)

Lemma Zgt_irrefl : forall n:Z, ~ n > n.
Proof.
  intros n H; apply (Zgt_asym n n H H).
Qed.

Lemma Zlt_irrefl : forall n:Z, ~ n < n.
Proof.
  intros n H; apply (Zlt_asym n n H H).
Qed.

Lemma Zlt_not_eq : forall n m:Z, n < m -> n <> m.
Proof.
  unfold not in |- *; intros x y H H0.
  rewrite H0 in H.
  apply (Zlt_irrefl _ H).
Qed.

(** Large = strict or equal *)

Lemma Zlt_le_weak : forall n m:Z, n < m -> n <= m.
Proof.
  intros n m Hlt; apply Znot_gt_le; apply Zgt_asym; apply Zlt_gt; assumption.
Qed.

Lemma Zle_lt_or_eq : forall n m:Z, n <= m -> n < m \/ n = m.
Proof.
  intros n m H; destruct (Ztrichotomy n m) as [Hlt| [Heq| Hgt]];
    [ left; assumption
      | right; assumption
      | absurd (n > m); [ apply Zle_not_gt | idtac ]; assumption ].
Qed.

Lemma Zle_lt_or_eq_iff : forall n m, n <= m <-> n < m \/ n = m.
Proof.
  unfold Zle, Zlt. intros.
  generalize (Zcompare_Eq_iff_eq n m).
  destruct (n ?= m); intuition; discriminate.
Qed.

(** Dichotomy *)

Lemma Zle_or_lt : forall n m:Z, n <= m \/ m < n.
Proof.
  intros n m; destruct (Ztrichotomy n m) as [Hlt| [Heq| Hgt]];
    [ left; apply Znot_gt_le; intro Hgt; assert (Hgt' := Zlt_gt _ _ Hlt);
      apply Zgt_asym with m n; assumption
      | left; rewrite Heq; apply Zle_refl
      | right; apply Zgt_lt; assumption ].
Qed.

(** Transitivity of strict orders *)

Lemma Zgt_trans : forall n m p:Z, n > m -> m > p -> n > p.
Proof.
  exact Zcompare_Gt_trans.
Qed.

Lemma Zlt_trans : forall n m p:Z, n < m -> m < p -> n < p.
Proof.
  exact Zcompare_Lt_trans.
Qed.

(** Mixed transitivity *)

Lemma Zle_gt_trans : forall n m p:Z, m <= n -> m > p -> n > p.
Proof.
  intros n m p H1 H2; destruct (Zle_lt_or_eq m n H1) as [Hlt| Heq];
    [ apply Zgt_trans with m; [ apply Zlt_gt; assumption | assumption ]
      | rewrite <- Heq; assumption ].
Qed.

Lemma Zgt_le_trans : forall n m p:Z, n > m -> p <= m -> n > p.
Proof.
  intros n m p H1 H2; destruct (Zle_lt_or_eq p m H2) as [Hlt| Heq];
    [ apply Zgt_trans with m; [ assumption | apply Zlt_gt; assumption ]
      | rewrite Heq; assumption ].
Qed.

Lemma Zlt_le_trans : forall n m p:Z, n < m -> m <= p -> n < p.
  intros n m p H1 H2; apply Zgt_lt; apply Zle_gt_trans with (m := m);
    [ assumption | apply Zlt_gt; assumption ].
Qed.

Lemma Zle_lt_trans : forall n m p:Z, n <= m -> m < p -> n < p.
Proof.
  intros n m p H1 H2; apply Zgt_lt; apply Zgt_le_trans with (m := m);
    [ apply Zlt_gt; assumption | assumption ].
Qed.

(** Transitivity of large orders *)

Lemma Zle_trans : forall n m p:Z, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p H1 H2; apply Znot_gt_le.
  intro Hgt; apply Zle_not_gt with n m. assumption.
  exact (Zgt_le_trans n p m Hgt H2).
Qed.

Lemma Zge_trans : forall n m p:Z, n >= m -> m >= p -> n >= p.
Proof.
  intros n m p H1 H2.
  apply Zle_ge.
  apply Zle_trans with m; apply Zge_le; trivial.
Qed.

Hint Resolve Zle_trans: zarith.


(** * Compatibility of order and operations on Z *)

(** ** Successor *)

(** Compatibility of successor wrt to order *)

Lemma Zsucc_le_compat : forall n m:Z, m <= n -> Zsucc m <= Zsucc n.
Proof.
  unfold Zle, not in |- *; intros m n H1 H2; apply H1;
    rewrite <- (Zcompare_plus_compat n m 1); do 2 rewrite (Zplus_comm 1);
      exact H2.
Qed.

Lemma Zsucc_gt_compat : forall n m:Z, m > n -> Zsucc m > Zsucc n.
Proof.
  unfold Zgt in |- *; intros n m H; rewrite Zcompare_succ_compat;
    auto with arith.
Qed.

Lemma Zsucc_lt_compat : forall n m:Z, n < m -> Zsucc n < Zsucc m.
Proof.
  intros n m H; apply Zgt_lt; apply Zsucc_gt_compat; apply Zlt_gt; assumption.
Qed.

Hint Resolve Zsucc_le_compat: zarith.

(** Simplification of successor wrt to order *)

Lemma Zsucc_gt_reg : forall n m:Z, Zsucc m > Zsucc n -> m > n.
Proof.
  unfold Zsucc, Zgt in |- *; intros n p;
    do 2 rewrite (fun m:Z => Zplus_comm m 1);
      rewrite (Zcompare_plus_compat p n 1); trivial with arith.
Qed.

Lemma Zsucc_le_reg : forall n m:Z, Zsucc m <= Zsucc n -> m <= n.
Proof.
  unfold Zle, not in |- *; intros m n H1 H2; apply H1; unfold Zsucc in |- *;
    do 2 rewrite <- (Zplus_comm 1); rewrite (Zcompare_plus_compat n m 1);
      assumption.
Qed.

Lemma Zsucc_lt_reg : forall n m:Z, Zsucc n < Zsucc m -> n < m.
Proof.
  intros n m H; apply Zgt_lt; apply Zsucc_gt_reg; apply Zlt_gt; assumption.
Qed.

(** Special base instances of order *)

Lemma Zgt_succ : forall n:Z, Zsucc n > n.
Proof.
  exact Zcompare_succ_Gt.
Qed.

Lemma Znot_le_succ : forall n:Z, ~ Zsucc n <= n.
Proof.
  intros n; apply Zgt_not_le; apply Zgt_succ.
Qed.

Lemma Zlt_succ : forall n:Z, n < Zsucc n.
Proof.
  intro n; apply Zgt_lt; apply Zgt_succ.
Qed.

Lemma Zlt_pred : forall n:Z, Zpred n < n.
Proof.
  intros n; apply Zsucc_lt_reg; rewrite <- Zsucc_pred; apply Zlt_succ.
Qed.

(** Relating strict and large order using successor or predecessor *)

Lemma Zgt_le_succ : forall n m:Z, m > n -> Zsucc n <= m.
Proof.
  unfold Zgt, Zle in |- *; intros n p H; elim (Zcompare_Gt_not_Lt p n);
    intros H1 H2; unfold not in |- *; intros H3; unfold not in H1;
      apply H1;
	[ assumption
	  | elim (Zcompare_Gt_Lt_antisym (n + 1) p); intros H4 H5; apply H4; exact H3 ].
Qed.

Lemma Zle_gt_succ : forall n m:Z, n <= m -> Zsucc m > n.
Proof.
  intros n p H; apply Zgt_le_trans with p.
  apply Zgt_succ.
  assumption.
Qed.

Lemma Zle_lt_succ : forall n m:Z, n <= m -> n < Zsucc m.
Proof.
  intros n m H; apply Zgt_lt; apply Zle_gt_succ; assumption.
Qed.

Lemma Zlt_le_succ : forall n m:Z, n < m -> Zsucc n <= m.
Proof.
  intros n p H; apply Zgt_le_succ; apply Zlt_gt; assumption.
Qed.

Lemma Zgt_succ_le : forall n m:Z, Zsucc m > n -> n <= m.
Proof.
  intros n p H; apply Zsucc_le_reg; apply Zgt_le_succ; assumption.
Qed.

Lemma Zlt_succ_le : forall n m:Z, n < Zsucc m -> n <= m.
Proof.
  intros n m H; apply Zgt_succ_le; apply Zlt_gt; assumption.
Qed.

Lemma Zle_succ_gt : forall n m:Z, Zsucc n <= m -> m > n.
Proof.
  intros n m H; apply Zle_gt_trans with (m := Zsucc n);
    [ assumption | apply Zgt_succ ].
Qed.

Lemma Zlt_succ_r : forall n m, n < Zsucc m <-> n <= m.
Proof.
  split; [apply Zlt_succ_le | apply Zle_lt_succ].
Qed.

(** Weakening order *)

Lemma Zle_succ : forall n:Z, n <= Zsucc n.
Proof.
  intros n; apply Zgt_succ_le; apply Zgt_trans with (m := Zsucc n);
    apply Zgt_succ.
Qed.

Hint Resolve Zle_succ: zarith.

Lemma Zle_pred : forall n:Z, Zpred n <= n.
Proof.
  intros n; pattern n at 2 in |- *; rewrite Zsucc_pred; apply Zle_succ.
Qed.

Lemma Zlt_lt_succ : forall n m:Z, n < m -> n < Zsucc m.
  intros n m H; apply Zgt_lt; apply Zgt_trans with (m := m);
    [ apply Zgt_succ | apply Zlt_gt; assumption ].
Qed.

Lemma Zle_le_succ : forall n m:Z, n <= m -> n <= Zsucc m.
Proof.
  intros x y H.
  apply Zle_trans with y; trivial with zarith.
Qed.

Lemma Zle_succ_le : forall n m:Z, Zsucc n <= m -> n <= m.
Proof.
  intros n m H; apply Zle_trans with (m := Zsucc n);
    [ apply Zle_succ | assumption ].
Qed.

Hint Resolve Zle_le_succ: zarith.

(** Relating order wrt successor and order wrt predecessor *)

Lemma Zgt_succ_pred : forall n m:Z, m > Zsucc n -> Zpred m > n.
Proof.
  unfold Zgt, Zsucc, Zpred in |- *; intros n p H;
    rewrite <- (fun x y => Zcompare_plus_compat x y 1);
      rewrite (Zplus_comm p); rewrite Zplus_assoc;
	rewrite (fun x => Zplus_comm x n); simpl in |- *;
	  assumption.
Qed.

Lemma Zlt_succ_pred : forall n m:Z, Zsucc n < m -> n < Zpred m.
Proof.
  intros n p H; apply Zsucc_lt_reg; rewrite <- Zsucc_pred; assumption.
Qed.

(** Relating strict order and large order on positive *)

Lemma Zlt_0_le_0_pred : forall n:Z, 0 < n -> 0 <= Zpred n.
Proof.
  intros x H.
  rewrite (Zsucc_pred x) in H.
  apply Zgt_succ_le.
  apply Zlt_gt.
  assumption.
Qed.

Lemma Zgt_0_le_0_pred : forall n:Z, n > 0 -> 0 <= Zpred n.
Proof.
  intros; apply Zlt_0_le_0_pred; apply Zgt_lt. assumption.
Qed.


(** Special cases of ordered integers *)

Lemma Zlt_0_1 : 0 < 1.
Proof.
  change (0 < Zsucc 0) in |- *. apply Zlt_succ.
Qed.

Lemma Zle_0_1 : 0 <= 1.
Proof.
  change (0 <= Zsucc 0) in |- *. apply Zle_succ.
Qed.

Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
Proof.
  intros p; red in |- *; simpl in |- *; red in |- *; intros H; discriminate.
Qed.

Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
Proof.
  unfold Zgt in |- *; trivial.
Qed.

(* weaker but useful (in [Zpower] for instance) *)
Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
Proof.
  intro; unfold Zle in |- *; discriminate.
Qed.

Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.
Proof.
  unfold Zlt in |- *; trivial.
Qed.

Lemma Zle_0_nat : forall n:nat, 0 <= Z_of_nat n.
Proof.
  simple induction n; simpl in |- *; intros;
    [ apply Zle_refl | unfold Zle in |- *; simpl in |- *; discriminate ].
Qed.

Hint Immediate Zeq_le: zarith.

(** Transitivity using successor *)

Lemma Zgt_trans_succ : forall n m p:Z, Zsucc n > m -> m > p -> n > p.
Proof.
  intros n m p H1 H2; apply Zle_gt_trans with (m := m);
    [ apply Zgt_succ_le; assumption | assumption ].
Qed.

(** Derived lemma *)

Lemma Zgt_succ_gt_or_eq : forall n m:Z, Zsucc n > m -> n > m \/ m = n.
Proof.
  intros n m H.
  assert (Hle : m <= n).
  apply Zgt_succ_le; assumption.
  destruct (Zle_lt_or_eq _ _ Hle) as [Hlt| Heq].
  left; apply Zlt_gt; assumption.
  right; assumption.
Qed.

(** ** Addition *)
(** Compatibility of addition wrt to order *)

Lemma Zplus_gt_compat_l : forall n m p:Z, n > m -> p + n > p + m.
Proof.
  unfold Zgt in |- *; intros n m p H; rewrite (Zcompare_plus_compat n m p);
    assumption.
Qed.

Lemma Zplus_gt_compat_r : forall n m p:Z, n > m -> n + p > m + p.
Proof.
  intros n m p H; rewrite (Zplus_comm n p); rewrite (Zplus_comm m p);
    apply Zplus_gt_compat_l; trivial.
Qed.

Lemma Zplus_le_compat_l : forall n m p:Z, n <= m -> p + n <= p + m.
Proof.
  intros n m p; unfold Zle, not in |- *; intros H1 H2; apply H1;
    rewrite <- (Zcompare_plus_compat n m p); assumption.
Qed.

Lemma Zplus_le_compat_r : forall n m p:Z, n <= m -> n + p <= m + p.
Proof.
  intros a b c; do 2 rewrite (fun n:Z => Zplus_comm n c);
    exact (Zplus_le_compat_l a b c).
Qed.

Lemma Zplus_lt_compat_l : forall n m p:Z, n < m -> p + n < p + m.
Proof.
  unfold Zlt in |- *; intros n m p; rewrite Zcompare_plus_compat;
    trivial with arith.
Qed.

Lemma Zplus_lt_compat_r : forall n m p:Z, n < m -> n + p < m + p.
Proof.
  intros n m p H; rewrite (Zplus_comm n p); rewrite (Zplus_comm m p);
    apply Zplus_lt_compat_l; trivial.
Qed.

Lemma Zplus_lt_le_compat : forall n m p q:Z, n < m -> p <= q -> n + p < m + q.
Proof.
  intros a b c d H0 H1.
  apply Zlt_le_trans with (b + c).
  apply Zplus_lt_compat_r; trivial.
  apply Zplus_le_compat_l; trivial.
Qed.

Lemma Zplus_le_lt_compat : forall n m p q:Z, n <= m -> p < q -> n + p < m + q.
Proof.
  intros a b c d H0 H1.
  apply Zle_lt_trans with (b + c).
  apply Zplus_le_compat_r; trivial.
  apply Zplus_lt_compat_l; trivial.
Qed.

Lemma Zplus_le_compat : forall n m p q:Z, n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q; intros H1 H2; apply Zle_trans with (m := n + q);
    [ apply Zplus_le_compat_l; assumption
      | apply Zplus_le_compat_r; assumption ].
Qed.


Lemma Zplus_lt_compat : forall n m p q:Z, n < m -> p < q -> n + p < m + q.
  intros; apply Zplus_le_lt_compat. apply Zlt_le_weak; assumption. assumption.
Qed.


(** Compatibility of addition wrt to being positive *)

Lemma Zplus_le_0_compat : forall n m:Z, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
  intros x y H1 H2; rewrite <- (Zplus_0_l 0); apply Zplus_le_compat; assumption.
Qed.

(** Simplification of addition wrt to order *)

Lemma Zplus_gt_reg_l : forall n m p:Z, p + n > p + m -> n > m.
Proof.
  unfold Zgt in |- *; intros n m p H; rewrite <- (Zcompare_plus_compat n m p);
    assumption.
Qed.

Lemma Zplus_gt_reg_r : forall n m p:Z, n + p > m + p -> n > m.
Proof.
  intros n m p H; apply Zplus_gt_reg_l with p.
  rewrite (Zplus_comm p n); rewrite (Zplus_comm p m); trivial.
Qed.

Lemma Zplus_le_reg_l : forall n m p:Z, p + n <= p + m -> n <= m.
Proof.
  intros n m p; unfold Zle, not in |- *; intros H1 H2; apply H1;
    rewrite (Zcompare_plus_compat n m p); assumption.
Qed.

Lemma Zplus_le_reg_r : forall n m p:Z, n + p <= m + p -> n <= m.
Proof.
  intros n m p H; apply Zplus_le_reg_l with p.
  rewrite (Zplus_comm p n); rewrite (Zplus_comm p m); trivial.
Qed.

Lemma Zplus_lt_reg_l : forall n m p:Z, p + n < p + m -> n < m.
Proof.
  unfold Zlt in |- *; intros n m p; rewrite Zcompare_plus_compat;
    trivial with arith.
Qed.

Lemma Zplus_lt_reg_r : forall n m p:Z, n + p < m + p -> n < m.
Proof.
  intros n m p H; apply Zplus_lt_reg_l with p.
  rewrite (Zplus_comm p n); rewrite (Zplus_comm p m); trivial.
Qed.

(** ** Multiplication *)
(** Compatibility of multiplication by a positive wrt to order *)

Lemma Zmult_le_compat_r : forall n m p:Z, n <= m -> 0 <= p -> n * p <= m * p.
Proof.
  intros a b c H H0; destruct c.
  do 2 rewrite Zmult_0_r; assumption.
  rewrite (Zmult_comm a); rewrite (Zmult_comm b).
  unfold Zle in |- *; rewrite Zcompare_mult_compat; assumption.
  unfold Zle in H0; contradiction H0; reflexivity.
Qed.

Lemma Zmult_le_compat_l : forall n m p:Z, n <= m -> 0 <= p -> p * n <= p * m.
Proof.
  intros a b c H1 H2; rewrite (Zmult_comm c a); rewrite (Zmult_comm c b).
  apply Zmult_le_compat_r; trivial.
Qed.

Lemma Zmult_lt_compat_r : forall n m p:Z, 0 < p -> n < m -> n * p < m * p.
Proof.
  intros x y z H H0; destruct z.
  contradiction (Zlt_irrefl 0).
  rewrite (Zmult_comm x); rewrite (Zmult_comm y).
  unfold Zlt in |- *; rewrite Zcompare_mult_compat; assumption.
  discriminate H.
Qed.

Lemma Zmult_gt_compat_r : forall n m p:Z, p > 0 -> n > m -> n * p > m * p.
Proof.
  intros x y z; intros; apply Zlt_gt; apply Zmult_lt_compat_r; apply Zgt_lt;
    assumption.
Qed.

Lemma Zmult_gt_0_lt_compat_r :
  forall n m p:Z, p > 0 -> n < m -> n * p < m * p.
Proof.
  intros x y z; intros; apply Zmult_lt_compat_r;
    [ apply Zgt_lt; assumption | assumption ].
Qed.

Lemma Zmult_gt_0_le_compat_r :
  forall n m p:Z, p > 0 -> n <= m -> n * p <= m * p.
Proof.
  intros x y z Hz Hxy.
  elim (Zle_lt_or_eq x y Hxy).
  intros; apply Zlt_le_weak.
  apply Zmult_gt_0_lt_compat_r; trivial.
  intros; apply Zeq_le.
  rewrite H; trivial.
Qed.

Lemma Zmult_lt_0_le_compat_r :
  forall n m p:Z, 0 < p -> n <= m -> n * p <= m * p.
Proof.
  intros x y z; intros; apply Zmult_gt_0_le_compat_r; try apply Zlt_gt;
    assumption.
Qed.

Lemma Zmult_gt_0_lt_compat_l :
  forall n m p:Z, p > 0 -> n < m -> p * n < p * m.
Proof.
  intros x y z; intros.
  rewrite (Zmult_comm z x); rewrite (Zmult_comm z y);
    apply Zmult_gt_0_lt_compat_r; assumption.
Qed.

Lemma Zmult_lt_compat_l : forall n m p:Z, 0 < p -> n < m -> p * n < p * m.
Proof.
  intros x y z; intros.
  rewrite (Zmult_comm z x); rewrite (Zmult_comm z y);
    apply Zmult_gt_0_lt_compat_r; try apply Zlt_gt; assumption.
Qed.

Lemma Zmult_gt_compat_l : forall n m p:Z, p > 0 -> n > m -> p * n > p * m.
Proof.
  intros x y z; intros; rewrite (Zmult_comm z x); rewrite (Zmult_comm z y);
    apply Zmult_gt_compat_r; assumption.
Qed.

Lemma Zmult_ge_compat_r : forall n m p:Z, n >= m -> p >= 0 -> n * p >= m * p.
Proof.
  intros a b c H1 H2; apply Zle_ge.
  apply Zmult_le_compat_r; apply Zge_le; trivial.
Qed.

Lemma Zmult_ge_compat_l : forall n m p:Z, n >= m -> p >= 0 -> p * n >= p * m.
Proof.
  intros a b c H1 H2; apply Zle_ge.
  apply Zmult_le_compat_l; apply Zge_le; trivial.
Qed.

Lemma Zmult_ge_compat :
  forall n m p q:Z, n >= p -> m >= q -> p >= 0 -> q >= 0 -> n * m >= p * q.
Proof.
  intros a b c d H0 H1 H2 H3.
  apply Zge_trans with (a * d).
  apply Zmult_ge_compat_l; trivial.
  apply Zge_trans with c; trivial.
  apply Zmult_ge_compat_r; trivial.
Qed.

Lemma Zmult_le_compat :
  forall n m p q:Z, n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q.
Proof.
  intros a b c d H0 H1 H2 H3.
  apply Zle_trans with (c * b).
  apply Zmult_le_compat_r; assumption.
  apply Zmult_le_compat_l.
  assumption.
  apply Zle_trans with a; assumption.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_gt_0_lt_reg_r : forall n m p:Z, p > 0 -> n * p < m * p -> n < m.
Proof.
  intros x y z; intros; destruct z.
  contradiction (Zgt_irrefl 0).
  rewrite (Zmult_comm x) in H0; rewrite (Zmult_comm y) in H0.
  unfold Zlt in H0; rewrite Zcompare_mult_compat in H0; assumption.
  discriminate H.
Qed.

Lemma Zmult_lt_reg_r : forall n m p:Z, 0 < p -> n * p < m * p -> n < m.
Proof.
  intros a b c H0 H1.
  apply Zmult_gt_0_lt_reg_r with c; try apply Zlt_gt; assumption.
Qed.

Lemma Zmult_le_reg_r : forall n m p:Z, p > 0 -> n * p <= m * p -> n <= m.
Proof.
  intros x y z Hz Hxy.
  elim (Zle_lt_or_eq (x * z) (y * z) Hxy).
  intros; apply Zlt_le_weak.
  apply Zmult_gt_0_lt_reg_r with z; trivial.
  intros; apply Zeq_le.
  apply Zmult_reg_r with z.
  intro. rewrite H0 in Hz. contradiction (Zgt_irrefl 0).
  assumption.
Qed.

Lemma Zmult_lt_0_le_reg_r : forall n m p:Z, 0 < p -> n * p <= m * p -> n <= m.
Proof.
  intros x y z; intros; apply Zmult_le_reg_r with z.
  try apply Zlt_gt; assumption.
  assumption.
Qed.


Lemma Zmult_ge_reg_r : forall n m p:Z, p > 0 -> n * p >= m * p -> n >= m.
Proof.
  intros a b c H1 H2; apply Zle_ge; apply Zmult_le_reg_r with c; trivial.
  apply Zge_le; trivial.
Qed.

Lemma Zmult_gt_reg_r : forall n m p:Z, p > 0 -> n * p > m * p -> n > m.
Proof.
  intros a b c H1 H2; apply Zlt_gt; apply Zmult_gt_0_lt_reg_r with c; trivial.
  apply Zgt_lt; trivial.
Qed.


(** Compatibility of multiplication by a positive wrt to being positive *)

Lemma Zmult_le_0_compat : forall n m:Z, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
  intros x y; case x.
  intros; rewrite Zmult_0_l; trivial.
  intros p H1; unfold Zle in |- *.
  pattern 0 at 2 in |- *; rewrite <- (Zmult_0_r (Zpos p)).
  rewrite Zcompare_mult_compat; trivial.
  intros p H1 H2; absurd (0 > Zneg p); trivial.
  unfold Zgt in |- *; simpl in |- *; auto with zarith.
Qed.

Lemma Zmult_gt_0_compat : forall n m:Z, n > 0 -> m > 0 -> n * m > 0.
Proof.
  intros x y; case x.
  intros H; discriminate H.
  intros p H1; unfold Zgt in |- *; pattern 0 at 2 in |- *;
    rewrite <- (Zmult_0_r (Zpos p)).
  rewrite Zcompare_mult_compat; trivial.
  intros p H; discriminate H.
Qed.

Lemma Zmult_lt_0_compat : forall n m:Z, 0 < n -> 0 < m -> 0 < n * m.
Proof.
  intros a b apos bpos.
  apply Zgt_lt.
  apply Zmult_gt_0_compat; try apply Zlt_gt; assumption.
Qed.

(** For compatibility *)
Notation Zmult_lt_O_compat := Zmult_lt_0_compat (only parsing).

Lemma Zmult_gt_0_le_0_compat : forall n m:Z, n > 0 -> 0 <= m -> 0 <= m * n.
Proof.
  intros x y H1 H2; apply Zmult_le_0_compat; trivial.
  apply Zlt_le_weak; apply Zgt_lt; trivial.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_le_0_reg_r : forall n m:Z, n > 0 -> 0 <= m * n -> 0 <= m.
Proof.
  intros x y; case x;
    [ simpl in |- *; unfold Zgt in |- *; simpl in |- *; intros H; discriminate H
      | intros p H1; unfold Zle in |- *; rewrite Zmult_comm;
	pattern 0 at 1 in |- *; rewrite <- (Zmult_0_r (Zpos p));
	  rewrite Zcompare_mult_compat; auto with arith
      | intros p; unfold Zgt in |- *; simpl in |- *; intros H; discriminate H ].
Qed.

Lemma Zmult_gt_0_lt_0_reg_r : forall n m:Z, n > 0 -> 0 < m * n -> 0 < m.
Proof.
  intros x y; case x;
    [ simpl in |- *; unfold Zgt in |- *; simpl in |- *; intros H; discriminate H
      | intros p H1; unfold Zlt in |- *; rewrite Zmult_comm;
	pattern 0 at 1 in |- *; rewrite <- (Zmult_0_r (Zpos p));
	  rewrite Zcompare_mult_compat; auto with arith
      | intros p; unfold Zgt in |- *; simpl in |- *; intros H; discriminate H ].
Qed.

Lemma Zmult_lt_0_reg_r : forall n m:Z, 0 < n -> 0 < m * n -> 0 < m.
Proof.
  intros x y; intros; eapply Zmult_gt_0_lt_0_reg_r with x; try apply Zlt_gt;
    assumption.
Qed.

Lemma Zmult_gt_0_reg_l : forall n m:Z, n > 0 -> n * m > 0 -> m > 0.
Proof.
  intros x y; case x.
  intros H; discriminate H.
  intros p H1; unfold Zgt in |- *.
  pattern 0 at 1 in |- *; rewrite <- (Zmult_0_r (Zpos p)).
  rewrite Zcompare_mult_compat; trivial.
  intros p H; discriminate H.
Qed.

(** ** Square *)
(** Simplification of square wrt order *)

Lemma Zgt_square_simpl :
  forall n m:Z, n >= 0 -> n * n > m * m -> n > m.
Proof.
  intros n m H0 H1.
  case (dec_Zlt m n).
  intro; apply Zlt_gt; trivial.
  intros H2; cut (m >= n).
  intros H.
  elim Zgt_not_le with (1 := H1).
  apply Zge_le.
  apply Zmult_ge_compat; auto.
  apply Znot_lt_ge; trivial.
Qed.

Lemma Zlt_square_simpl :
  forall n m:Z, 0 <= n -> m * m < n * n -> m < n.
Proof.
  intros x y H0 H1.
  apply Zgt_lt.
  apply Zgt_square_simpl; try apply Zle_ge; try apply Zlt_gt; assumption.
Qed.

(** * Equivalence between inequalities *)

Lemma Zle_plus_swap : forall n m p:Z, n + p <= m <-> n <= m - p.
Proof.
  intros x y z; intros. split. intro. rewrite <- (Zplus_0_r x). rewrite <- (Zplus_opp_r z).
  rewrite Zplus_assoc. exact (Zplus_le_compat_r _ _ _ H).
  intro. rewrite <- (Zplus_0_r y). rewrite <- (Zplus_opp_l z). rewrite Zplus_assoc.
  apply Zplus_le_compat_r. assumption.
Qed.

Lemma Zlt_plus_swap : forall n m p:Z, n + p < m <-> n < m - p.
Proof.
  intros x y z; intros. split. intro. unfold Zminus in |- *. rewrite Zplus_comm. rewrite <- (Zplus_0_l x).
  rewrite <- (Zplus_opp_l z). rewrite Zplus_assoc_reverse. apply Zplus_lt_compat_l. rewrite Zplus_comm.
  assumption.
  intro. rewrite Zplus_comm. rewrite <- (Zplus_0_l y). rewrite <- (Zplus_opp_r z).
  rewrite Zplus_assoc_reverse. apply Zplus_lt_compat_l. rewrite Zplus_comm. assumption.
Qed.

Lemma Zeq_plus_swap : forall n m p:Z, n + p = m <-> n = m - p.
Proof.
  intros x y z; intros. split. intro. apply Zplus_minus_eq. symmetry  in |- *. rewrite Zplus_comm.
  assumption.
  intro. rewrite H. unfold Zminus in |- *. rewrite Zplus_assoc_reverse.
  rewrite Zplus_opp_l. apply Zplus_0_r.
Qed.

Lemma Zlt_minus_simpl_swap : forall n m:Z, 0 < m -> n - m < n.
Proof.
  intros n m H; apply Zplus_lt_reg_l with (p := m); rewrite Zplus_minus;
    pattern n at 1 in |- *; rewrite <- (Zplus_0_r n);
      rewrite (Zplus_comm m n); apply Zplus_lt_compat_l;
	assumption.
Qed.

Lemma Zlt_0_minus_lt : forall n m:Z, 0 < n - m -> m < n.
Proof.
  intros n m H; apply Zplus_lt_reg_l with (p := - m); rewrite Zplus_opp_l;
    rewrite Zplus_comm; exact H.
Qed.

Lemma Zle_0_minus_le : forall n m:Z, 0 <= n - m -> m <= n.
Proof.
  intros n m H; apply Zplus_le_reg_l with (p := - m); rewrite Zplus_opp_l;
    rewrite Zplus_comm; exact H.
Qed.

Lemma Zle_minus_le_0 : forall n m:Z, m <= n -> 0 <= n - m.
Proof.
  intros n m H; unfold Zminus; apply Zplus_le_reg_r with (p := m);
    rewrite <- Zplus_assoc; rewrite Zplus_opp_l; rewrite Zplus_0_r; exact H.
Qed.

Lemma Zmult_lt_compat:
  forall n m p q : Z, 0 <= n < p -> 0 <= m < q -> n * m < p * q.
Proof.
  intros n m p q (H1, H2) (H3,H4).
  assert (0<p) by (apply Zle_lt_trans with n; auto).
  assert (0<q) by (apply Zle_lt_trans with m; auto).
  case Zle_lt_or_eq with (1 := H1); intros H5; auto with zarith.
  case Zle_lt_or_eq with (1 := H3); intros H6; auto with zarith.
  apply Zlt_trans with (n * q).
  apply Zmult_lt_compat_l; auto.
  apply Zmult_lt_compat_r; auto with zarith.
  rewrite <- H6; rewrite Zmult_0_r; apply Zmult_lt_0_compat; auto with zarith.
  rewrite <- H5; simpl; apply Zmult_lt_0_compat; auto with zarith.
Qed.

Lemma Zmult_lt_compat2:
  forall n m p q : Z, 0 < n <= p -> 0 < m < q -> n * m < p * q.
Proof.
  intros n m p q (H1, H2) (H3, H4).
  apply Zle_lt_trans with (p * m).
  apply Zmult_le_compat_r; auto.
  apply Zlt_le_weak; auto.
  apply Zmult_lt_compat_l; auto.
  apply Zlt_le_trans with n; auto.
Qed.

(** For compatibility *)
Notation Zlt_O_minus_lt := Zlt_0_minus_lt (only parsing).
