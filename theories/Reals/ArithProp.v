(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

  (*i $Id$ i*)

Require Import Rbase.
Require Import Rbasic_fun.
Require Import Even.
Require Import Div2.
Require Import ArithRing.

Open Local Scope Z_scope.
Open Local Scope R_scope.

Lemma minus_neq_O : forall n i:nat, (i < n)%nat -> (n - i)%nat <> 0%nat.
Proof.
  intros; red in |- *; intro.
  cut (forall n m:nat, (m <= n)%nat -> (n - m)%nat = 0%nat -> n = m).
  intro; assert (H2 := H1 _ _ (lt_le_weak _ _ H) H0); rewrite H2 in H;
    elim (lt_irrefl _ H).
  set (R := fun n m:nat => (m <= n)%nat -> (n - m)%nat = 0%nat -> n = m).
  cut
    ((forall n m:nat, R n m) ->
      forall n0 m:nat, (m <= n0)%nat -> (n0 - m)%nat = 0%nat -> n0 = m).
  intro; apply H1.
  apply nat_double_ind.
  unfold R in |- *; intros; inversion H2; reflexivity.
  unfold R in |- *; intros; simpl in H3; assumption.
  unfold R in |- *; intros; simpl in H4; assert (H5 := le_S_n _ _ H3);
    assert (H6 := H2 H5 H4); rewrite H6; reflexivity.
  unfold R in |- *; intros; apply H1; assumption.
Qed.

Lemma le_minusni_n : forall n i:nat, (i <= n)%nat -> (n - i <= n)%nat.
Proof.
  set (R := fun m n:nat => (n <= m)%nat -> (m - n <= m)%nat).
  cut
    ((forall m n:nat, R m n) -> forall n i:nat, (i <= n)%nat -> (n - i <= n)%nat).
  intro; apply H.
  apply nat_double_ind.
  unfold R in |- *; intros; simpl in |- *; apply le_n.
  unfold R in |- *; intros; simpl in |- *; apply le_n.
  unfold R in |- *; intros; simpl in |- *; apply le_trans with n.
  apply H0; apply le_S_n; assumption.
  apply le_n_Sn.
  unfold R in |- *; intros; apply H; assumption.
Qed.

Lemma lt_minus_O_lt : forall m n:nat, (m < n)%nat -> (0 < n - m)%nat.
Proof.
  intros n m; pattern n, m in |- *; apply nat_double_ind;
    [ intros; rewrite <- minus_n_O; assumption
      | intros; elim (lt_n_O _ H)
      | intros; simpl in |- *; apply H; apply lt_S_n; assumption ].
Qed.

Lemma even_odd_cor :
  forall n:nat,  exists p : nat, n = (2 * p)%nat \/ n = S (2 * p).
Proof.
  intro.
  assert (H := even_or_odd n).
  exists (div2 n).
  assert (H0 := even_odd_double n).
  elim H0; intros.
  elim H1; intros H3 _.
  elim H2; intros H4 _.
  replace (2 * div2 n)%nat with (double (div2 n)).
  elim H; intro.
  left.
  apply H3; assumption.
  right.
  apply H4; assumption.
  unfold double in |- *;ring.
Qed.

  (* 2m <= 2n => m<=n *)
Lemma le_double : forall m n:nat, (2 * m <= 2 * n)%nat -> (m <= n)%nat.
Proof.
  intros; apply INR_le.
  assert (H1 := le_INR _ _ H).
  do 2 rewrite mult_INR in H1.
  apply Rmult_le_reg_l with (INR 2).
  replace (INR 2) with 2; [ prove_sup0 | reflexivity ].
  assumption.
Qed.

(** Here, we have the euclidian division *)
(** This lemma is used in the proof of sin_eq_0 : (sin x)=0<->x=kPI *)
Lemma euclidian_division :
  forall x y:R,
    y <> 0 ->
    exists k : Z, (exists r : R, x = IZR k * y + r /\ 0 <= r < Rabs y).
Proof.
  intros.
  set
    (k0 :=
      match Rcase_abs y with
	| left _ => (1 - up (x / - y))%Z
	| right _ => (up (x / y) - 1)%Z
      end).
  exists k0.
  exists (x - IZR k0 * y).
  split.
  ring.
  unfold k0 in |- *; case (Rcase_abs y); intro.
  assert (H0 := archimed (x / - y)); rewrite <- Z_R_minus; simpl in |- *;
    unfold Rminus in |- *.
  replace (- ((1 + - IZR (up (x / - y))) * y)) with
    ((IZR (up (x / - y)) - 1) * y); [ idtac | ring ].
  split.
  apply Rmult_le_reg_l with (/ - y).
  apply Rinv_0_lt_compat; apply Ropp_0_gt_lt_contravar; exact r.
  rewrite Rmult_0_r; rewrite (Rmult_comm (/ - y)); rewrite Rmult_plus_distr_r;
    rewrite <- Ropp_inv_permute; [ idtac | assumption ].
  rewrite Rmult_assoc; repeat rewrite Ropp_mult_distr_r_reverse;
    rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r | assumption ].
  apply Rplus_le_reg_l with (IZR (up (x / - y)) - x / - y).
  rewrite Rplus_0_r; unfold Rdiv in |- *; pattern (/ - y) at 4 in |- *;
    rewrite <- Ropp_inv_permute; [ idtac | assumption ].
  replace
    (IZR (up (x * / - y)) - x * - / y +
      (- (x * / y) + - (IZR (up (x * / - y)) - 1))) with 1;
    [ idtac | ring ].
  elim H0; intros _ H1; unfold Rdiv in H1; exact H1.
  rewrite (Rabs_left _ r); apply Rmult_lt_reg_l with (/ - y).
  apply Rinv_0_lt_compat; apply Ropp_0_gt_lt_contravar; exact r.
  rewrite <- Rinv_l_sym.
  rewrite (Rmult_comm (/ - y)); rewrite Rmult_plus_distr_r;
    rewrite <- Ropp_inv_permute; [ idtac | assumption ].
  rewrite Rmult_assoc; repeat rewrite Ropp_mult_distr_r_reverse;
    rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r | assumption ];
      apply Rplus_lt_reg_r with (IZR (up (x / - y)) - 1).
  replace (IZR (up (x / - y)) - 1 + 1) with (IZR (up (x / - y)));
    [ idtac | ring ].
  replace (IZR (up (x / - y)) - 1 + (- (x * / y) + - (IZR (up (x / - y)) - 1)))
    with (- (x * / y)); [ idtac | ring ].
  rewrite <- Ropp_mult_distr_r_reverse; rewrite (Ropp_inv_permute _ H); elim H0;
    unfold Rdiv in |- *; intros H1 _; exact H1.
  apply Ropp_neq_0_compat; assumption.
  assert (H0 := archimed (x / y)); rewrite <- Z_R_minus; simpl in |- *;
    cut (0 < y).
  intro; unfold Rminus in |- *;
    replace (- ((IZR (up (x / y)) + -1) * y)) with ((1 - IZR (up (x / y))) * y);
      [ idtac | ring ].
  split.
  apply Rmult_le_reg_l with (/ y).
  apply Rinv_0_lt_compat; assumption.
  rewrite Rmult_0_r; rewrite (Rmult_comm (/ y)); rewrite Rmult_plus_distr_r;
    rewrite Rmult_assoc; rewrite <- Rinv_r_sym;
      [ rewrite Rmult_1_r | assumption ];
      apply Rplus_le_reg_l with (IZR (up (x / y)) - x / y);
	rewrite Rplus_0_r; unfold Rdiv in |- *;
	  replace
	    (IZR (up (x * / y)) - x * / y + (x * / y + (1 - IZR (up (x * / y))))) with
	    1; [ idtac | ring ]; elim H0; intros _ H2; unfold Rdiv in H2;
	      exact H2.
  rewrite (Rabs_right _ r); apply Rmult_lt_reg_l with (/ y).
  apply Rinv_0_lt_compat; assumption.
  rewrite <- (Rinv_l_sym _ H); rewrite (Rmult_comm (/ y));
    rewrite Rmult_plus_distr_r; rewrite Rmult_assoc; rewrite <- Rinv_r_sym;
      [ rewrite Rmult_1_r | assumption ];
      apply Rplus_lt_reg_r with (IZR (up (x / y)) - 1);
	replace (IZR (up (x / y)) - 1 + 1) with (IZR (up (x / y)));
	  [ idtac | ring ];
	  replace (IZR (up (x / y)) - 1 + (x * / y + (1 - IZR (up (x / y))))) with
	    (x * / y); [ idtac | ring ]; elim H0; unfold Rdiv in |- *;
	      intros H2 _; exact H2.
  case (total_order_T 0 y); intro.
  elim s; intro.
  assumption.
  elim H; symmetry  in |- *; exact b.
  assert (H1 := Rge_le _ _ r); elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 r0)).
Qed.

Lemma tech8 : forall n i:nat, (n <= S n + i)%nat.
Proof.
  intros; induction  i as [| i Hreci].
  replace (S n + 0)%nat with (S n); [ apply le_n_Sn | ring ].
  replace (S n + S i)%nat with (S (S n + i)).
  apply le_S; assumption.
  apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR; do 2 rewrite S_INR; ring.
Qed.
