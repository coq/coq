(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rdefinitions Raxioms RIneq.
Require Import Rbasic_fun.
Require Import ArithRing.
Require Import PeanoNat.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Lemma minus_neq_O : forall n i:nat, (i < n)%nat -> (n - i)%nat <> 0%nat.
Proof.
  intros n i Hlt.
  apply Nat.neq_0_lt_0, Nat.lt_add_lt_sub_r; assumption.
Qed.

Lemma le_minusni_n : forall n i:nat, (i <= n)%nat -> (n - i <= n)%nat.
Proof.
  intros n i _.
  induction i as [ | i IHi ].
  - rewrite Nat.sub_0_r; reflexivity.
  - etransitivity; [ | apply IHi ].
    rewrite Nat.sub_succ_r.
    apply Nat.le_pred_l.
Qed.

Lemma lt_minus_O_lt : forall m n:nat, (m < n)%nat -> (0 < n - m)%nat.
Proof.
  intros n i Hlt.
  apply Nat.lt_add_lt_sub_r; assumption.
Qed.

Lemma even_odd_cor :
  forall n:nat, exists p : nat, n = (2 * p)%nat \/ n = S (2 * p).
Proof.
  intros n; exists (Nat.div2 n).
  case_eq (Nat.odd n); intros H; [right|left].
  - assert (Nat.b2n (Nat.odd n) = 1%nat) as Hb by now rewrite H.
    rewrite Nat.div2_odd at 1; rewrite Hb, Nat.add_1_r; reflexivity.
  - assert (Nat.b2n (Nat.odd n) = 0%nat) as Hb by now rewrite H.
    rewrite Nat.div2_odd at 1; rewrite Hb, Nat.add_0_r; reflexivity.
Qed.

  (* 2m <= 2n => m<=n *)
Lemma le_double : forall m n:nat, (2 * m <= 2 * n)%nat -> (m <= n)%nat.
Proof.
  intros; apply INR_le.
  assert (H1 := le_INR _ _ H).
  do 2 rewrite mult_INR in H1.
  apply Rmult_le_reg_l with (INR 2).
  - apply lt_0_INR. apply Nat.lt_0_2.
  - assumption.
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
  - ring.
  - unfold k0; case (Rcase_abs y) as [Hlt|Hge].
    + assert (H0 := archimed (x / - y)); rewrite <- Z_R_minus; simpl;
        unfold Rminus.
      replace (- ((1 + - IZR (up (x / - y))) * y)) with
        ((IZR (up (x / - y)) - 1) * y); [ idtac | ring ].
      split.
      * apply Rmult_le_reg_l with (/ - y).
        -- apply Rinv_0_lt_compat; apply Ropp_0_gt_lt_contravar; exact Hlt.
        -- rewrite Rmult_0_r; rewrite (Rmult_comm (/ - y)); rewrite Rmult_plus_distr_r;
             rewrite Rinv_opp.
           rewrite Rmult_assoc; repeat rewrite Ropp_mult_distr_r_reverse;
             rewrite Rinv_r; [ rewrite Rmult_1_r | assumption ].
           apply Rplus_le_reg_l with (IZR (up (x / - y)) - x / - y).
           rewrite Rplus_0_r; unfold Rdiv; pattern (/ - y) at 4;
             rewrite Rinv_opp.
           replace
             (IZR (up (x * / - y)) - x * - / y +
                (- (x * / y) + - (IZR (up (x * / - y)) - 1))) with 1;
             [ idtac | ring ].
           elim H0; intros _ H1; unfold Rdiv in H1; exact H1.
      * rewrite (Rabs_left _ Hlt); apply Rmult_lt_reg_l with (/ - y).
        -- apply Rinv_0_lt_compat; apply Ropp_0_gt_lt_contravar; exact Hlt.
        -- rewrite Rinv_l.
           ++ rewrite (Rmult_comm (/ - y)); rewrite Rmult_plus_distr_r;
                rewrite Rinv_opp.
              rewrite Rmult_assoc; repeat rewrite Ropp_mult_distr_r_reverse;
                rewrite Rinv_r; [ rewrite Rmult_1_r | assumption ];
                apply Rplus_lt_reg_l with (IZR (up (x / - y)) - 1).
              replace (IZR (up (x / - y)) - 1 + 1) with (IZR (up (x / - y)));
                [ idtac | ring ].
              replace (IZR (up (x / - y)) - 1 + (- (x * / y) + - (IZR (up (x / - y)) - 1)))
                with (- (x * / y)); [ idtac | ring ].
              rewrite <- Ropp_mult_distr_r_reverse; rewrite <- Rinv_opp; elim H0;
                unfold Rdiv; intros H1 _; exact H1.
           ++ apply Ropp_neq_0_compat; assumption.
    + assert (H0 := archimed (x / y)); rewrite <- Z_R_minus; simpl;
        cut (0 < y).
      * intro; unfold Rminus;
          replace (- ((IZR (up (x / y)) + -(1)) * y)) with ((1 - IZR (up (x / y))) * y);
          [ idtac | ring ].
        split.
        -- apply Rmult_le_reg_l with (/ y).
           ++ apply Rinv_0_lt_compat; assumption.
           ++ rewrite Rmult_0_r; rewrite (Rmult_comm (/ y)); rewrite Rmult_plus_distr_r;
                rewrite Rmult_assoc; rewrite Rinv_r;
                [ rewrite Rmult_1_r | assumption ];
                apply Rplus_le_reg_l with (IZR (up (x / y)) - x / y);
                rewrite Rplus_0_r; unfold Rdiv;
                replace
                  (IZR (up (x * / y)) - x * / y + (x * / y + (1 - IZR (up (x * / y))))) with
                1; [ idtac | ring ]; elim H0; intros _ H2; unfold Rdiv in H2;
                exact H2.
        -- rewrite (Rabs_right _ Hge); apply Rmult_lt_reg_l with (/ y).
           ++ apply Rinv_0_lt_compat; assumption.
           ++ rewrite (Rinv_l _ H); rewrite (Rmult_comm (/ y));
                rewrite Rmult_plus_distr_r; rewrite Rmult_assoc; rewrite Rinv_r;
                [ rewrite Rmult_1_r | assumption ];
                apply Rplus_lt_reg_l with (IZR (up (x / y)) - 1);
                replace (IZR (up (x / y)) - 1 + 1) with (IZR (up (x / y)));
                [ idtac | ring ];
                replace (IZR (up (x / y)) - 1 + (x * / y + (1 - IZR (up (x / y))))) with
                (x * / y); [ idtac | ring ]; elim H0; unfold Rdiv;
                intros H2 _; exact H2.
      * destruct (total_order_T 0 y) as [[Hlt|Heq]|Hgt].
        -- assumption.
        -- elim H; symmetry ; exact Heq.
        -- apply Rge_le in Hge; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hge Hgt)).
Qed.

Lemma tech8 : forall n i:nat, (n <= S n + i)%nat.
Proof.
  intros; induction  i as [| i Hreci].
  - replace (S n + 0)%nat with (S n); [ apply Nat.le_succ_diag_r | ring ].
  - replace (S n + S i)%nat with (S (S n + i)).
    + apply le_S; assumption.
    + apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR; do 2 rewrite S_INR; ring.
Qed.
