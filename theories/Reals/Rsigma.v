(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import PartSum.
Require Import Lia.
Local Open Scope R_scope.

Set Implicit Arguments.

Section Sigma.

  Variable f : nat -> R.

  Definition sigma (low high:nat) : R :=
    sum_f_R0 (fun k:nat => f (low + k)) (high - low).

  Theorem sigma_split :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high = sigma low k + sigma (S k) high.
  Proof.
    intros; induction  k as [| k Hreck].
    - cut (low = 0%nat).
      + intro; rewrite H1; unfold sigma; rewrite Nat.sub_diag, Nat.sub_0_r;
          simpl; replace (high - 1)%nat with (pred high).
        * apply (decomp_sum (fun k:nat => f k)).
          assumption.
        * symmetry; apply Nat.sub_1_r.
      + inversion H; reflexivity.
    - cut ((low <= k)%nat \/ low = S k).
      + intro; elim H1; intro.
        * replace (sigma low (S k)) with (sigma low k + f (S k)).
          -- rewrite Rplus_assoc;
               replace (f (S k) + sigma (S (S k)) high) with (sigma (S k) high).
             ++ apply Hreck.
                ** assumption.
                ** apply Nat.lt_trans with (S k); [ apply Nat.lt_succ_diag_r | assumption ].
             ++ unfold sigma; replace (high - S (S k))%nat with (pred (high - S k)).
                ** pattern (S k) at 3; replace (S k) with (S k + 0)%nat;
                     [ idtac | ring ].
                   replace (sum_f_R0 (fun k0:nat => f (S (S k) + k0)) (pred (high - S k))) with
                     (sum_f_R0 (fun k0:nat => f (S k + S k0)) (pred (high - S k))).
                   { apply (decomp_sum (fun i:nat => f (S k + i))).
                     apply lt_minus_O_lt; assumption. }
                   apply sum_eq; intros. replace (S k + S i)%nat with (S (S k) + i)%nat by ring.
                   reflexivity.
                ** replace (high - S (S k))%nat with (high - S k - 1)%nat by lia.
                   symmetry; apply Nat.sub_1_r.
          -- unfold sigma; replace (S k - low)%nat with (S (k - low)) by lia.
             pattern (S k) at 1; replace (S k) with (low + S (k - low))%nat by lia.
             symmetry ; apply (tech5 (fun i:nat => f (low + i))).
        * rewrite <- H2; unfold sigma; rewrite Nat.sub_diag; simpl;
            replace (high - S low)%nat with (pred (high - low)) by lia.
          replace (sum_f_R0 (fun k0:nat => f (S (low + k0))) (pred (high - low))) with
            (sum_f_R0 (fun k0:nat => f (low + S k0)) (pred (high - low))).
          -- apply (decomp_sum (fun k0:nat => f (low + k0))).
             apply lt_minus_O_lt.
             apply Nat.le_lt_trans with (S k); [ rewrite H2; apply Nat.le_refl | assumption ].
          -- apply sum_eq; intros; replace (S (low + i)) with (low + S i)%nat by ring.
             reflexivity.
      + inversion H; [ right; reflexivity | left; assumption ].
  Qed.

  Theorem sigma_diff :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high - sigma low k = sigma (S k) high.
  Proof.
    intros low high k H1 H2; symmetry ; rewrite (sigma_split H1 H2); ring.
  Qed.

  Theorem sigma_diff_neg :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low k - sigma low high = - sigma (S k) high.
  Proof.
    intros low high k H1 H2; rewrite (sigma_split H1 H2); ring.
  Qed.

  Theorem sigma_first :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f low + sigma (S low) high.
  Proof.
    intros low high H1; generalize (proj2 (Nat.le_succ_l low high) H1); intro H2;
      generalize (Nat.lt_le_incl low high H1); intro H3;
        replace (f low) with (sigma low low).
    - apply sigma_split.
      + apply le_n.
      + assumption.
    - unfold sigma; rewrite Nat.sub_diag.
      simpl.
      replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

  Theorem sigma_last :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f high + sigma low (pred high).
  Proof.
    intros low high H1; generalize (proj2 (Nat.le_succ_l low high) H1); intro H2;
      generalize (Nat.lt_le_incl low high H1); intro H3;
        replace (f high) with (sigma high high).
    - rewrite Rplus_comm; cut (high = S (pred high)).
      + intro; pattern high at 3; rewrite H.
        apply sigma_split.
        * apply le_S_n; rewrite <- H; apply Nat.le_succ_l; assumption.
        * apply Nat.lt_pred_l, Nat.neq_0_lt_0; apply Nat.le_lt_trans with low; [ apply Nat.le_0_l | assumption ].
      + symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.le_lt_trans with low;
          [ apply Nat.le_0_l | assumption ].
    - unfold sigma; rewrite Nat.sub_diag; simpl;
        replace (high + 0)%nat with high; [ reflexivity | ring ].
  Qed.

  Theorem sigma_eq_arg : forall low:nat, sigma low low = f low.
  Proof.
    intro; unfold sigma; rewrite Nat.sub_diag.
    simpl; replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

End Sigma.
