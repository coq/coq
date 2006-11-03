(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import PartSum.
Open Local Scope R_scope.

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
    cut (low = 0%nat).
    intro; rewrite H1; unfold sigma in |- *; rewrite <- minus_n_n;
      rewrite <- minus_n_O; simpl in |- *; replace (high - 1)%nat with (pred high).
    apply (decomp_sum (fun k:nat => f k)).
    assumption.
    apply pred_of_minus.
    inversion H; reflexivity.
    cut ((low <= k)%nat \/ low = S k).
    intro; elim H1; intro.
    replace (sigma low (S k)) with (sigma low k + f (S k)).
    rewrite Rplus_assoc;
      replace (f (S k) + sigma (S (S k)) high) with (sigma (S k) high).
    apply Hreck.
    assumption.
    apply lt_trans with (S k); [ apply lt_n_Sn | assumption ].
    unfold sigma in |- *; replace (high - S (S k))%nat with (pred (high - S k)).
    pattern (S k) at 3 in |- *; replace (S k) with (S k + 0)%nat;
      [ idtac | ring ].
    replace (sum_f_R0 (fun k0:nat => f (S (S k) + k0)) (pred (high - S k))) with
    (sum_f_R0 (fun k0:nat => f (S k + S k0)) (pred (high - S k))).
    apply (decomp_sum (fun i:nat => f (S k + i))).
    apply lt_minus_O_lt; assumption.
    apply sum_eq; intros; replace (S k + S i)%nat with (S (S k) + i)%nat.
    reflexivity.
    ring_nat.
    replace (high - S (S k))%nat with (high - S k - 1)%nat.
    apply pred_of_minus.
    omega.
    unfold sigma in |- *; replace (S k - low)%nat with (S (k - low)).
    pattern (S k) at 1 in |- *; replace (S k) with (low + S (k - low))%nat.
    symmetry  in |- *; apply (tech5 (fun i:nat => f (low + i))).
    omega.
    omega.
    rewrite <- H2; unfold sigma in |- *; rewrite <- minus_n_n; simpl in |- *;
      replace (high - S low)%nat with (pred (high - low)).
    replace (sum_f_R0 (fun k0:nat => f (S (low + k0))) (pred (high - low))) with
    (sum_f_R0 (fun k0:nat => f (low + S k0)) (pred (high - low))).
    apply (decomp_sum (fun k0:nat => f (low + k0))).
    apply lt_minus_O_lt.
    apply le_lt_trans with (S k); [ rewrite H2; apply le_n | assumption ].
    apply sum_eq; intros; replace (S (low + i)) with (low + S i)%nat.
    reflexivity.
    ring_nat.
    omega.
    inversion H; [ right; reflexivity | left; assumption ].
  Qed.

  Theorem sigma_diff :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high - sigma low k = sigma (S k) high.
  Proof.
    intros low high k H1 H2; symmetry  in |- *; rewrite (sigma_split H1 H2); ring.
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
    intros low high H1; generalize (lt_le_S low high H1); intro H2;
      generalize (lt_le_weak low high H1); intro H3;
        replace (f low) with (sigma low low).
    apply sigma_split.
    apply le_n.
    assumption.
    unfold sigma in |- *; rewrite <- minus_n_n.
    simpl in |- *.
    replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

  Theorem sigma_last :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f high + sigma low (pred high).
  Proof.
    intros low high H1; generalize (lt_le_S low high H1); intro H2;
      generalize (lt_le_weak low high H1); intro H3;
        replace (f high) with (sigma high high).
    rewrite Rplus_comm; cut (high = S (pred high)).
    intro; pattern high at 3 in |- *; rewrite H.
    apply sigma_split.
    apply le_S_n; rewrite <- H; apply lt_le_S; assumption.
    apply lt_pred_n_n; apply le_lt_trans with low; [ apply le_O_n | assumption ].
    apply S_pred with 0%nat; apply le_lt_trans with low;
      [ apply le_O_n | assumption ].
    unfold sigma in |- *; rewrite <- minus_n_n; simpl in |- *;
      replace (high + 0)%nat with high; [ reflexivity | ring ].
  Qed.

  Theorem sigma_eq_arg : forall low:nat, sigma low low = f low.
  Proof.
    intro; unfold sigma in |- *; rewrite <- minus_n_n.
    simpl in |- *; replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

End Sigma.
