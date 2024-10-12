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
Local Open Scope R_scope.

  (**********)
Lemma sum_N_predN :
  forall (An:nat -> R) (N:nat),
    (0 < N)%nat -> sum_f_R0 An N = sum_f_R0 An (pred N) + An N.
Proof.
  intros.
  replace N with (S (pred N)).
  - rewrite tech5.
    reflexivity.
  - apply Nat.lt_succ_pred with 0%nat; assumption.
Qed.

  (**********)
Lemma sum_plus :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun l:nat => An l + Bn l) N = sum_f_R0 An N + sum_f_R0 Bn N.
Proof.
  intros.
  induction  N as [| N HrecN].
  - reflexivity.
  - do 3 rewrite tech5.
    rewrite HrecN; ring.
Qed.

  (* The main result *)
Theorem cauchy_finite :
  forall (An Bn:nat -> R) (N:nat),
    (0 < N)%nat ->
    sum_f_R0 An N * sum_f_R0 Bn N =
    sum_f_R0 (fun k:nat => sum_f_R0 (fun p:nat => An p * Bn (k - p)%nat) k) N +
    sum_f_R0
    (fun k:nat =>
      sum_f_R0 (fun l:nat => An (S (l + k)) * Bn (N - l)%nat)
      (pred (N - k))) (pred N).
Proof.
  intros; induction  N as [| N HrecN].
  { elim (Nat.lt_irrefl _ H). }
  assert (H0:N = 0%nat \/ (0 < N)%nat). {
    inversion H.
    - left; reflexivity.
    - right; apply Nat.lt_le_trans with 1%nat; [ apply Nat.lt_succ_diag_r | exact H1 ].
  }
  elim H0; intro.
  { rewrite H1; simpl; ring. }
  replace (pred (S N)) with (S (pred N))
    by (simpl; apply Nat.lt_succ_pred with 0%nat; assumption).
  do 5 rewrite tech5.
  rewrite Rmult_plus_distr_r; rewrite Rmult_plus_distr_l; rewrite (HrecN H1).
  repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  replace (pred (S N - S (pred N))) with 0%nat by auto with zarith.
  rewrite Rmult_plus_distr_l;
    replace
      (sum_f_R0 (fun l:nat => An (S (l + S (pred N))) * Bn (S N - l)%nat) 0) with
    (An (S N) * Bn (S N)).
  2:{ simpl. replace (S (pred N)) with N by auto with zarith.
      reflexivity. }
  repeat rewrite <- Rplus_assoc;
    do 2 rewrite <- (Rplus_comm (An (S N) * Bn (S N)));
    repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  rewrite Nat.sub_diag; assert (H2:N = 1%nat \/ (2 <= N)%nat).
  { inversion H1.
    - left; reflexivity.
    - right; apply le_n_S; assumption. }
  elim H2; intro.
  { rewrite H3; simpl; ring. }
  replace
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (l + k)) * Bn (N - l)%nat) (pred (N - k)))
       (pred N)) with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (pred (N - k)))) (pred (pred N))
     + sum_f_R0 (fun l:nat => An (S l) * Bn (N - l)%nat) (pred N)).
  2:{ rewrite Rplus_comm.
      rewrite
        (decomp_sum
           (fun k:nat =>
              sum_f_R0 (fun l:nat => An (S (l + k)) * Bn (N - l)%nat) (pred (N - k)))
           (pred N)).
      2:{ auto with zarith. }
      rewrite Nat.sub_0_r.
      replace (sum_f_R0 (fun l:nat => An (S (l + 0)) * Bn (N - l)%nat) (pred N))
        with (sum_f_R0 (fun l:nat => An (S l) * Bn (N - l)%nat) (pred N)).
      2:{ apply sum_eq; intros.
          replace (i + 0)%nat with i by trivial; reflexivity. }
      apply Rplus_eq_compat_l.
      apply sum_eq; intros.
      replace (pred (N - S i)) with (pred (pred (N - i))) by auto with zarith.
      apply sum_eq; intros.
      replace (i0 + S i)%nat with (S (i0 + i)) by auto with zarith.
      reflexivity.
  }
  replace (sum_f_R0 (fun p:nat => An p * Bn (S N - p)%nat) N) with
    (sum_f_R0 (fun l:nat => An (S l) * Bn (N - l)%nat) (pred N) +
       An 0%nat * Bn (S N)).
  2:{ rewrite Rplus_comm.
      rewrite (decomp_sum (fun p:nat => An p * Bn (S N - p)%nat) N).
      - reflexivity.
      - assumption.
  }
  repeat rewrite <- Rplus_assoc;
    rewrite <-
            (Rplus_comm (sum_f_R0 (fun l:nat => An (S l) * Bn (N - l)%nat) (pred N)))
  ; repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  replace
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (l + k)) * Bn (S N - l)%nat)
                   (pred (S N - k))) (pred N)) with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (N - k))) (pred N) +
       Bn (S N) * sum_f_R0 (fun l:nat => An (S l)) (pred N)).
  2:{ replace
        (sum_f_R0
           (fun k:nat =>
              sum_f_R0 (fun l:nat => An (S (l + k)) * Bn (S N - l)%nat)
                       (pred (S N - k))) (pred N)) with
         (sum_f_R0
            (fun k:nat =>
               sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                        (pred (N - k)) + An (S k) * Bn (S N)) (pred N)).
      { rewrite
          (sum_plus
             (fun k:nat =>
                sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                         (pred (N - k))) (fun k:nat => An (S k) * Bn (S N))).
        apply Rplus_eq_compat_l.
        rewrite scal_sum; reflexivity.
      }
      apply sum_eq; intros; rewrite Rplus_comm;
        rewrite
          (decomp_sum (fun l:nat => An (S (l + i)) * Bn (S N - l)%nat)
                      (pred (S N - i))).
      2:{ auto with zarith. }
      replace (0 + i)%nat with i by ring.
      rewrite Nat.sub_0_r; apply Rplus_eq_compat_l.
      replace (pred (pred (S N - i))) with (pred (N - i)) by auto with zarith.
      apply sum_eq; intros.
      replace (S N - S i0)%nat with (N - i0)%nat; [ idtac | reflexivity ].
      replace (S i0 + i)%nat with (S (i0 + i)) by auto with zarith.
      reflexivity.
  }
  rewrite (decomp_sum An N H1); rewrite Rmult_plus_distr_r;
  repeat rewrite <- Rplus_assoc; rewrite <- (Rplus_comm (An 0%nat * Bn (S N)));
  repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc;
  rewrite <- (Rplus_comm (sum_f_R0 (fun i:nat => An (S i)) (pred N) * Bn (S N)));
  rewrite <- (Rplus_comm (Bn (S N) * sum_f_R0 (fun i:nat => An (S i)) (pred N)));
  rewrite (Rmult_comm (Bn (S N))); repeat rewrite Rplus_assoc;
  apply Rplus_eq_compat_l.
  replace
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (N - k))) (pred N)) with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (pred (N - k)))) (pred (pred N)) +
       An (S N) * sum_f_R0 (fun l:nat => Bn (S l)) (pred N)).
  { rewrite (decomp_sum Bn N H1); rewrite Rmult_plus_distr_l.
    set
      (Z :=
         sum_f_R0
           (fun k:nat =>
              sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                       (pred (pred (N - k)))) (pred (pred N)));
      set (Z2 := sum_f_R0 (fun i:nat => Bn (S i)) (pred N));
      ring.
  }
  rewrite
    (sum_N_predN
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (N - k))) (pred N)).
  2:{ auto with zarith. }
  replace
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (N - k))) (pred (pred N))) with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (pred (N - k))) + An (S N) * Bn (S k)) (
         pred (pred N))).
  2:{ apply sum_eq; intros;
      rewrite
        (sum_N_predN (fun l:nat => An (S (S (l + i))) * Bn (N - l)%nat)
                     (pred (N - i))).
      2:{ auto with zarith. }
      replace (S (S (pred (N - i) + i))) with (S N) by auto with zarith.
      replace (N - pred (N - i))%nat with (S i) by auto with zarith.
      reflexivity.
  }
  rewrite
    (sum_plus
       (fun k:nat =>
          sum_f_R0 (fun l:nat => An (S (S (l + k))) * Bn (N - l)%nat)
                   (pred (pred (N - k)))) (fun k:nat => An (S N) * Bn (S k))
       (pred (pred N))).
  repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  replace (pred (N - pred N)) with 0%nat by auto with zarith.
  simpl; rewrite Nat.sub_0_r.
  replace (S (pred N)) with N by auto with zarith.
  replace (sum_f_R0 (fun k:nat => An (S N) * Bn (S k)) (pred (pred N))) with
    (sum_f_R0 (fun k:nat => Bn (S k) * An (S N)) (pred (pred N))).
  2:{ apply sum_eq; intros; apply Rmult_comm. }
  rewrite <- (scal_sum (fun l:nat => Bn (S l)) (pred (pred N)) (An (S N)));
  rewrite (sum_N_predN (fun l:nat => Bn (S l)) (pred N)).
  2:{ auto with zarith. }
  replace (S (pred N)) with N by auto with zarith.
  ring.
Qed.
