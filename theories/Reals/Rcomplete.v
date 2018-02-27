(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import SeqProp.
Require Import Max.
Local Open Scope R_scope.

(****************************************************)
(*              R is complete :                     *)
(*        Each sequence which satisfies             *)
(*       the Cauchy's criterion converges           *)
(*                                                  *)
(*    Proof with adjacent sequences (Vn and Wn)     *)
(****************************************************)

Theorem R_complete :
  forall Un:nat -> R, Cauchy_crit Un -> { l:R | Un_cv Un l } .
Proof.
  intros.
  set (Vn := sequence_minorant Un (cauchy_min Un H)).
  set (Wn := sequence_majorant Un (cauchy_maj Un H)).
  pose proof (maj_cv Un H) as (x,p).
  fold Wn in p.
  pose proof (min_cv Un H) as (x0,p0).
  fold Vn in p0.
  cut (x = x0).
  intros H2.
  exists x.
  rewrite <- H2 in p0.
  unfold Un_cv.
  intros.
  unfold Un_cv in p; unfold Un_cv in p0.
  cut (0 < eps / 3).
  intro H4.
  elim (p (eps / 3) H4); intros.
  elim (p0 (eps / 3) H4); intros.
  exists (max x1 x2).
  intros.
  unfold R_dist.
  apply Rle_lt_trans with (Rabs (Un n - Vn n) + Rabs (Vn n - x)).
  replace (Un n - x) with (Un n - Vn n + (Vn n - x));
  [ apply Rabs_triang | ring ].
  apply Rle_lt_trans with (Rabs (Wn n - Vn n) + Rabs (Vn n - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (Vn n - x))).
  apply Rplus_le_compat_l.
  repeat rewrite Rabs_right.
  unfold Rminus; do 2 rewrite <- (Rplus_comm (- Vn n));
    apply Rplus_le_compat_l.
  assert (H8 := Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
  fold Vn Wn in H8.
  elim (H8 n); intros.
  assumption.
  apply Rle_ge.
  unfold Rminus; apply Rplus_le_reg_l with (Vn n).
  rewrite Rplus_0_r.
  replace (Vn n + (Wn n + - Vn n)) with (Wn n); [ idtac | ring ].
  assert (H8 := Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
  fold Vn Wn in H8.
  elim (H8 n); intros.
  apply Rle_trans with (Un n); assumption.
  apply Rle_ge.
  unfold Rminus; apply Rplus_le_reg_l with (Vn n).
  rewrite Rplus_0_r.
  replace (Vn n + (Un n + - Vn n)) with (Un n); [ idtac | ring ].
  assert (H8 := Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
  fold Vn Wn in H8.
  elim (H8 n); intros.
  assumption.
  apply Rle_lt_trans with (Rabs (Wn n - x) + Rabs (x - Vn n) + Rabs (Vn n - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (Vn n - x))).
  apply Rplus_le_compat_l.
  replace (Wn n - Vn n) with (Wn n - x + (x - Vn n));
  [ apply Rabs_triang | ring ].
  apply Rlt_le_trans with (eps / 3 + eps / 3 + eps / 3).
  repeat apply Rplus_lt_compat.
  unfold R_dist in H1.
  apply H1.
  unfold ge; apply le_trans with (max x1 x2).
  apply le_max_l.
  assumption.
  rewrite <- Rabs_Ropp.
  replace (- (x - Vn n)) with (Vn n - x); [ idtac | ring ].
  unfold R_dist in H3.
  apply H3.
  unfold ge; apply le_trans with (max x1 x2).
  apply le_max_r.
  assumption.
  unfold R_dist in H3.
  apply H3.
  unfold ge; apply le_trans with (max x1 x2).
  apply le_max_r.
  assumption.
  right.
  pattern eps at 4; replace eps with (3 * (eps / 3)).
  ring.
  unfold Rdiv; rewrite <- Rmult_assoc; apply Rinv_r_simpl_m; discrR.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  apply cond_eq.
  intros.
  cut (0 < eps / 5).
  intro.
  unfold Un_cv in p; unfold Un_cv in p0.
  unfold R_dist in p; unfold R_dist in p0.
  elim (p (eps / 5) H1); intros N1 H4.
  elim (p0 (eps / 5) H1); intros N2 H5.
  unfold Cauchy_crit in H.
  unfold R_dist in H.
  elim (H (eps / 5) H1); intros N3 H6.
  set (N := max (max N1 N2) N3).
  apply Rle_lt_trans with (Rabs (x - Wn N) + Rabs (Wn N - x0)).
  replace (x - x0) with (x - Wn N + (Wn N - x0)); [ apply Rabs_triang | ring ].
  apply Rle_lt_trans with
    (Rabs (x - Wn N) + Rabs (Wn N - Vn N) + Rabs (Vn N - x0)).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  replace (Wn N - x0) with (Wn N - Vn N + (Vn N - x0));
  [ apply Rabs_triang | ring ].
  replace eps with (eps / 5 + 3 * (eps / 5) + eps / 5).
  repeat apply Rplus_lt_compat.
  rewrite <- Rabs_Ropp.
  replace (- (x - Wn N)) with (Wn N - x); [ apply H4 | ring ].
  unfold ge, N.
  apply le_trans with (max N1 N2); apply le_max_l.
  unfold Wn, Vn.
  unfold sequence_majorant, sequence_minorant.
  assert
    (H7 :=
      approx_maj (fun k:nat => Un (N + k)%nat) (maj_ss Un N (cauchy_maj Un H))).
  assert
    (H8 :=
      approx_min (fun k:nat => Un (N + k)%nat) (min_ss Un N (cauchy_min Un H))).
  cut
    (Wn N =
      majorant (fun k:nat => Un (N + k)%nat) (maj_ss Un N (cauchy_maj Un H))).
  cut
    (Vn N =
      minorant (fun k:nat => Un (N + k)%nat) (min_ss Un N (cauchy_min Un H))).
  intros H9 H10.
  rewrite <- H9 in H8 |- *.
  rewrite <- H10 in H7 |- *.
  elim (H7 (eps / 5) H1); intros k2 H11.
  elim (H8 (eps / 5) H1); intros k1 H12.
  apply Rle_lt_trans with
    (Rabs (Wn N - Un (N + k2)%nat) + Rabs (Un (N + k2)%nat - Vn N)).
  replace (Wn N - Vn N) with
  (Wn N - Un (N + k2)%nat + (Un (N + k2)%nat - Vn N));
  [ apply Rabs_triang | ring ].
  apply Rle_lt_trans with
    (Rabs (Wn N - Un (N + k2)%nat) + Rabs (Un (N + k2)%nat - Un (N + k1)%nat) +
      Rabs (Un (N + k1)%nat - Vn N)).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  replace (Un (N + k2)%nat - Vn N) with
  (Un (N + k2)%nat - Un (N + k1)%nat + (Un (N + k1)%nat - Vn N));
  [ apply Rabs_triang | ring ].
  replace (3 * (eps / 5)) with (eps / 5 + eps / 5 + eps / 5);
  [ repeat apply Rplus_lt_compat | ring ].
  assumption.
  apply H6.
  unfold ge.
  apply le_trans with N.
  unfold N; apply le_max_r.
  apply le_plus_l.
  unfold ge.
  apply le_trans with N.
  unfold N; apply le_max_r.
  apply le_plus_l.
  rewrite <- Rabs_Ropp.
  replace (- (Un (N + k1)%nat - Vn N)) with (Vn N - Un (N + k1)%nat);
  [ assumption | ring ].
  reflexivity.
  reflexivity.
  apply H5.
  unfold ge; apply le_trans with (max N1 N2).
  apply le_max_r.
  unfold N; apply le_max_l.
  pattern eps at 4; replace eps with (5 * (eps / 5)).
  ring.
  unfold Rdiv; rewrite <- Rmult_assoc; apply Rinv_r_simpl_m.
  discrR.
  unfold Rdiv; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat.
  prove_sup0; try apply lt_O_Sn.
Qed.
