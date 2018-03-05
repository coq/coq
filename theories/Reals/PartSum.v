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
Require Import Rcomplete.
Require Import Max.
Local Open Scope R_scope.

Lemma tech1 :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> 0 < An n) -> 0 < sum_f_R0 An N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; apply H; apply le_n.
  simpl; apply Rplus_lt_0_compat.
  apply HrecN; intros; apply H; apply le_S; assumption.
  apply H; apply le_n.
Qed.

(* Chasles' relation *)
Lemma tech2 :
  forall (An:nat -> R) (m n:nat),
    (m < n)%nat ->
    sum_f_R0 An n =
    sum_f_R0 An m + sum_f_R0 (fun i:nat => An (S m + i)%nat) (n - S m).
Proof.
  intros; induction  n as [| n Hrecn].
  elim (lt_n_O _ H).
  cut ((m < n)%nat \/ m = n).
  intro; elim H0; intro.
  replace (sum_f_R0 An (S n)) with (sum_f_R0 An n + An (S n));
  [ idtac | reflexivity ].
  replace (S n - S m)%nat with (S (n - S m)).
  replace (sum_f_R0 (fun i:nat => An (S m + i)%nat) (S (n - S m))) with
  (sum_f_R0 (fun i:nat => An (S m + i)%nat) (n - S m) +
    An (S m + S (n - S m))%nat); [ idtac | reflexivity ].
  replace (S m + S (n - S m))%nat with (S n).
  rewrite (Hrecn H1).
  ring.
  apply INR_eq; rewrite S_INR; rewrite plus_INR; do 2 rewrite S_INR;
    rewrite minus_INR.
  rewrite S_INR; ring.
  apply lt_le_S; assumption.
  apply INR_eq; rewrite S_INR; repeat rewrite minus_INR.
  repeat rewrite S_INR; ring.
  apply le_n_S; apply lt_le_weak; assumption.
  apply lt_le_S; assumption.
  rewrite H1; rewrite <- minus_n_n; simpl.
  replace (n + 0)%nat with n; [ reflexivity | ring ].
  inversion H.
  right; reflexivity.
  left; apply lt_le_trans with (S m); [ apply lt_n_Sn | assumption ].
Qed.

(* Sum of geometric sequences *)
Lemma tech3 :
  forall (k:R) (N:nat),
    k <> 1 -> sum_f_R0 (fun i:nat => k ^ i) N = (1 - k ^ S N) / (1 - k).
Proof.
  intros; cut (1 - k <> 0).
  intro; induction  N as [| N HrecN].
  simpl; rewrite Rmult_1_r; unfold Rdiv; rewrite <- Rinv_r_sym.
  reflexivity.
  apply H0.
  replace (sum_f_R0 (fun i:nat => k ^ i) (S N)) with
  (sum_f_R0 (fun i:nat => k ^ i) N + k ^ S N); [ idtac | reflexivity ];
  rewrite HrecN;
    replace ((1 - k ^ S N) / (1 - k) + k ^ S N) with
    ((1 - k ^ S N + (1 - k) * k ^ S N) / (1 - k)).
  apply Rmult_eq_reg_l with (1 - k).
  unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ (1 - k)));
    repeat rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
      [ do 2 rewrite Rmult_1_l; simpl; ring | apply H0 ].
  apply H0.
  unfold Rdiv; rewrite Rmult_plus_distr_r; rewrite (Rmult_comm (1 - k));
    repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; reflexivity.
  apply H0.
  apply Rminus_eq_contra; red; intro; elim H; symmetry ;
    assumption.
Qed.

Lemma tech4 :
  forall (An:nat -> R) (k:R) (N:nat),
    0 <= k -> (forall i:nat, An (S i) < k * An i) -> An N <= An 0%nat * k ^ N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; right; ring.
  apply Rle_trans with (k * An N).
  left; apply (H0 N).
  replace (S N) with (N + 1)%nat; [ idtac | ring ].
  rewrite pow_add; simpl; rewrite Rmult_1_r;
    replace (An 0%nat * (k ^ N * k)) with (k * (An 0%nat * k ^ N));
    [ idtac | ring ]; apply Rmult_le_compat_l.
  assumption.
  apply HrecN.
Qed.

Lemma tech5 :
  forall (An:nat -> R) (N:nat), sum_f_R0 An (S N) = sum_f_R0 An N + An (S N).
Proof.
  intros; reflexivity.
Qed.

Lemma tech6 :
  forall (An:nat -> R) (k:R) (N:nat),
    0 <= k ->
    (forall i:nat, An (S i) < k * An i) ->
    sum_f_R0 An N <= An 0%nat * sum_f_R0 (fun i:nat => k ^ i) N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; right; ring.
  apply Rle_trans with (An 0%nat * sum_f_R0 (fun i:nat => k ^ i) N + An (S N)).
  rewrite tech5; do 2 rewrite <- (Rplus_comm (An (S N)));
    apply Rplus_le_compat_l.
  apply HrecN.
  rewrite tech5; rewrite Rmult_plus_distr_l; apply Rplus_le_compat_l.
  apply tech4; assumption.
Qed.

Lemma tech7 : forall r1 r2:R, r1 <> 0 -> r2 <> 0 -> r1 <> r2 -> / r1 <> / r2.
Proof.
  intros; red; intro.
  assert (H3 := Rmult_eq_compat_l r1 _ _ H2).
  rewrite <- Rinv_r_sym in H3; [ idtac | assumption ].
  assert (H4 := Rmult_eq_compat_l r2 _ _ H3).
  rewrite Rmult_1_r in H4; rewrite <- Rmult_assoc in H4.
  rewrite Rinv_r_simpl_m in H4; [ idtac | assumption ].
  elim H1; symmetry ; assumption.
Qed.

Lemma tech11 :
  forall (An Bn Cn:nat -> R) (N:nat),
    (forall i:nat, An i = Bn i - Cn i) ->
    sum_f_R0 An N = sum_f_R0 Bn N - sum_f_R0 Cn N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; apply H.
  do 3 rewrite tech5; rewrite HrecN; rewrite (H (S N)); ring.
Qed.

Lemma tech12 :
  forall (An:nat -> R) (x l:R),
    Un_cv (fun N:nat => sum_f_R0 (fun i:nat => An i * x ^ i) N) l ->
    Pser An x l.
Proof.
  intros; unfold Pser; unfold infinite_sum; unfold Un_cv in H;
    assumption.
Qed.

Lemma scal_sum :
  forall (An:nat -> R) (N:nat) (x:R),
    x * sum_f_R0 An N = sum_f_R0 (fun i:nat => An i * x) N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; ring.
  do 2 rewrite tech5.
  rewrite Rmult_plus_distr_l; rewrite <- HrecN; ring.
Qed.

Lemma decomp_sum :
  forall (An:nat -> R) (N:nat),
    (0 < N)%nat ->
    sum_f_R0 An N = An 0%nat + sum_f_R0 (fun i:nat => An (S i)) (pred N).
Proof.
  intros; induction  N as [| N HrecN].
  elim (lt_irrefl _ H).
  cut ((0 < N)%nat \/ N = 0%nat).
  intro; elim H0; intro.
  cut (S (pred N) = pred (S N)).
  intro; rewrite <- H2.
  do 2 rewrite tech5.
  replace (S (S (pred N))) with (S N).
  rewrite (HrecN H1); ring.
  rewrite H2; simpl; reflexivity.
  destruct (O_or_S N) as [(m,<-)|<-].
  simpl; reflexivity.
  elim (lt_irrefl _ H1).
  rewrite H1; simpl; reflexivity.
  inversion H.
  right; reflexivity.
  left; apply lt_le_trans with 1%nat; [ apply lt_O_Sn | assumption ].
Qed.

Lemma plus_sum :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun i:nat => An i + Bn i) N = sum_f_R0 An N + sum_f_R0 Bn N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; ring.
  do 3 rewrite tech5; rewrite HrecN; ring.
Qed.

Lemma sum_eq :
  forall (An Bn:nat -> R) (N:nat),
    (forall i:nat, (i <= N)%nat -> An i = Bn i) ->
    sum_f_R0 An N = sum_f_R0 Bn N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; apply H; apply le_n.
  do 2 rewrite tech5; rewrite HrecN.
  rewrite (H (S N)); [ reflexivity | apply le_n ].
  intros; apply H; apply le_trans with N; [ assumption | apply le_n_Sn ].
Qed.

(* Unicity of the limit defined by convergent series *)
Lemma uniqueness_sum :
  forall (An:nat -> R) (l1 l2:R),
    infinite_sum An l1 -> infinite_sum An l2 -> l1 = l2.
Proof.
  unfold infinite_sum; intros.
  case (Req_dec l1 l2); intro.
  assumption.
  cut (0 < Rabs ((l1 - l2) / 2)); [ intro | apply Rabs_pos_lt ].
  elim (H (Rabs ((l1 - l2) / 2)) H2); intros.
  elim (H0 (Rabs ((l1 - l2) / 2)) H2); intros.
  set (N := max x0 x); cut (N >= x0)%nat.
  cut (N >= x)%nat.
  intros; assert (H7 := H3 N H5); assert (H8 := H4 N H6).
  cut (Rabs (l1 - l2) <= R_dist (sum_f_R0 An N) l1 + R_dist (sum_f_R0 An N) l2).
  intro; assert (H10 := Rplus_lt_compat _ _ _ _ H7 H8);
    assert (H11 := Rle_lt_trans _ _ _ H9 H10); unfold Rdiv in H11;
      rewrite Rabs_mult in H11.
  cut (Rabs (/ 2) = / 2).
  intro; rewrite H12 in H11; assert (H13 := double_var); unfold Rdiv in H13;
    rewrite <- H13 in H11.
  elim (Rlt_irrefl _ H11).
  apply Rabs_right; left; change (0 < / 2); apply Rinv_0_lt_compat;
    cut (0%nat <> 2%nat);
      [ intro H20; generalize (lt_INR_0 2 (neq_O_lt 2 H20)); unfold INR;
        intro; assumption
        | discriminate ].
  unfold R_dist; rewrite <- (Rabs_Ropp (sum_f_R0 An N - l1));
    rewrite Ropp_minus_distr'.
  replace (l1 - l2) with (l1 - sum_f_R0 An N + (sum_f_R0 An N - l2));
  [ idtac | ring ].
  apply Rabs_triang.
  unfold ge; unfold N; apply le_max_r.
  unfold ge; unfold N; apply le_max_l.
  unfold Rdiv; apply prod_neq_R0.
  apply Rminus_eq_contra; assumption.
  apply Rinv_neq_0_compat; discrR.
Qed.

Lemma minus_sum :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun i:nat => An i - Bn i) N = sum_f_R0 An N - sum_f_R0 Bn N.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; ring.
  do 3 rewrite tech5; rewrite HrecN; ring.
Qed.

Lemma sum_decomposition :
  forall (An:nat -> R) (N:nat),
    sum_f_R0 (fun l:nat => An (2 * l)%nat) (S N) +
    sum_f_R0 (fun l:nat => An (S (2 * l))) N = sum_f_R0 An (2 * S N).
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl; ring.
  rewrite tech5.
  rewrite (tech5 (fun l:nat => An (S (2 * l))) N).
  replace (2 * S (S N))%nat with (S (S (2 * S N))).
  rewrite (tech5 An (S (2 * S N))).
  rewrite (tech5 An (2 * S N)).
  rewrite <- HrecN.
  ring.
  ring.
Qed.

Lemma sum_Rle :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> An n <= Bn n) ->
    sum_f_R0 An N <= sum_f_R0 Bn N.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl; apply H.
  apply le_n.
  do 2 rewrite tech5.
  apply Rle_trans with (sum_f_R0 An N + Bn (S N)).
  apply Rplus_le_compat_l.
  apply H.
  apply le_n.
  do 2 rewrite <- (Rplus_comm (Bn (S N))).
  apply Rplus_le_compat_l.
  apply HrecN.
  intros; apply H.
  apply le_trans with N; [ assumption | apply le_n_Sn ].
Qed.

Lemma Rsum_abs :
  forall (An:nat -> R) (N:nat),
    Rabs (sum_f_R0 An N) <= sum_f_R0 (fun l:nat => Rabs (An l)) N.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl.
  right; reflexivity.
  do 2 rewrite tech5.
  apply Rle_trans with (Rabs (sum_f_R0 An N) + Rabs (An (S N))).
  apply Rabs_triang.
  do 2 rewrite <- (Rplus_comm (Rabs (An (S N)))).
  apply Rplus_le_compat_l.
  apply HrecN.
Qed.

Lemma sum_cte :
  forall (x:R) (N:nat), sum_f_R0 (fun _:nat => x) N = x * INR (S N).
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl; ring.
  rewrite tech5.
  rewrite HrecN; repeat rewrite S_INR; ring.
Qed.

(**********)
Lemma sum_growing :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, An n <= Bn n) -> sum_f_R0 An N <= sum_f_R0 Bn N.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl; apply H.
  do 2 rewrite tech5.
  apply Rle_trans with (sum_f_R0 An N + Bn (S N)).
  apply Rplus_le_compat_l; apply H.
  do 2 rewrite <- (Rplus_comm (Bn (S N))).
  apply Rplus_le_compat_l; apply HrecN.
Qed.

(**********)
Lemma Rabs_triang_gen :
  forall (An:nat -> R) (N:nat),
    Rabs (sum_f_R0 An N) <= sum_f_R0 (fun i:nat => Rabs (An i)) N.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl.
  right; reflexivity.
  do 2 rewrite tech5.
  apply Rle_trans with (Rabs (sum_f_R0 An N) + Rabs (An (S N))).
  apply Rabs_triang.
  do 2 rewrite <- (Rplus_comm (Rabs (An (S N)))).
  apply Rplus_le_compat_l; apply HrecN.
Qed.

(**********)
Lemma cond_pos_sum :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, 0 <= An n) -> 0 <= sum_f_R0 An N.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl; apply H.
  rewrite tech5.
  apply Rplus_le_le_0_compat.
  apply HrecN.
  apply H.
Qed.

(* Cauchy's criterion for series *)
Definition Cauchy_crit_series (An:nat -> R) : Prop :=
  Cauchy_crit (fun N:nat => sum_f_R0 An N).

(* If (|An|) satisfies the Cauchy's criterion for series, then (An) too *)
Lemma cauchy_abs :
  forall An:nat -> R,
    Cauchy_crit_series (fun i:nat => Rabs (An i)) -> Cauchy_crit_series An.
Proof.
  unfold Cauchy_crit_series; unfold Cauchy_crit.
  intros.
  elim (H eps H0); intros.
  exists x.
  intros.
  cut
    (R_dist (sum_f_R0 An n) (sum_f_R0 An m) <=
      R_dist (sum_f_R0 (fun i:nat => Rabs (An i)) n)
      (sum_f_R0 (fun i:nat => Rabs (An i)) m)).
  intro.
  apply Rle_lt_trans with
    (R_dist (sum_f_R0 (fun i:nat => Rabs (An i)) n)
      (sum_f_R0 (fun i:nat => Rabs (An i)) m)).
  assumption.
  apply H1; assumption.
  destruct (lt_eq_lt_dec n m) as [[ | -> ]|].
  rewrite (tech2 An n m); [ idtac | assumption ].
  rewrite (tech2 (fun i:nat => Rabs (An i)) n m); [ idtac | assumption ].
  unfold R_dist.
  unfold Rminus.
  do 2 rewrite Ropp_plus_distr.
  do 2 rewrite <- Rplus_assoc.
  do 2 rewrite Rplus_opp_r.
  do 2 rewrite Rplus_0_l.
  do 2 rewrite Rabs_Ropp.
  rewrite
    (Rabs_right (sum_f_R0 (fun i:nat => Rabs (An (S n + i)%nat)) (m - S n)))
    .
  set (Bn := fun i:nat => An (S n + i)%nat).
  replace (fun i:nat => Rabs (An (S n + i)%nat)) with
  (fun i:nat => Rabs (Bn i)).
  apply Rabs_triang_gen.
  unfold Bn; reflexivity.
  apply Rle_ge.
  apply cond_pos_sum.
  intro; apply Rabs_pos.
  unfold R_dist.
  unfold Rminus; do 2 rewrite Rplus_opp_r.
  rewrite Rabs_R0; right; reflexivity.
  rewrite (tech2 An m n); [ idtac | assumption ].
  rewrite (tech2 (fun i:nat => Rabs (An i)) m n); [ idtac | assumption ].
  unfold R_dist.
  unfold Rminus.
  do 2 rewrite Rplus_assoc.
  rewrite (Rplus_comm (sum_f_R0 An m)).
  rewrite (Rplus_comm (sum_f_R0 (fun i:nat => Rabs (An i)) m)).
  do 2 rewrite Rplus_assoc.
  do 2 rewrite Rplus_opp_l.
  do 2 rewrite Rplus_0_r.
  rewrite
    (Rabs_right (sum_f_R0 (fun i:nat => Rabs (An (S m + i)%nat)) (n - S m)))
    .
  set (Bn := fun i:nat => An (S m + i)%nat).
  replace (fun i:nat => Rabs (An (S m + i)%nat)) with
  (fun i:nat => Rabs (Bn i)).
  apply Rabs_triang_gen.
  unfold Bn; reflexivity.
  apply Rle_ge.
  apply cond_pos_sum.
  intro; apply Rabs_pos.
Qed.

(**********)
Lemma cv_cauchy_1 :
  forall An:nat -> R,
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l } ->
    Cauchy_crit_series An.
Proof.
  intros An (x,p).
  unfold Un_cv in p.
  unfold Cauchy_crit_series; unfold Cauchy_crit.
  intros.
  cut (0 < eps / 2).
  intro.
  elim (p (eps / 2) H0); intros.
  exists x0.
  intros.
  apply Rle_lt_trans with (R_dist (sum_f_R0 An n) x + R_dist (sum_f_R0 An m) x).
  unfold R_dist.
  replace (sum_f_R0 An n - sum_f_R0 An m) with
  (sum_f_R0 An n - x + - (sum_f_R0 An m - x)); [ idtac | ring ].
  rewrite <- (Rabs_Ropp (sum_f_R0 An m - x)).
  apply Rabs_triang.
  apply Rlt_le_trans with (eps / 2 + eps / 2).
  apply Rplus_lt_compat.
  apply H1; assumption.
  apply H1; assumption.
  right; symmetry ; apply double_var.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
Qed.

Lemma cv_cauchy_2 :
  forall An:nat -> R,
    Cauchy_crit_series An ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros.
  apply R_complete.
  unfold Cauchy_crit_series in H.
  exact H.
Qed.

(**********)
Lemma sum_eq_R0 :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> An n = 0) -> sum_f_R0 An N = 0.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; apply H; apply le_n.
  rewrite tech5; rewrite HrecN;
    [ rewrite Rplus_0_l; apply H; apply le_n
      | intros; apply H; apply le_trans with N; [ assumption | apply le_n_Sn ] ].
Qed.

Definition SP (fn:nat -> R -> R) (N:nat) (x:R) : R :=
  sum_f_R0 (fun k:nat => fn k x) N.

(**********)
Lemma sum_incr :
  forall (An:nat -> R) (N:nat) (l:R),
    Un_cv (fun n:nat => sum_f_R0 An n) l ->
    (forall n:nat, 0 <= An n) -> sum_f_R0 An N <= l.
Proof.
  intros; destruct (total_order_T (sum_f_R0 An N) l) as [[Hlt|Heq]|Hgt].
  left; apply Hlt.
  right; apply Heq.
  cut (Un_growing (fun n:nat => sum_f_R0 An n)).
  intro; set (l1 := sum_f_R0 An N) in Hgt.
  unfold Un_cv in H; cut (0 < l1 - l).
  intro; elim (H _ H2); intros.
  set (N0 := max x N); cut (N0 >= x)%nat.
  intro; assert (H5 := H3 N0 H4).
  cut (l1 <= sum_f_R0 An N0).
  intro; unfold R_dist in H5; rewrite Rabs_right in H5.
  cut (sum_f_R0 An N0 < l1).
  intro; elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H7 H6)).
  apply Rplus_lt_reg_l with (- l).
  do 2 rewrite (Rplus_comm (- l)).
  apply H5.
  apply Rle_ge; apply Rplus_le_reg_l with l.
  rewrite Rplus_0_r; replace (l + (sum_f_R0 An N0 - l)) with (sum_f_R0 An N0);
    [ idtac | ring ]; apply Rle_trans with l1.
  left; apply Hgt.
  apply H6.
  unfold l1; apply Rge_le;
    apply (growing_prop (fun k:nat => sum_f_R0 An k)).
  apply H1.
  unfold ge, N0; apply le_max_r.
  unfold ge, N0; apply le_max_l.
  apply Rplus_lt_reg_l with l; rewrite Rplus_0_r;
    replace (l + (l1 - l)) with l1; [ apply Hgt | ring ].
  unfold Un_growing; intro; simpl;
    pattern (sum_f_R0 An n) at 1; rewrite <- Rplus_0_r;
      apply Rplus_le_compat_l; apply H0.
Qed.

(**********)
Lemma sum_cv_maj :
  forall (An:nat -> R) (fn:nat -> R -> R) (x l1 l2:R),
    Un_cv (fun n:nat => SP fn n x) l1 ->
    Un_cv (fun n:nat => sum_f_R0 An n) l2 ->
    (forall n:nat, Rabs (fn n x) <= An n) -> Rabs l1 <= l2.
Proof.
  intros; destruct (total_order_T (Rabs l1) l2) as [[Hlt|Heq]|Hgt].
  left; apply Hlt.
  right; apply Heq.
  cut (forall n0:nat, Rabs (SP fn n0 x) <= sum_f_R0 An n0).
  intro; cut (0 < (Rabs l1 - l2) / 2).
  intro; unfold Un_cv in H, H0.
  elim (H _ H3); intros Na H4.
  elim (H0 _ H3); intros Nb H5.
  set (N := max Na Nb).
  unfold R_dist in H4, H5.
  cut (Rabs (sum_f_R0 An N - l2) < (Rabs l1 - l2) / 2).
  intro; cut (Rabs (Rabs l1 - Rabs (SP fn N x)) < (Rabs l1 - l2) / 2).
  intro; cut (sum_f_R0 An N < (Rabs l1 + l2) / 2).
  intro; cut ((Rabs l1 + l2) / 2 < Rabs (SP fn N x)).
  intro; cut (sum_f_R0 An N < Rabs (SP fn N x)).
  intro; assert (H11 := H2 N).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H11 H10)).
  apply Rlt_trans with ((Rabs l1 + l2) / 2); assumption.
  destruct (Rcase_abs (Rabs l1 - Rabs (SP fn N x))) as [Hlt|Hge].
  apply Rlt_trans with (Rabs l1).
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv; rewrite (Rmult_comm 2); rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite double; apply Rplus_lt_compat_l; apply Hgt.
  discrR.
  apply (Rminus_lt _ _ Hlt).
  rewrite (Rabs_right _ Hge) in H7.
  apply Rplus_lt_reg_l with ((Rabs l1 - l2) / 2 - Rabs (SP fn N x)).
  replace ((Rabs l1 - l2) / 2 - Rabs (SP fn N x) + (Rabs l1 + l2) / 2) with
  (Rabs l1 - Rabs (SP fn N x)).
  unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_l;
    rewrite Rplus_0_r; apply H7.
  unfold Rdiv; rewrite Rmult_plus_distr_r;
    rewrite <- (Rmult_comm (/ 2)); rewrite Rmult_minus_distr_l;
      repeat rewrite (Rmult_comm (/ 2)); pattern (Rabs l1) at 1;
        rewrite double_var; unfold Rdiv in |- *; ring.
  destruct (Rcase_abs (sum_f_R0 An N - l2)) as [Hlt|Hge].
  apply Rlt_trans with l2.
  apply (Rminus_lt _ _ Hlt).
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite (double l2); unfold Rdiv; rewrite (Rmult_comm 2);
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite (Rplus_comm (Rabs l1)); apply Rplus_lt_compat_l;
    apply Hgt.
  discrR.
  rewrite (Rabs_right _ Hge) in H6; apply Rplus_lt_reg_l with (- l2).
  replace (- l2 + (Rabs l1 + l2) / 2) with ((Rabs l1 - l2) / 2).
  rewrite Rplus_comm; apply H6.
  unfold Rdiv; rewrite <- (Rmult_comm (/ 2));
    rewrite Rmult_minus_distr_l; rewrite Rmult_plus_distr_r;
      pattern l2 at 2; rewrite double_var;
        repeat rewrite (Rmult_comm (/ 2)); rewrite Ropp_plus_distr;
          unfold Rdiv; ring.
  apply Rle_lt_trans with (Rabs (SP fn N x - l1)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr'; apply Rabs_triang_inv2.
  apply H4; unfold ge, N; apply le_max_l.
  apply H5; unfold ge, N; apply le_max_r.
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_l with l2.
  rewrite Rplus_0_r; replace (l2 + (Rabs l1 - l2)) with (Rabs l1);
    [ apply Hgt | ring ].
  apply Rinv_0_lt_compat; prove_sup0.
  intros; induction  n0 as [| n0 Hrecn0].
  unfold SP; simpl; apply H1.
  unfold SP; simpl.
  apply Rle_trans with
    (Rabs (sum_f_R0 (fun k:nat => fn k x) n0) + Rabs (fn (S n0) x)).
  apply Rabs_triang.
  apply Rle_trans with (sum_f_R0 An n0 + Rabs (fn (S n0) x)).
  do 2 rewrite <- (Rplus_comm (Rabs (fn (S n0) x))).
  apply Rplus_le_compat_l; apply Hrecn0.
  apply Rplus_le_compat_l; apply H1.
Qed.
