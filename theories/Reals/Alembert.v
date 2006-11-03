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
Require Import SeqProp.
Require Import PartSum.
Require Import Max.

Open Local Scope R_scope.

(***************************************************)
(* Various versions of the criterion of D'Alembert *)
(***************************************************)

Lemma Alembert_C1 :
  forall An:nat -> R,
    (forall n:nat, 0 < An n) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l).
Proof.
  intros An H H0.
  cut
    (sigT (fun l:R => is_lub (EUn (fun N:nat => sum_f_R0 An N)) l) ->
      sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l)).
  intro X; apply X.
  apply completeness.
  unfold Un_cv in H0; unfold bound in |- *; cut (0 < / 2);
    [ intro | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H0 (/ 2) H1); intros.
  exists (sum_f_R0 An x + 2 * An (S x)).
  unfold is_upper_bound in |- *; intros; unfold EUn in H3; elim H3; intros.
  rewrite H4; assert (H5 := lt_eq_lt_dec x1 x).
  elim H5; intros.
  elim a; intro.
  replace (sum_f_R0 An x) with
    (sum_f_R0 An x1 + sum_f_R0 (fun i:nat => An (S x1 + i)%nat) (x - S x1)).
  pattern (sum_f_R0 An x1) at 1 in |- *; rewrite <- Rplus_0_r;
    rewrite Rplus_assoc; apply Rplus_le_compat_l.
  left; apply Rplus_lt_0_compat.
  apply tech1; intros; apply H.
  apply Rmult_lt_0_compat; [ prove_sup0 | apply H ].
  symmetry  in |- *; apply tech2; assumption.
  rewrite b; pattern (sum_f_R0 An x) at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_le_compat_l.
  left; apply Rmult_lt_0_compat; [ prove_sup0 | apply H ].
  replace (sum_f_R0 An x1) with
    (sum_f_R0 An x + sum_f_R0 (fun i:nat => An (S x + i)%nat) (x1 - S x)).
  apply Rplus_le_compat_l.
  cut
    (sum_f_R0 (fun i:nat => An (S x + i)%nat) (x1 - S x) <=
      An (S x) * sum_f_R0 (fun i:nat => (/ 2) ^ i) (x1 - S x)).
  intro;
    apply Rle_trans with
      (An (S x) * sum_f_R0 (fun i:nat => (/ 2) ^ i) (x1 - S x)).
  assumption.
  rewrite <- (Rmult_comm (An (S x))); apply Rmult_le_compat_l.
  left; apply H.
  rewrite tech3.
  replace (1 - / 2) with (/ 2).
  unfold Rdiv in |- *; rewrite Rinv_involutive.
  pattern 2 at 3 in |- *; rewrite <- Rmult_1_r; rewrite <- (Rmult_comm 2);
    apply Rmult_le_compat_l.
  left; prove_sup0.
  left; apply Rplus_lt_reg_r with ((/ 2) ^ S (x1 - S x)).
  replace ((/ 2) ^ S (x1 - S x) + (1 - (/ 2) ^ S (x1 - S x))) with 1;
    [ idtac | ring ].
  rewrite <- (Rplus_comm 1); pattern 1 at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_lt_compat_l.
  apply pow_lt; apply Rinv_0_lt_compat; prove_sup0.
  discrR.
  apply Rmult_eq_reg_l with 2.
  rewrite Rmult_minus_distr_l; rewrite <- Rinv_r_sym.
  ring.
  discrR.
  discrR.
  pattern 1 at 3 in |- *; replace 1 with (/ 1);
    [ apply tech7; discrR | apply Rinv_1 ].
  replace (An (S x)) with (An (S x + 0)%nat).
  apply (tech6 (fun i:nat => An (S x + i)%nat) (/ 2)).
  left; apply Rinv_0_lt_compat; prove_sup0.
  intro; cut (forall n:nat, (n >= x)%nat -> An (S n) < / 2 * An n).
  intro; replace (S x + S i)%nat with (S (S x + i)).
  apply H6; unfold ge in |- *; apply tech8.
  apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR; do 2 rewrite S_INR; ring.
  intros; unfold R_dist in H2; apply Rmult_lt_reg_l with (/ An n).
  apply Rinv_0_lt_compat; apply H.
  do 2 rewrite (Rmult_comm (/ An n)); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r;
    replace (An (S n) * / An n) with (Rabs (Rabs (An (S n) / An n) - 0)).
  apply H2; assumption.
  unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite Rabs_Rabsolu; rewrite Rabs_right.
  unfold Rdiv in |- *; reflexivity.
  left; unfold Rdiv in |- *; change (0 < An (S n) * / An n) in |- *;
    apply Rmult_lt_0_compat; [ apply H | apply Rinv_0_lt_compat; apply H ].
  red in |- *; intro; assert (H8 := H n); rewrite H7 in H8;
    elim (Rlt_irrefl _ H8).
  replace (S x + 0)%nat with (S x); [ reflexivity | ring ].
  symmetry  in |- *; apply tech2; assumption.
  exists (sum_f_R0 An 0); unfold EUn in |- *; exists 0%nat; reflexivity.
  intro X; elim X; intros.
  apply existT with x; apply tech10;
    [ unfold Un_growing in |- *; intro; rewrite tech5;
      pattern (sum_f_R0 An n) at 1 in |- *; rewrite <- Rplus_0_r;
	apply Rplus_le_compat_l; left; apply H
      | apply p ].
Qed.

Lemma Alembert_C2 :
  forall An:nat -> R,
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l).
Proof.
  intros.
  set (Vn := fun i:nat => (2 * Rabs (An i) + An i) / 2).
  set (Wn := fun i:nat => (2 * Rabs (An i) - An i) / 2).
  cut (forall n:nat, 0 < Vn n).
  intro; cut (forall n:nat, 0 < Wn n).
  intro; cut (Un_cv (fun n:nat => Rabs (Vn (S n) / Vn n)) 0).
  intro; cut (Un_cv (fun n:nat => Rabs (Wn (S n) / Wn n)) 0).
  intro; assert (H5 := Alembert_C1 Vn H1 H3).
  assert (H6 := Alembert_C1 Wn H2 H4).
  elim H5; intros.
  elim H6; intros.
  apply existT with (x - x0); unfold Un_cv in |- *; unfold Un_cv in p;
    unfold Un_cv in p0; intros; cut (0 < eps / 2).
  intro; elim (p (eps / 2) H8); clear p; intros.
  elim (p0 (eps / 2) H8); clear p0; intros.
  set (N := max x1 x2).
  exists N; intros;
    replace (sum_f_R0 An n) with (sum_f_R0 Vn n - sum_f_R0 Wn n).
  unfold R_dist in |- *;
    replace (sum_f_R0 Vn n - sum_f_R0 Wn n - (x - x0)) with
      (sum_f_R0 Vn n - x + - (sum_f_R0 Wn n - x0)); [ idtac | ring ];
      apply Rle_lt_trans with
	(Rabs (sum_f_R0 Vn n - x) + Rabs (- (sum_f_R0 Wn n - x0))).
  apply Rabs_triang.
  rewrite Rabs_Ropp; apply Rlt_le_trans with (eps / 2 + eps / 2).
  apply Rplus_lt_compat.
  unfold R_dist in H9; apply H9; unfold ge in |- *; apply le_trans with N;
    [ unfold N in |- *; apply le_max_l | assumption ].
  unfold R_dist in H10; apply H10; unfold ge in |- *; apply le_trans with N;
    [ unfold N in |- *; apply le_max_r | assumption ].
  right; symmetry  in |- *; apply double_var.
  symmetry  in |- *; apply tech11; intro; unfold Vn, Wn in |- *;
    unfold Rdiv in |- *; do 2 rewrite <- (Rmult_comm (/ 2));
      apply Rmult_eq_reg_l with 2.
  rewrite Rmult_minus_distr_l; repeat rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  ring.
  discrR.
  discrR.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  cut (forall n:nat, / 2 * Rabs (An n) <= Wn n <= 3 * / 2 * Rabs (An n)).
  intro; cut (forall n:nat, / Wn n <= 2 * / Rabs (An n)).
  intro; cut (forall n:nat, Wn (S n) / Wn n <= 3 * Rabs (An (S n) / An n)).
  intro; unfold Un_cv in |- *; intros; unfold Un_cv in H0; cut (0 < eps / 3).
  intro; elim (H0 (eps / 3) H8); intros.
  exists x; intros.
  assert (H11 := H9 n H10).
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite Rabs_Rabsolu; unfold R_dist in H11;
      unfold Rminus in H11; rewrite Ropp_0 in H11; rewrite Rplus_0_r in H11;
	rewrite Rabs_Rabsolu in H11; rewrite Rabs_right.
  apply Rle_lt_trans with (3 * Rabs (An (S n) / An n)).
  apply H6.
  apply Rmult_lt_reg_l with (/ 3).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ];
    rewrite Rmult_1_l; rewrite <- (Rmult_comm eps); unfold Rdiv in H11;
      exact H11.
  left; change (0 < Wn (S n) / Wn n) in |- *; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat.
  apply H2.
  apply Rinv_0_lt_compat; apply H2.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  intro; unfold Rdiv in |- *; rewrite Rabs_mult; rewrite <- Rmult_assoc;
    replace 3 with (2 * (3 * / 2));
      [ idtac | rewrite <- Rmult_assoc; apply Rinv_r_simpl_m; discrR ];
      apply Rle_trans with (Wn (S n) * 2 * / Rabs (An n)).
  rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply H2.
  apply H5.
  rewrite Rabs_Rinv.
  replace (Wn (S n) * 2 * / Rabs (An n)) with (2 * / Rabs (An n) * Wn (S n));
    [ idtac | ring ];
    replace (2 * (3 * / 2) * Rabs (An (S n)) * / Rabs (An n)) with
      (2 * / Rabs (An n) * (3 * / 2 * Rabs (An (S n)))); 
      [ idtac | ring ]; apply Rmult_le_compat_l.
  left; apply Rmult_lt_0_compat.
  prove_sup0.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; apply H.
  elim (H4 (S n)); intros; assumption.
  apply H.
  intro; apply Rmult_le_reg_l with (Wn n).
  apply H2.
  rewrite <- Rinv_r_sym.
  apply Rmult_le_reg_l with (Rabs (An n)).
  apply Rabs_pos_lt; apply H.
  rewrite Rmult_1_r;
    replace (Rabs (An n) * (Wn n * (2 * / Rabs (An n)))) with
      (2 * Wn n * (Rabs (An n) * / Rabs (An n))); [ idtac | ring ];
      rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rmult_le_reg_l with (/ 2).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; elim (H4 n); intros; assumption.
  discrR.
  apply Rabs_no_R0; apply H.
  red in |- *; intro; assert (H6 := H2 n); rewrite H5 in H6;
    elim (Rlt_irrefl _ H6).
  intro; split.
  unfold Wn in |- *; unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; prove_sup0.
  pattern (Rabs (An n)) at 1 in |- *; rewrite <- Rplus_0_r; rewrite double;
    unfold Rminus in |- *; rewrite Rplus_assoc; apply Rplus_le_compat_l.
  apply Rplus_le_reg_l with (An n).
  rewrite Rplus_0_r; rewrite (Rplus_comm (An n)); rewrite Rplus_assoc;
    rewrite Rplus_opp_l; rewrite Rplus_0_r; apply RRle_abs.
  unfold Wn in |- *; unfold Rdiv in |- *; repeat rewrite <- (Rmult_comm (/ 2));
    repeat rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; prove_sup0.
  unfold Rminus in |- *; rewrite double;
    replace (3 * Rabs (An n)) with (Rabs (An n) + Rabs (An n) + Rabs (An n));
      [ idtac | ring ]; repeat rewrite Rplus_assoc; repeat apply Rplus_le_compat_l.
  rewrite <- Rabs_Ropp; apply RRle_abs.
  cut (forall n:nat, / 2 * Rabs (An n) <= Vn n <= 3 * / 2 * Rabs (An n)).
  intro; cut (forall n:nat, / Vn n <= 2 * / Rabs (An n)).
  intro; cut (forall n:nat, Vn (S n) / Vn n <= 3 * Rabs (An (S n) / An n)).
  intro; unfold Un_cv in |- *; intros; unfold Un_cv in H1; cut (0 < eps / 3).
  intro; elim (H0 (eps / 3) H7); intros.
  exists x; intros.
  assert (H10 := H8 n H9).
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite Rabs_Rabsolu; unfold R_dist in H10;
      unfold Rminus in H10; rewrite Ropp_0 in H10; rewrite Rplus_0_r in H10;
	rewrite Rabs_Rabsolu in H10; rewrite Rabs_right.
  apply Rle_lt_trans with (3 * Rabs (An (S n) / An n)).
  apply H5.
  apply Rmult_lt_reg_l with (/ 3).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ];
    rewrite Rmult_1_l; rewrite <- (Rmult_comm eps); unfold Rdiv in H10;
      exact H10.
  left; change (0 < Vn (S n) / Vn n) in |- *; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat.
  apply H1.
  apply Rinv_0_lt_compat; apply H1.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  intro; unfold Rdiv in |- *; rewrite Rabs_mult; rewrite <- Rmult_assoc;
    replace 3 with (2 * (3 * / 2));
      [ idtac | rewrite <- Rmult_assoc; apply Rinv_r_simpl_m; discrR ];
      apply Rle_trans with (Vn (S n) * 2 * / Rabs (An n)).
  rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply H1.
  apply H4.
  rewrite Rabs_Rinv.
  replace (Vn (S n) * 2 * / Rabs (An n)) with (2 * / Rabs (An n) * Vn (S n));
    [ idtac | ring ];
    replace (2 * (3 * / 2) * Rabs (An (S n)) * / Rabs (An n)) with
      (2 * / Rabs (An n) * (3 * / 2 * Rabs (An (S n)))); 
      [ idtac | ring ]; apply Rmult_le_compat_l.
  left; apply Rmult_lt_0_compat.
  prove_sup0.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; apply H.
  elim (H3 (S n)); intros; assumption.
  apply H.
  intro; apply Rmult_le_reg_l with (Vn n).
  apply H1.
  rewrite <- Rinv_r_sym.
  apply Rmult_le_reg_l with (Rabs (An n)).
  apply Rabs_pos_lt; apply H.
  rewrite Rmult_1_r;
    replace (Rabs (An n) * (Vn n * (2 * / Rabs (An n)))) with
      (2 * Vn n * (Rabs (An n) * / Rabs (An n))); [ idtac | ring ];
      rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rmult_le_reg_l with (/ 2).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; elim (H3 n); intros; assumption.
  discrR.
  apply Rabs_no_R0; apply H.
  red in |- *; intro; assert (H5 := H1 n); rewrite H4 in H5;
    elim (Rlt_irrefl _ H5).
  intro; split.
  unfold Vn in |- *; unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; prove_sup0.
  pattern (Rabs (An n)) at 1 in |- *; rewrite <- Rplus_0_r; rewrite double;
    rewrite Rplus_assoc; apply Rplus_le_compat_l.
  apply Rplus_le_reg_l with (- An n); rewrite Rplus_0_r;
    rewrite <- (Rplus_comm (An n)); rewrite <- Rplus_assoc; 
      rewrite Rplus_opp_l; rewrite Rplus_0_l; rewrite <- Rabs_Ropp; 
	apply RRle_abs.
  unfold Vn in |- *; unfold Rdiv in |- *; repeat rewrite <- (Rmult_comm (/ 2));
    repeat rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; prove_sup0.
  unfold Rminus in |- *; rewrite double;
    replace (3 * Rabs (An n)) with (Rabs (An n) + Rabs (An n) + Rabs (An n));
      [ idtac | ring ]; repeat rewrite Rplus_assoc; repeat apply Rplus_le_compat_l;
	apply RRle_abs.
  intro; unfold Wn in |- *; unfold Rdiv in |- *; rewrite <- (Rmult_0_r (/ 2));
    rewrite <- (Rmult_comm (/ 2)); apply Rmult_lt_compat_l.
  apply Rinv_0_lt_compat; prove_sup0.
  apply Rplus_lt_reg_r with (An n); rewrite Rplus_0_r; unfold Rminus in |- *;
    rewrite (Rplus_comm (An n)); rewrite Rplus_assoc; 
      rewrite Rplus_opp_l; rewrite Rplus_0_r;
	apply Rle_lt_trans with (Rabs (An n)).
  apply RRle_abs.
  rewrite double; pattern (Rabs (An n)) at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_lt_compat_l; apply Rabs_pos_lt; apply H.
  intro; unfold Vn in |- *; unfold Rdiv in |- *; rewrite <- (Rmult_0_r (/ 2));
    rewrite <- (Rmult_comm (/ 2)); apply Rmult_lt_compat_l.
  apply Rinv_0_lt_compat; prove_sup0.
  apply Rplus_lt_reg_r with (- An n); rewrite Rplus_0_r; unfold Rminus in |- *;
    rewrite (Rplus_comm (- An n)); rewrite Rplus_assoc; 
      rewrite Rplus_opp_r; rewrite Rplus_0_r;
	apply Rle_lt_trans with (Rabs (An n)).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  rewrite double; pattern (Rabs (An n)) at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_lt_compat_l; apply Rabs_pos_lt; apply H.
Qed.

Lemma AlembertC3_step1 :
  forall (An:nat -> R) (x:R),
    x <> 0 ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    sigT (fun l:R => Pser An x l).
Proof.
  intros; set (Bn := fun i:nat => An i * x ^ i).
  cut (forall n:nat, Bn n <> 0).
  intro; cut (Un_cv (fun n:nat => Rabs (Bn (S n) / Bn n)) 0).
  intro; assert (H4 := Alembert_C2 Bn H2 H3).
  elim H4; intros.
  apply existT with x0; unfold Bn in p; apply tech12; assumption.
  unfold Un_cv in |- *; intros; unfold Un_cv in H1; cut (0 < eps / Rabs x).
  intro; elim (H1 (eps / Rabs x) H4); intros.
  exists x0; intros; unfold R_dist in |- *; unfold Rminus in |- *;
    rewrite Ropp_0; rewrite Rplus_0_r; rewrite Rabs_Rabsolu; 
      unfold Bn in |- *;
	replace (An (S n) * x ^ S n / (An n * x ^ n)) with (An (S n) / An n * x).
  rewrite Rabs_mult; apply Rmult_lt_reg_l with (/ Rabs x).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  rewrite <- (Rmult_comm (Rabs x)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite <- (Rmult_comm eps); unfold Rdiv in H5;
    replace (Rabs (An (S n) / An n)) with (R_dist (Rabs (An (S n) * / An n)) 0).
  apply H5; assumption.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite Rabs_Rabsolu; unfold Rdiv in |- *; 
      reflexivity.
  apply Rabs_no_R0; assumption.
  replace (S n) with (n + 1)%nat; [ idtac | ring ]; rewrite pow_add;
    unfold Rdiv in |- *; rewrite Rinv_mult_distr.
  replace (An (n + 1)%nat * (x ^ n * x ^ 1) * (/ An n * / x ^ n)) with
    (An (n + 1)%nat * x ^ 1 * / An n * (x ^ n * / x ^ n)); 
    [ idtac | ring ]; rewrite <- Rinv_r_sym.
  simpl in |- *; ring.
  apply pow_nonzero; assumption.
  apply H0.
  apply pow_nonzero; assumption.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption ].
  intro; unfold Bn in |- *; apply prod_neq_R0;
    [ apply H0 | apply pow_nonzero; assumption ].
Qed.

Lemma AlembertC3_step2 :
  forall (An:nat -> R) (x:R), x = 0 -> sigT (fun l:R => Pser An x l).
Proof.
  intros; apply existT with (An 0%nat).
  unfold Pser in |- *; unfold infinit_sum in |- *; intros; exists 0%nat; intros;
    replace (sum_f_R0 (fun n0:nat => An n0 * x ^ n0) n) with (An 0%nat).
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Rplus_opp_r;
    rewrite Rabs_R0; assumption.
  induction  n as [| n Hrecn].
  simpl in |- *; ring.
  rewrite tech5; rewrite Hrecn;
    [ rewrite H; simpl in |- *; ring | unfold ge in |- *; apply le_O_n ].
Qed.

(** An useful criterion of convergence for power series *)
Theorem Alembert_C3 :
  forall (An:nat -> R) (x:R),
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    sigT (fun l:R => Pser An x l).
Proof.
  intros; case (total_order_T x 0); intro.
  elim s; intro.
  cut (x <> 0).
  intro; apply AlembertC3_step1; assumption.
  red in |- *; intro; rewrite H1 in a; elim (Rlt_irrefl _ a).
  apply AlembertC3_step2; assumption.
  cut (x <> 0).
  intro; apply AlembertC3_step1; assumption.
  red in |- *; intro; rewrite H1 in r; elim (Rlt_irrefl _ r).
Qed.

Lemma Alembert_C4 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    (forall n:nat, 0 < An n) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l).
Proof.
  intros An k Hyp H H0.
  cut
    (sigT (fun l:R => is_lub (EUn (fun N:nat => sum_f_R0 An N)) l) ->
      sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l)).
  intro X; apply X.
  apply completeness.
  assert (H1 := tech13 _ _ Hyp H0).
  elim H1; intros.
  elim H2; intros.
  elim H4; intros.
  unfold bound in |- *; exists (sum_f_R0 An x0 + / (1 - x) * An (S x0)).
  unfold is_upper_bound in |- *; intros; unfold EUn in H6.
  elim H6; intros.
  rewrite H7.
  assert (H8 := lt_eq_lt_dec x2 x0).
  elim H8; intros.
  elim a; intro.
  replace (sum_f_R0 An x0) with
    (sum_f_R0 An x2 + sum_f_R0 (fun i:nat => An (S x2 + i)%nat) (x0 - S x2)).
  pattern (sum_f_R0 An x2) at 1 in |- *; rewrite <- Rplus_0_r.
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  left; apply Rplus_lt_0_compat.
  apply tech1.
  intros; apply H.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat; apply Rplus_lt_reg_r with x; rewrite Rplus_0_r;
    replace (x + (1 - x)) with 1; [ elim H3; intros; assumption | ring ].
  apply H.
  symmetry  in |- *; apply tech2; assumption.
  rewrite b; pattern (sum_f_R0 An x0) at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_le_compat_l.
  left; apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat; apply Rplus_lt_reg_r with x; rewrite Rplus_0_r;
    replace (x + (1 - x)) with 1; [ elim H3; intros; assumption | ring ].
  apply H.
  replace (sum_f_R0 An x2) with
    (sum_f_R0 An x0 + sum_f_R0 (fun i:nat => An (S x0 + i)%nat) (x2 - S x0)).
  apply Rplus_le_compat_l.
  cut
    (sum_f_R0 (fun i:nat => An (S x0 + i)%nat) (x2 - S x0) <=
      An (S x0) * sum_f_R0 (fun i:nat => x ^ i) (x2 - S x0)).
  intro;
    apply Rle_trans with (An (S x0) * sum_f_R0 (fun i:nat => x ^ i) (x2 - S x0)).
  assumption.
  rewrite <- (Rmult_comm (An (S x0))); apply Rmult_le_compat_l.
  left; apply H.
  rewrite tech3.
  unfold Rdiv in |- *; apply Rmult_le_reg_l with (1 - x).
  apply Rplus_lt_reg_r with x; rewrite Rplus_0_r.
  replace (x + (1 - x)) with 1; [ elim H3; intros; assumption | ring ].
  do 2 rewrite (Rmult_comm (1 - x)).
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; apply Rplus_le_reg_l with (x ^ S (x2 - S x0)).
  replace (x ^ S (x2 - S x0) + (1 - x ^ S (x2 - S x0))) with 1;
    [ idtac | ring ].
  rewrite <- (Rplus_comm 1); pattern 1 at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_le_compat_l.
  left; apply pow_lt.
  apply Rle_lt_trans with k.
  elim Hyp; intros; assumption.
  elim H3; intros; assumption.
  apply Rminus_eq_contra.
  red in |- *; intro.
  elim H3; intros.
  rewrite H10 in H12; elim (Rlt_irrefl _ H12).
  red in |- *; intro.
  elim H3; intros.
  rewrite H10 in H12; elim (Rlt_irrefl _ H12).
  replace (An (S x0)) with (An (S x0 + 0)%nat).
  apply (tech6 (fun i:nat => An (S x0 + i)%nat) x).
  left; apply Rle_lt_trans with k.
  elim Hyp; intros; assumption.
  elim H3; intros; assumption.
  intro.
  cut (forall n:nat, (n >= x0)%nat -> An (S n) < x * An n).
  intro.
  replace (S x0 + S i)%nat with (S (S x0 + i)).
  apply H9.
  unfold ge in |- *.
  apply tech8.
  apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR; do 2 rewrite S_INR;
    ring.
  intros.
  apply Rmult_lt_reg_l with (/ An n).
  apply Rinv_0_lt_compat; apply H.
  do 2 rewrite (Rmult_comm (/ An n)).
  rewrite Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  replace (An (S n) * / An n) with (Rabs (An (S n) / An n)).
  apply H5; assumption.
  rewrite Rabs_right.
  unfold Rdiv in |- *; reflexivity.
  left; unfold Rdiv in |- *; change (0 < An (S n) * / An n) in |- *;
    apply Rmult_lt_0_compat.
  apply H.
  apply Rinv_0_lt_compat; apply H.
  red in |- *; intro.
  assert (H11 := H n).
  rewrite H10 in H11; elim (Rlt_irrefl _ H11).
  replace (S x0 + 0)%nat with (S x0); [ reflexivity | ring ].
  symmetry  in |- *; apply tech2; assumption.
  exists (sum_f_R0 An 0); unfold EUn in |- *; exists 0%nat; reflexivity.
  intro X; elim X; intros.
  apply existT with x; apply tech10;
    [ unfold Un_growing in |- *; intro; rewrite tech5;
      pattern (sum_f_R0 An n) at 1 in |- *; rewrite <- Rplus_0_r;
	apply Rplus_le_compat_l; left; apply H
      | apply p ].
Qed.

Lemma Alembert_C5 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l).
Proof.
  intros.
  cut
    (sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l) ->
      sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 An N) l)).
  intro Hyp0; apply Hyp0.
  apply cv_cauchy_2.
  apply cauchy_abs.
  apply cv_cauchy_1.
  cut
    (sigT
      (fun l:R => Un_cv (fun N:nat => sum_f_R0 (fun i:nat => Rabs (An i)) N) l) ->
      sigT
      (fun l:R => Un_cv (fun N:nat => sum_f_R0 (fun i:nat => Rabs (An i)) N) l)).
  intro Hyp; apply Hyp.
  apply (Alembert_C4 (fun i:nat => Rabs (An i)) k).
  assumption.
  intro; apply Rabs_pos_lt; apply H0.
  unfold Un_cv in |- *.
  unfold Un_cv in H1.
  unfold Rdiv in |- *.
  intros.
  elim (H1 eps H2); intros.
  exists x; intros.
  rewrite <- Rabs_Rinv.
  rewrite <- Rabs_mult.
  rewrite Rabs_Rabsolu.
  unfold Rdiv in H3; apply H3; assumption.
  apply H0.
  intro X.
  elim X; intros.
  apply existT with x.
  assumption.
  intro X.
  elim X; intros.
  apply existT with x.
  assumption.
Qed.

(** Convergence of power series in D(O,1/k)
    k=0 is described in Alembert_C3     *)
Lemma Alembert_C6 :
  forall (An:nat -> R) (x k:R),
    0 < k ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    Rabs x < / k -> sigT (fun l:R => Pser An x l).
  intros.
  cut
    (sigT
      (fun l:R => Un_cv (fun N:nat => sum_f_R0 (fun i:nat => An i * x ^ i) N) l)).
  intro X.
  elim X; intros.
  apply existT with x0.
  apply tech12; assumption.
  case (total_order_T x 0); intro.
  elim s; intro.
  eapply Alembert_C5 with (k * Rabs x).
  split.
  unfold Rdiv in |- *; apply Rmult_le_pos.
  left; assumption.
  left; apply Rabs_pos_lt.
  red in |- *; intro; rewrite H3 in a; elim (Rlt_irrefl _ a).
  apply Rmult_lt_reg_l with (/ k).
  apply Rinv_0_lt_compat; assumption.
  rewrite <- Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  rewrite Rmult_1_r; assumption.
  red in |- *; intro; rewrite H3 in H; elim (Rlt_irrefl _ H).
  intro; apply prod_neq_R0.
  apply H0.
  apply pow_nonzero.
  red in |- *; intro; rewrite H3 in a; elim (Rlt_irrefl _ a).
  unfold Un_cv in |- *; unfold Un_cv in H1.
  intros.
  cut (0 < eps / Rabs x).
  intro.
  elim (H1 (eps / Rabs x) H4); intros.
  exists x0.
  intros.
  replace (An (S n) * x ^ S n / (An n * x ^ n)) with (An (S n) / An n * x).
  unfold R_dist in |- *.
  rewrite Rabs_mult.
  replace (Rabs (An (S n) / An n) * Rabs x - k * Rabs x) with
    (Rabs x * (Rabs (An (S n) / An n) - k)); [ idtac | ring ].
  rewrite Rabs_mult.
  rewrite Rabs_Rabsolu.
  apply Rmult_lt_reg_l with (/ Rabs x).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  red in |- *; intro; rewrite H7 in a; elim (Rlt_irrefl _ a).
  rewrite <- Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  rewrite <- (Rmult_comm eps).
  unfold R_dist in H5.
  unfold Rdiv in |- *; unfold Rdiv in H5; apply H5; assumption.
  apply Rabs_no_R0.
  red in |- *; intro; rewrite H7 in a; elim (Rlt_irrefl _ a).
  unfold Rdiv in |- *; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite pow_add.
  simpl in |- *.
  rewrite Rmult_1_r.
  rewrite Rinv_mult_distr.
  replace (An (n + 1)%nat * (x ^ n * x) * (/ An n * / x ^ n)) with
    (An (n + 1)%nat * / An n * x * (x ^ n * / x ^ n)); 
    [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; reflexivity.
  apply pow_nonzero.
  red in |- *; intro; rewrite H7 in a; elim (Rlt_irrefl _ a).
  apply H0.
  apply pow_nonzero.
  red in |- *; intro; rewrite H7 in a; elim (Rlt_irrefl _ a).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  red in |- *; intro H7; rewrite H7 in a; elim (Rlt_irrefl _ a).
  apply existT with (An 0%nat).
  unfold Un_cv in |- *.
  intros.
  exists 0%nat.
  intros.
  unfold R_dist in |- *.
  replace (sum_f_R0 (fun i:nat => An i * x ^ i) n) with (An 0%nat).
  unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  induction  n as [| n Hrecn].
  simpl in |- *; ring.
  rewrite tech5.
  rewrite <- Hrecn.
  rewrite b; simpl in |- *; ring.
  unfold ge in |- *; apply le_O_n.
  eapply Alembert_C5 with (k * Rabs x).
  split.
  unfold Rdiv in |- *; apply Rmult_le_pos.
  left; assumption.
  left; apply Rabs_pos_lt.
  red in |- *; intro; rewrite H3 in r; elim (Rlt_irrefl _ r).
  apply Rmult_lt_reg_l with (/ k).
  apply Rinv_0_lt_compat; assumption.
  rewrite <- Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  rewrite Rmult_1_r; assumption.
  red in |- *; intro; rewrite H3 in H; elim (Rlt_irrefl _ H).
  intro; apply prod_neq_R0.
  apply H0.
  apply pow_nonzero.
  red in |- *; intro; rewrite H3 in r; elim (Rlt_irrefl _ r).
  unfold Un_cv in |- *; unfold Un_cv in H1.
  intros.
  cut (0 < eps / Rabs x).
  intro.
  elim (H1 (eps / Rabs x) H4); intros.
  exists x0.
  intros.
  replace (An (S n) * x ^ S n / (An n * x ^ n)) with (An (S n) / An n * x).
  unfold R_dist in |- *.
  rewrite Rabs_mult.
  replace (Rabs (An (S n) / An n) * Rabs x - k * Rabs x) with
    (Rabs x * (Rabs (An (S n) / An n) - k)); [ idtac | ring ].
  rewrite Rabs_mult.
  rewrite Rabs_Rabsolu.
  apply Rmult_lt_reg_l with (/ Rabs x).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  red in |- *; intro; rewrite H7 in r; elim (Rlt_irrefl _ r).
  rewrite <- Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  rewrite <- (Rmult_comm eps).
  unfold R_dist in H5.
  unfold Rdiv in |- *; unfold Rdiv in H5; apply H5; assumption.
  apply Rabs_no_R0.
  red in |- *; intro; rewrite H7 in r; elim (Rlt_irrefl _ r).
  unfold Rdiv in |- *; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite pow_add.
  simpl in |- *.
  rewrite Rmult_1_r.
  rewrite Rinv_mult_distr.
  replace (An (n + 1)%nat * (x ^ n * x) * (/ An n * / x ^ n)) with
    (An (n + 1)%nat * / An n * x * (x ^ n * / x ^ n)); 
    [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; reflexivity.
  apply pow_nonzero.
  red in |- *; intro; rewrite H7 in r; elim (Rlt_irrefl _ r).
  apply H0.
  apply pow_nonzero.
  red in |- *; intro; rewrite H7 in r; elim (Rlt_irrefl _ r).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  red in |- *; intro H7; rewrite H7 in r; elim (Rlt_irrefl _ r).
Qed.
