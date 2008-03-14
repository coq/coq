(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(**********************************************************)
(** Complements for the reals.Integer and fractional part *)
(*                                                        *)
(**********************************************************)

Require Import Rbase.
Require Import Omega.
Open Local Scope R_scope.

(*********************************************************)
(** *    Fractional part                                 *)
(*********************************************************)

(**********)
Definition Int_part (r:R) : Z := (up r - 1)%Z.

(**********)
Definition frac_part (r:R) : R := r - IZR (Int_part r).

(**********)
Lemma tech_up : forall (r:R) (z:Z), r < IZR z -> IZR z <= r + 1 -> z = up r.
Proof.
  intros; generalize (archimed r); intro; elim H1; intros; clear H1;
    unfold Rgt in H2; unfold Rminus in H3;
      generalize (Rplus_le_compat_l r (IZR (up r) + - r) 1 H3); 
        intro; clear H3; rewrite (Rplus_comm (IZR (up r)) (- r)) in H1;
          rewrite <- (Rplus_assoc r (- r) (IZR (up r))) in H1;
            rewrite (Rplus_opp_r r) in H1; elim (Rplus_ne (IZR (up r))); 
              intros a b; rewrite b in H1; clear a b; apply (single_z_r_R1 r z (up r));
                auto with zarith real.
Qed.

(**********)
Lemma up_tech :
  forall (r:R) (z:Z), IZR z <= r -> r < IZR (z + 1) -> (z + 1)%Z = up r.
Proof.
  intros; generalize (Rplus_le_compat_l 1 (IZR z) r H); intro; clear H;
    rewrite (Rplus_comm 1 (IZR z)) in H1; rewrite (Rplus_comm 1 r) in H1;
      cut (1 = IZR 1); auto with zarith real.
  intro; generalize H1; pattern 1 at 1 in |- *; rewrite H; intro; clear H H1;
    rewrite <- (plus_IZR z 1) in H2; apply (tech_up r (z + 1));
      auto with zarith real.
Qed.

(**********)
Lemma fp_R0 : frac_part 0 = 0.
Proof.
  unfold frac_part in |- *; unfold Int_part in |- *; elim (archimed 0); intros;
    unfold Rminus in |- *; elim (Rplus_ne (- IZR (up 0 - 1))); 
      intros a b; rewrite b; clear a b; rewrite <- Z_R_minus; 
        cut (up 0 = 1%Z).
  intro; rewrite H1;
    rewrite (Rminus_diag_eq (IZR 1) (IZR 1) (refl_equal (IZR 1))); 
      apply Ropp_0. 
  elim (archimed 0); intros; clear H2; unfold Rgt in H1;
    rewrite (Rminus_0_r (IZR (up 0))) in H0; generalize (lt_O_IZR (up 0) H1);
      intro; clear H1; generalize (le_IZR_R1 (up 0) H0); 
        intro; clear H H0; omega.
Qed.

(**********)
Lemma for_base_fp : forall r:R, IZR (up r) - r > 0 /\ IZR (up r) - r <= 1.
Proof.
  intro; split; cut (IZR (up r) > r /\ IZR (up r) - r <= 1).
  intro; elim H; intros.
  apply (Rgt_minus (IZR (up r)) r H0).
  apply archimed.
  intro; elim H; intros.
  exact H1.
  apply archimed.
Qed.

(**********)
Lemma base_fp : forall r:R, frac_part r >= 0 /\ frac_part r < 1.
Proof.
  intro; unfold frac_part in |- *; unfold Int_part in |- *; split.
     (*sup a O*)
  cut (r - IZR (up r) >= -1).
  rewrite <- Z_R_minus; simpl in |- *; intro; unfold Rminus in |- *;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
      fold (r - IZR (up r)) in |- *; fold (r - IZR (up r) - -1) in |- *;
        apply Rge_minus; auto with zarith real.
  rewrite <- Ropp_minus_distr; apply Ropp_le_ge_contravar; elim (for_base_fp r);
    auto with zarith real.
    (*inf a 1*) 
  cut (r - IZR (up r) < 0).
  rewrite <- Z_R_minus; simpl in |- *; intro; unfold Rminus in |- *;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
      fold (r - IZR (up r)) in |- *; rewrite Ropp_involutive; 
        elim (Rplus_ne 1); intros a b; pattern 1 at 2 in |- *; 
          rewrite <- a; clear a b; rewrite (Rplus_comm (r - IZR (up r)) 1);
            apply Rplus_lt_compat_l; auto with zarith real.
  elim (for_base_fp r); intros; rewrite <- Ropp_0; rewrite <- Ropp_minus_distr;
    apply Ropp_gt_lt_contravar; auto with zarith real.
Qed.

(*********************************************************)
(** *    Properties                                      *)
(*********************************************************)

(**********)
Lemma base_Int_part :
  forall r:R, IZR (Int_part r) <= r /\ IZR (Int_part r) - r > -1. 
Proof.
  intro; unfold Int_part in |- *; elim (archimed r); intros.
  split; rewrite <- (Z_R_minus (up r) 1); simpl in |- *.
  generalize (Rle_minus (IZR (up r) - r) 1 H0); intro; unfold Rminus in H1;
    rewrite (Rplus_assoc (IZR (up r)) (- r) (-1)) in H1;
      rewrite (Rplus_comm (- r) (-1)) in H1;
        rewrite <- (Rplus_assoc (IZR (up r)) (-1) (- r)) in H1;
          fold (IZR (up r) - 1) in H1; fold (IZR (up r) - 1 - r) in H1;
            apply Rminus_le; auto with zarith real.
  generalize (Rplus_gt_compat_l (-1) (IZR (up r)) r H); intro;
    rewrite (Rplus_comm (-1) (IZR (up r))) in H1;
      generalize (Rplus_gt_compat_l (- r) (IZR (up r) + -1) (-1 + r) H1); 
        intro; clear H H0 H1; rewrite (Rplus_comm (- r) (IZR (up r) + -1)) in H2;
          fold (IZR (up r) - 1) in H2; fold (IZR (up r) - 1 - r) in H2;
            rewrite (Rplus_comm (- r) (-1 + r)) in H2;
              rewrite (Rplus_assoc (-1) r (- r)) in H2; rewrite (Rplus_opp_r r) in H2;
                elim (Rplus_ne (-1)); intros a b; rewrite a in H2; 
                  clear a b; auto with zarith real.  
Qed.

(**********)
Lemma Int_part_INR : forall n:nat, Int_part (INR n) = Z_of_nat n.
Proof.
  intros n; unfold Int_part in |- *.
  cut (up (INR n) = (Z_of_nat n + Z_of_nat 1)%Z).
  intros H'; rewrite H'; simpl in |- *; ring.
  apply sym_equal; apply tech_up; auto.
  replace (Z_of_nat n + Z_of_nat 1)%Z with (Z_of_nat (S n)).
  repeat rewrite <- INR_IZR_INZ.
  apply lt_INR; auto.
  rewrite Zplus_comm; rewrite <- Znat.inj_plus; simpl in |- *; auto.
  rewrite plus_IZR; simpl in |- *; auto with real.
  repeat rewrite <- INR_IZR_INZ; auto with real.
Qed.

(**********)
Lemma fp_nat : forall r:R, frac_part r = 0 ->  exists c : Z, r = IZR c.
Proof.
  unfold frac_part in |- *; intros; split with (Int_part r);
    apply Rminus_diag_uniq; auto with zarith real.
Qed.

(**********)
Lemma R0_fp_O : forall r:R, 0 <> frac_part r -> 0 <> r.
Proof.
  red in |- *; intros; rewrite <- H0 in H; generalize fp_R0; intro;
    auto with zarith real.
Qed.

(**********)
Lemma Rminus_Int_part1 :
  forall r1 r2:R,
    frac_part r1 >= frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z.
Proof.
  intros; elim (base_fp r1); elim (base_fp r2); intros;
    generalize (Rge_le (frac_part r2) 0 H0); intro; clear H0;
      generalize (Ropp_le_ge_contravar 0 (frac_part r2) H4); 
        intro; clear H4; rewrite Ropp_0 in H0;
          generalize (Rge_le 0 (- frac_part r2) H0); intro; 
            clear H0; generalize (Rge_le (frac_part r1) 0 H2); 
              intro; clear H2; generalize (Ropp_lt_gt_contravar (frac_part r2) 1 H1);
                intro; clear H1; unfold Rgt in H2;
                  generalize
                    (sum_inequa_Rle_lt 0 (frac_part r1) 1 (-1) (- frac_part r2) 0 H0 H3 H2 H4);
                    intro; elim H1; intros; clear H1; elim (Rplus_ne 1); 
                      intros a b; rewrite a in H6; clear a b H5;
                        generalize (Rge_minus (frac_part r1) (frac_part r2) H); 
                          intro; clear H; fold (frac_part r1 - frac_part r2) in H6;
                            generalize (Rge_le (frac_part r1 - frac_part r2) 0 H1); 
                              intro; clear H1 H3 H4 H0 H2; unfold frac_part in H6, H;
                                unfold Rminus in H6, H;
                                  rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H;
                                    rewrite (Ropp_involutive (IZR (Int_part r2))) in H;
                                      rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)))
                                        in H;
                                        rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)))
                                          in H; rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H;
                                            rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H;
                                              rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)))
                                                in H; rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H;
                                                  fold (r1 - r2) in H; fold (IZR (Int_part r2) - IZR (Int_part r1)) in H;
                                                    generalize
                                                      (Rplus_le_compat_l (IZR (Int_part r1) - IZR (Int_part r2)) 0
                                                        (r1 - r2 + (IZR (Int_part r2) - IZR (Int_part r1))) H); 
                                                      intro; clear H;
                                                        rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H0;
                                                          rewrite <-
                                                            (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2))
                                                              (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2))
                                                            in H0; unfold Rminus in H0; fold (r1 - r2) in H0;
                                                              rewrite
                                                                (Rplus_assoc (IZR (Int_part r1)) (- IZR (Int_part r2))
                                                                  (IZR (Int_part r2) + - IZR (Int_part r1))) in H0;
                                                                rewrite <-
                                                                  (Rplus_assoc (- IZR (Int_part r2)) (IZR (Int_part r2))
                                                                    (- IZR (Int_part r1))) in H0;
                                                                  rewrite (Rplus_opp_l (IZR (Int_part r2))) in H0;
                                                                    elim (Rplus_ne (- IZR (Int_part r1))); intros a b; 
                                                                      rewrite b in H0; clear a b;
                                                                        elim (Rplus_ne (IZR (Int_part r1) + - IZR (Int_part r2))); 
                                                                          intros a b; rewrite a in H0; clear a b;
                                                                            rewrite (Rplus_opp_r (IZR (Int_part r1))) in H0; elim (Rplus_ne (r1 - r2));
                                                                              intros a b; rewrite b in H0; clear a b;
                                                                                fold (IZR (Int_part r1) - IZR (Int_part r2)) in H0;
                                                                                  rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H6;
                                                                                    rewrite (Ropp_involutive (IZR (Int_part r2))) in H6;
                                                                                      rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)))
                                                                                        in H6;
                                                                                        rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)))
                                                                                          in H6; rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H6;
                                                                                            rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H6;
                                                                                              rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)))
                                                                                                in H6;
                                                                                                rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H6;
                                                                                                  fold (r1 - r2) in H6; fold (IZR (Int_part r2) - IZR (Int_part r1)) in H6;
                                                                                                    generalize
                                                                                                      (Rplus_lt_compat_l (IZR (Int_part r1) - IZR (Int_part r2))
                                                                                                        (r1 - r2 + (IZR (Int_part r2) - IZR (Int_part r1))) 1 H6); 
                                                                                                      intro; clear H6;
                                                                                                        rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H;
                                                                                                          rewrite <-
                                                                                                            (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2))
                                                                                                              (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2))
                                                                                                            in H;
                                                                                                            rewrite <- (Ropp_minus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
                                                                                                              rewrite (Rplus_opp_r (IZR (Int_part r1) - IZR (Int_part r2))) in H;
                                                                                                                elim (Rplus_ne (r1 - r2)); intros a b; rewrite b in H; 
                                                                                                                  clear a b; rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H0;
                                                                                                                    rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H; 
                                                                                                                      cut (1 = IZR 1); auto with zarith real.
  intro; rewrite H1 in H; clear H1;
    rewrite <- (plus_IZR (Int_part r1 - Int_part r2) 1) in H;
      generalize (up_tech (r1 - r2) (Int_part r1 - Int_part r2) H0 H); 
        intros; clear H H0; unfold Int_part at 1 in |- *; 
          omega.
Qed.

(**********)
Lemma Rminus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z.
Proof.
  intros; elim (base_fp r1); elim (base_fp r2); intros;
    generalize (Rge_le (frac_part r2) 0 H0); intro; clear H0;
      generalize (Ropp_le_ge_contravar 0 (frac_part r2) H4); 
        intro; clear H4; rewrite Ropp_0 in H0;
          generalize (Rge_le 0 (- frac_part r2) H0); intro; 
            clear H0; generalize (Rge_le (frac_part r1) 0 H2); 
              intro; clear H2; generalize (Ropp_lt_gt_contravar (frac_part r2) 1 H1);
                intro; clear H1; unfold Rgt in H2;
                  generalize
                    (sum_inequa_Rle_lt 0 (frac_part r1) 1 (-1) (- frac_part r2) 0 H0 H3 H2 H4);
                    intro; elim H1; intros; clear H1; elim (Rplus_ne (-1)); 
                      intros a b; rewrite b in H5; clear a b H6;
                        generalize (Rlt_minus (frac_part r1) (frac_part r2) H); 
                          intro; clear H; fold (frac_part r1 - frac_part r2) in H5; 
                            clear H3 H4 H0 H2; unfold frac_part in H5, H1; unfold Rminus in H5, H1;
                              rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H5;
                                rewrite (Ropp_involutive (IZR (Int_part r2))) in H5;
                                  rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)))
                                    in H5;
                                    rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)))
                                      in H5; rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H5;
                                        rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H5;
                                          rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)))
                                            in H5;
                                            rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H5;
                                              fold (r1 - r2) in H5; fold (IZR (Int_part r2) - IZR (Int_part r1)) in H5;
                                                generalize
                                                  (Rplus_lt_compat_l (IZR (Int_part r1) - IZR (Int_part r2)) (-1)
                                                    (r1 - r2 + (IZR (Int_part r2) - IZR (Int_part r1))) H5); 
                                                  intro; clear H5;
                                                    rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H;
                                                      rewrite <-
                                                        (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2))
                                                          (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2))
                                                        in H; unfold Rminus in H; fold (r1 - r2) in H;
                                                          rewrite
                                                            (Rplus_assoc (IZR (Int_part r1)) (- IZR (Int_part r2))
                                                              (IZR (Int_part r2) + - IZR (Int_part r1))) in H;
                                                            rewrite <-
                                                              (Rplus_assoc (- IZR (Int_part r2)) (IZR (Int_part r2))
                                                                (- IZR (Int_part r1))) in H;
                                                              rewrite (Rplus_opp_l (IZR (Int_part r2))) in H;
                                                                elim (Rplus_ne (- IZR (Int_part r1))); intros a b; 
                                                                  rewrite b in H; clear a b; rewrite (Rplus_opp_r (IZR (Int_part r1))) in H;
                                                                    elim (Rplus_ne (r1 - r2)); intros a b; rewrite b in H; 
                                                                      clear a b; fold (IZR (Int_part r1) - IZR (Int_part r2)) in H;
                                                                        fold (IZR (Int_part r1) - IZR (Int_part r2) - 1) in H;
                                                                          rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H1;
                                                                            rewrite (Ropp_involutive (IZR (Int_part r2))) in H1;
                                                                              rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)))
                                                                                in H1;
                                                                                rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)))
                                                                                  in H1; rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H1;
                                                                                    rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                                                                                      rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)))
                                                                                        in H1;
                                                                                        rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                                                                                          fold (r1 - r2) in H1; fold (IZR (Int_part r2) - IZR (Int_part r1)) in H1;
                                                                                            generalize
                                                                                              (Rplus_lt_compat_l (IZR (Int_part r1) - IZR (Int_part r2))
                                                                                                (r1 - r2 + (IZR (Int_part r2) - IZR (Int_part r1))) 0 H1); 
                                                                                              intro; clear H1;
                                                                                                rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H0;
                                                                                                  rewrite <-
                                                                                                    (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2))
                                                                                                      (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2))
                                                                                                    in H0;
                                                                                                    rewrite <- (Ropp_minus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
                                                                                                      rewrite (Rplus_opp_r (IZR (Int_part r1) - IZR (Int_part r2))) in H0;
                                                                                                        elim (Rplus_ne (r1 - r2)); intros a b; rewrite b in H0; 
                                                                                                          clear a b; rewrite <- (Rplus_opp_l 1) in H0;
                                                                                                            rewrite <- (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2)) (-1) 1)
                                                                                                              in H0; fold (IZR (Int_part r1) - IZR (Int_part r2) - 1) in H0;
                                                                                                                rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H0;
                                                                                                                  rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H; 
                                                                                                                    cut (1 = IZR 1); auto with zarith real.
  intro; rewrite H1 in H; rewrite H1 in H0; clear H1;
    rewrite (Z_R_minus (Int_part r1 - Int_part r2) 1) in H;
      rewrite (Z_R_minus (Int_part r1 - Int_part r2) 1) in H0;
        rewrite <- (plus_IZR (Int_part r1 - Int_part r2 - 1) 1) in H0;
          generalize (Rlt_le (IZR (Int_part r1 - Int_part r2 - 1)) (r1 - r2) H); 
            intro; clear H;
              generalize (up_tech (r1 - r2) (Int_part r1 - Int_part r2 - 1) H1 H0); 
                intros; clear H0 H1; unfold Int_part at 1 in |- *; 
                  omega.
Qed.

(**********)
Lemma Rminus_fp1 :
  forall r1 r2:R,
    frac_part r1 >= frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2.
Proof.
  intros; unfold frac_part in |- *; generalize (Rminus_Int_part1 r1 r2 H);
    intro; rewrite H0; rewrite <- (Z_R_minus (Int_part r1) (Int_part r2));
      unfold Rminus in |- *;
        rewrite (Ropp_plus_distr (IZR (Int_part r1)) (- IZR (Int_part r2)));
          rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2)));
            rewrite (Ropp_involutive (IZR (Int_part r2)));
              rewrite (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)));
                rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)));
                  rewrite <- (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2)));
                    rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)));
                      rewrite (Rplus_comm (- r2) (- IZR (Int_part r1))); 
                        auto with zarith real.
Qed.

(**********)
Lemma Rminus_fp2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2 + 1.
Proof.
  intros; unfold frac_part in |- *; generalize (Rminus_Int_part2 r1 r2 H);
    intro; rewrite H0; rewrite <- (Z_R_minus (Int_part r1 - Int_part r2) 1);
      rewrite <- (Z_R_minus (Int_part r1) (Int_part r2)); 
        unfold Rminus in |- *;
          rewrite
            (Ropp_plus_distr (IZR (Int_part r1) + - IZR (Int_part r2)) (- IZR 1))
            ; rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2)));
              rewrite (Ropp_involutive (IZR 1));
                rewrite (Ropp_involutive (IZR (Int_part r2)));
                  rewrite (Ropp_plus_distr (IZR (Int_part r1)));
                    rewrite (Ropp_involutive (IZR (Int_part r2))); simpl in |- *;
                      rewrite <-
                        (Rplus_assoc (r1 + - r2) (- IZR (Int_part r1) + IZR (Int_part r2)) 1)
                        ; rewrite (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)));
                          rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)));
                            rewrite <- (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2)));
                              rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)));
                                rewrite (Rplus_comm (- r2) (- IZR (Int_part r1))); 
                                  auto with zarith real.
Qed.

(**********)
Lemma plus_Int_part1 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 >= 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2 + 1)%Z.
Proof.
  intros; generalize (Rge_le (frac_part r1 + frac_part r2) 1 H); intro; clear H;
    elim (base_fp r1); elim (base_fp r2); intros; clear H H2;
      generalize (Rplus_lt_compat_l (frac_part r2) (frac_part r1) 1 H3); 
        intro; clear H3; generalize (Rplus_lt_compat_l 1 (frac_part r2) 1 H1); 
          intro; clear H1; rewrite (Rplus_comm 1 (frac_part r2)) in H2;
            generalize
              (Rlt_trans (frac_part r2 + frac_part r1) (frac_part r2 + 1) 2 H H2); 
              intro; clear H H2; rewrite (Rplus_comm (frac_part r2) (frac_part r1)) in H1;
                unfold frac_part in H0, H1; unfold Rminus in H0, H1;
                  rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                    in H1; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H1;
                      rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                        in H1;
                        rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H1;
                          rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                            in H1;
                            rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                              rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                                in H0; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H0;
                                  rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                                    in H0;
                                    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H0;
                                      rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                                        in H0;
                                        rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
                                          generalize
                                            (Rplus_le_compat_l (IZR (Int_part r1) + IZR (Int_part r2)) 1
                                              (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) H0); 
                                            intro; clear H0;
                                              generalize
                                                (Rplus_lt_compat_l (IZR (Int_part r1) + IZR (Int_part r2))
                                                  (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) 2 H1); 
                                                intro; clear H1;
                                                  rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                    in H;
                                                    rewrite <-
                                                      (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                        (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                      in H; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H;
                                                        elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H; 
                                                          clear a b;
                                                            rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                              in H0;
                                                              rewrite <-
                                                                (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                                  (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                                in H0; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H0;
                                                                  elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H0; 
                                                                    clear a b;
                                                                      rewrite <- (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2)) 1 1) in H0;
                                                                        cut (1 = IZR 1); auto with zarith real.
  intro; rewrite H1 in H0; rewrite H1 in H; clear H1;
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H;
      rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
        rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H;
          rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H0;
            rewrite <- (plus_IZR (Int_part r1 + Int_part r2 + 1) 1) in H0;
              generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2 + 1) H H0); 
                intro; clear H H0; unfold Int_part at 1 in |- *; omega.
Qed.

(**********)
Lemma plus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2)%Z.
Proof.
  intros; elim (base_fp r1); elim (base_fp r2); intros; clear H1 H3;
    generalize (Rge_le (frac_part r2) 0 H0); intro; clear H0;
      generalize (Rge_le (frac_part r1) 0 H2); intro; clear H2;
        generalize (Rplus_le_compat_l (frac_part r1) 0 (frac_part r2) H1); 
          intro; clear H1; elim (Rplus_ne (frac_part r1)); intros a b; 
            rewrite a in H2; clear a b;
              generalize (Rle_trans 0 (frac_part r1) (frac_part r1 + frac_part r2) H0 H2);
                intro; clear H0 H2; unfold frac_part in H, H1; unfold Rminus in H, H1;
                  rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                    in H1; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H1;
                      rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                        in H1;
                        rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H1;
                          rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                            in H1;
                            rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                              rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                                in H; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H;
                                  rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2) in H;
                                    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H;
                                      rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                                        in H;
                                        rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
                                          generalize
                                            (Rplus_le_compat_l (IZR (Int_part r1) + IZR (Int_part r2)) 0
                                              (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) H1); 
                                            intro; clear H1;
                                              generalize
                                                (Rplus_lt_compat_l (IZR (Int_part r1) + IZR (Int_part r2))
                                                  (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) 1 H); 
                                                intro; clear H;
                                                  rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                    in H1;
                                                    rewrite <-
                                                      (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                        (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                      in H1; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H1;
                                                        elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H1; 
                                                          clear a b;
                                                            rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                              in H0;
                                                              rewrite <-
                                                                (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                                  (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                                in H0; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H0;
                                                                  elim (Rplus_ne (IZR (Int_part r1) + IZR (Int_part r2))); 
                                                                    intros a b; rewrite a in H0; clear a b; elim (Rplus_ne (r1 + r2));
                                                                      intros a b; rewrite b in H0; clear a b; cut (1 = IZR 1);
                                                                        auto with zarith real.
  intro; rewrite H in H1; clear H;
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
      rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H1;
        rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H1;
          generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2) H0 H1); 
            intro; clear H0 H1; unfold Int_part at 1 in |- *; 
              omega.
Qed.

(**********)
Lemma plus_frac_part1 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 >= 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - 1.
Proof.
  intros; unfold frac_part in |- *; generalize (plus_Int_part1 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1 + Int_part r2) 1);
      rewrite (plus_IZR (Int_part r1) (Int_part r2)); simpl in |- *;
        unfold Rminus at 3 4 in |- *;
          rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
            rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
              rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
                rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
                  rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
                    rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
                      unfold Rminus in |- *;
                        rewrite
                          (Rplus_assoc (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))) (-1))
                          ; rewrite <- (Ropp_plus_distr (IZR (Int_part r1) + IZR (Int_part r2)) 1);
                            trivial with zarith real.
Qed.

(**********)
Lemma plus_frac_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof.
  intros; unfold frac_part in |- *; generalize (plus_Int_part2 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1) (Int_part r2));
      unfold Rminus at 2 3 in |- *;
        rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
          rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
            rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
              rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
                rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
                  rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
                    unfold Rminus in |- *; trivial with zarith real.
Qed.
