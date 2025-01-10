(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************************************)
(** Complements for the reals.Integer and fractional part *)
(*                                                        *)
(**********************************************************)

Require Import Rdefinitions Raxioms RIneq.
Require Import ZArith.
Local Open Scope R_scope.

(*********************************************************)
(** *    Fractional part                                 *)
(*********************************************************)

(**********)
Definition Int_part (r:R) : Z := (up r - 1)%Z.

(**********)
Definition frac_part (r:R) : R := r - IZR (Int_part r).

(**********)
(* TODO: rename this, this is not a technical lemma but the specification of up. *)
Lemma tech_up : forall (r:R) (z:Z), r < IZR z -> IZR z <= r + 1 -> z = up r.
Proof.
  intros r z Hlt Hle.
  destruct (archimed r) as [Hlt'%Ropp_lt_contravar Hle'%Ropp_le_contravar].
  apply (Rplus_le_compat_l (- r)) in Hle'.
  rewrite Ropp_minus_distr, Rminus_def, <-Rplus_assoc, Rplus_opp_l, Rplus_0_l in Hle'.
  apply Z.sub_move_0_r, one_IZR_lt1; split; rewrite minus_IZR.
  - replace (-1) with (r + (- r + - 1))
      by (now rewrite <-Rplus_assoc, Rplus_opp_r, Rplus_0_l).
    now apply Rplus_lt_le_compat.
  - replace 1 with (r + 1 + -r)
      by (now rewrite (Rplus_comm r), Rplus_assoc, Rplus_opp_r, Rplus_0_r).
    now apply Rplus_le_lt_compat.
Qed.

Lemma Int_part_spec : forall r z, r - 1 < IZR z <= r -> z = Int_part r.
Proof.
  unfold Int_part; intros r z [Hle Hlt]; apply Z.add_move_r, tech_up.
  - rewrite <-(Rplus_0_r r), <-(Rplus_opp_l 1), <-Rplus_assoc, plus_IZR.
    now apply Rplus_lt_compat_r.
  - now rewrite plus_IZR; apply Rplus_le_compat_r.
Qed.

(**********)
Lemma up_tech :
  forall (r:R) (z:Z), IZR z <= r -> r < IZR (z + 1) -> (z + 1)%Z = up r.
Proof.
  intros.
  apply tech_up with (1 := H0).
  rewrite plus_IZR.
  now apply Rplus_le_compat_r.
Qed.

(**********)
Lemma fp_R0 : frac_part 0 = 0.
Proof.
  unfold frac_part, Int_part.
  replace (up 0) with 1%Z.
  - now rewrite <- minus_IZR.
  - destruct (archimed 0) as [H1 H2].
    apply lt_IZR in H1.
    rewrite <- minus_IZR in H2.
    apply le_IZR in H2.
    Lia.lia.
Qed.

(**********)
Lemma for_base_fp : forall r:R, IZR (up r) - r > 0 /\ IZR (up r) - r <= 1.
Proof.
  intro; split; cut (IZR (up r) > r /\ IZR (up r) - r <= 1).
  - intro; elim H; intros.
    apply (Rgt_minus (IZR (up r)) r H0).
  - apply archimed.
  - intro; elim H; intros.
    exact H1.
  - apply archimed.
Qed.

(**********)
Lemma base_fp : forall r:R, frac_part r >= 0 /\ frac_part r < 1.
Proof.
  intro; unfold frac_part; unfold Int_part; split.
  - (*sup a O*)
    cut (r - IZR (up r) >= -1).
    + rewrite <- Z_R_minus; simpl; intro; unfold Rminus;
        rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
        fold (r - IZR (up r)); fold (r - IZR (up r) - -1);
        apply Rge_minus; auto with zarith real.
    + rewrite <- Ropp_minus_distr; apply Ropp_le_ge_contravar; elim (for_base_fp r);
        auto with zarith real.
  - (*inf a 1*)
    cut (r - IZR (up r) < 0).
    + rewrite <- Z_R_minus; simpl; intro; unfold Rminus;
        rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
        fold (r - IZR (up r)); rewrite Ropp_involutive;
        elim (Rplus_ne 1); intros a b; pattern 1 at 2;
        rewrite <- a; clear a b; rewrite (Rplus_comm (r - IZR (up r)) 1);
        apply Rplus_lt_compat_l; auto with zarith real.
    + elim (for_base_fp r); intros; rewrite <- Ropp_0; rewrite <- Ropp_minus_distr;
        apply Ropp_gt_lt_contravar; auto with zarith real.
Qed.

(*********************************************************)
(** *    Properties                                      *)
(*********************************************************)

(**********)
Lemma base_Int_part :
  forall r:R, IZR (Int_part r) <= r /\ IZR (Int_part r) - r > -1.
Proof.
  intro; unfold Int_part; elim (archimed r); intros.
  split; rewrite <- (Z_R_minus (up r) 1); simpl.
  - apply Rminus_le.
    replace (IZR (up r) - 1 - r) with (IZR (up r) - r - 1) by ring.
    now apply Rle_minus.
  - apply Rminus_gt.
    replace (IZR (up r) - 1 - r - -1) with (IZR (up r) - r) by ring.
    now apply Rgt_minus.
Qed.

(**********)
Lemma Int_part_INR : forall n:nat, Int_part (INR n) = Z.of_nat n.
Proof.
  intros n; unfold Int_part.
  cut (up (INR n) = (Z.of_nat n + Z.of_nat 1)%Z).
  - intros H'; rewrite H'; simpl; ring.
  - symmetry; apply tech_up; auto.
    + replace (Z.of_nat n + Z.of_nat 1)%Z with (Z.of_nat (S n)).
      * repeat rewrite <- INR_IZR_INZ.
        apply lt_INR; auto.
      * rewrite Z.add_comm; rewrite <- Znat.Nat2Z.inj_add; simpl; auto.
    + rewrite plus_IZR; simpl; auto with real.
      repeat rewrite <- INR_IZR_INZ; auto with real.
Qed.

(**********)
Lemma fp_nat : forall r:R, frac_part r = 0 ->  exists c : Z, r = IZR c.
Proof.
  unfold frac_part; intros; split with (Int_part r);
    apply Rminus_diag_uniq; auto with zarith real.
Qed.

(**********)
Lemma R0_fp_O : forall r:R, 0 <> frac_part r -> 0 <> r.
Proof.
  red; intros; rewrite <- H0 in H; generalize fp_R0; intro;
    auto with zarith real.
Qed.

Lemma Rplus_Int_part_frac_part : forall r, r = IZR (Int_part r) + frac_part r.
Proof. now unfold frac_part; intros r; rewrite Rplus_minus. Qed.

Lemma Int_part_frac_part_spec :
  forall r z f, 0 <= f < 1 -> r = (IZR z) + f -> z = Int_part r /\ f = frac_part r.
Proof.
  intros r z f [Hlef Hltf] E%(Rminus_eq_compat_r f); rewrite Rplus_minus_r in E.
  assert (IP : z = Int_part r). {
    apply Int_part_spec; split.
    - now rewrite <-E; apply Rplus_lt_compat_l, Ropp_lt_contravar.
    - rewrite <-E; apply (Rplus_le_reg_r f).
      rewrite <-Rplus_minus_swap, Rplus_minus_r, <-(Rplus_0_r r) at 1.
      now apply Rplus_le_compat_l.
  }
  split; try easy.
  unfold frac_part.
  now rewrite <-IP, <-E, Rminus_def, Ropp_minus_distr, Rplus_minus.
Qed.
(**********)
Lemma Rminus_Int_part1 :
  forall r1 r2:R,
    frac_part r1 >= frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z.
Proof.
  intros r1 r2 H; symmetry.
  apply (Int_part_frac_part_spec _ _ (frac_part r1 - frac_part r2)).
  - split.
    + apply (Rplus_le_reg_r (frac_part r2)).
      rewrite Rplus_0_l, <-Rplus_minus_swap, Rplus_minus_r.
      now apply Rge_le.
    + rewrite <-(Rminus_0_r 1); apply Rplus_lt_le_compat.
      * now apply base_fp.
      * now apply Ropp_le_contravar, Rge_le, base_fp.
  - rewrite (Rplus_Int_part_frac_part r1) at 1.
    rewrite (Rplus_Int_part_frac_part r2) at 1.
    rewrite minus_IZR, Rplus_minus_swap, Rminus_def at 1.
    rewrite Ropp_plus_distr, !Rplus_assoc, (Rplus_comm _ (frac_part r1)).
    now unfold Rminus; rewrite !Rplus_assoc.
Qed.

(**********)
Lemma Rminus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z.
Proof.
  intros r1 r2 H; symmetry.
  apply (Int_part_frac_part_spec _ _ (frac_part r1 - frac_part r2 + 1)).
  - split.
    + apply (Rplus_le_reg_r (- 1)).
      rewrite !Rplus_assoc, Rplus_opp_r, Rplus_0_r.
      apply Rplus_le_compat.
      * now apply Rge_le, base_fp.
      * apply Ropp_le_contravar; left; apply base_fp.
    + rewrite <-(Rplus_0_l 1) at 2.
      now apply Rplus_lt_compat_r, Rlt_minus_0.
  - rewrite (Rplus_Int_part_frac_part r1) at 1.
    rewrite (Rplus_Int_part_frac_part r2) at 1.
    rewrite !minus_IZR, Rplus_minus_swap, Rminus_def at 1.
    rewrite Ropp_plus_distr, !Rplus_assoc, (Rplus_comm _ (frac_part r1)).
    unfold Rminus. rewrite (Rplus_assoc _ (- 1)), (Rplus_comm (- 1)).
    now rewrite !Rplus_assoc, Rplus_opp_r, Rplus_0_r.
Qed.

(**********)
Lemma Rminus_fp1 :
  forall r1 r2:R,
    frac_part r1 >= frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2.
Proof.
  intros r1 r2 H%Rminus_Int_part1; unfold frac_part.
  rewrite H, minus_IZR; unfold Rminus; rewrite !Ropp_plus_distr, Ropp_involutive.
  rewrite (Rplus_assoc r1), <-(Rplus_assoc (- r2)), (Rplus_comm (- r2)).
  now rewrite !Rplus_assoc.
Qed.

(**********)
Lemma Rminus_fp2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2 + 1.
Proof.
  intros r1 r2 H%Rminus_Int_part2; unfold frac_part.
  rewrite H, !minus_IZR; unfold Rminus; rewrite !Ropp_plus_distr, !Ropp_involutive.
  rewrite (Rplus_assoc r1), <-!(Rplus_assoc (- r2)), (Rplus_comm (- r2)).
  now rewrite !Rplus_assoc.
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
    change 2 with (1 + 1) in H0;
    rewrite <- (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2)) 1 1) in H0;
    auto with real.
  rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H;
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
    rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H;
    rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H0;
    rewrite <- (plus_IZR (Int_part r1 + Int_part r2 + 1) 1) in H0;
    generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2 + 1) H H0);
    intro; clear H H0; unfold Int_part at 1.
  Lia.lia.
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
    intros a b; rewrite b in H0; clear a b.
  rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H1;
    rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H1;
    generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2) H0 H1);
    intro; clear H0 H1; unfold Int_part at 1.
  Lia.lia.
Qed.

(**********)
Lemma plus_frac_part1 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 >= 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - 1.
Proof.
  intros; unfold frac_part; generalize (plus_Int_part1 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1 + Int_part r2) 1);
    rewrite (plus_IZR (Int_part r1) (Int_part r2)); simpl;
    unfold Rminus at 3 4;
    rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
    rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
    rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
    rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
    rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
    unfold Rminus;
    rewrite
      (Rplus_assoc (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))) (-(1)))
  ; rewrite <- (Ropp_plus_distr (IZR (Int_part r1) + IZR (Int_part r2)) 1);
    trivial with real.
Qed.

(**********)
Lemma plus_frac_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof.
  intros; unfold frac_part; generalize (plus_Int_part2 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1) (Int_part r2));
    unfold Rminus at 2 3;
    rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
    rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
    rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
    rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
    rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
    unfold Rminus; trivial with zarith real.
Qed.
