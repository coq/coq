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
Require Import SeqSeries.
Require Import Rtrigo1.
Require Import R_sqrt.
Local Open Scope R_scope.

(** * Distance *)

Definition dist_euc (x0 y0 x1 y1:R) : R :=
  sqrt (Rsqr (x0 - x1) + Rsqr (y0 - y1)).

Lemma distance_refl : forall x0 y0:R, dist_euc x0 y0 x0 y0 = 0.
Proof.
  intros x0 y0; unfold dist_euc; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat;
      [ apply Rle_0_sqr | apply Rle_0_sqr ]
      | right; reflexivity
      | rewrite Rsqr_0; rewrite Rsqr_sqrt;
        [ unfold Rsqr; ring
          | apply Rplus_le_le_0_compat; [ apply Rle_0_sqr | apply Rle_0_sqr ] ] ].
Qed.

Lemma distance_symm :
  forall x0 y0 x1 y1:R, dist_euc x0 y0 x1 y1 = dist_euc x1 y1 x0 y0.
Proof.
  intros x0 y0 x1 y1; unfold dist_euc; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat
      | apply sqrt_positivity; apply Rplus_le_le_0_compat
      | repeat rewrite Rsqr_sqrt;
        [ unfold Rsqr; ring
          | apply Rplus_le_le_0_compat
          | apply Rplus_le_le_0_compat ] ]; apply Rle_0_sqr.
Qed.

Lemma law_cosines :
  forall x0 y0 x1 y1 x2 y2 ac:R,
    let a := dist_euc x1 y1 x0 y0 in
      let b := dist_euc x2 y2 x0 y0 in
        let c := dist_euc x2 y2 x1 y1 in
          a * c * cos ac = (x0 - x1) * (x2 - x1) + (y0 - y1) * (y2 - y1) ->
          Rsqr b = Rsqr c + Rsqr a - 2 * (a * c * cos ac).
Proof.
  unfold dist_euc; intros; repeat rewrite Rsqr_sqrt;
    [ rewrite H; unfold Rsqr; ring
      | apply Rplus_le_le_0_compat
      | apply Rplus_le_le_0_compat
      | apply Rplus_le_le_0_compat ]; apply Rle_0_sqr.
Qed.

Lemma triangle :
  forall x0 y0 x1 y1 x2 y2:R,
    dist_euc x0 y0 x1 y1 <= dist_euc x0 y0 x2 y2 + dist_euc x2 y2 x1 y1.
Proof.
  intros; unfold dist_euc; apply Rsqr_incr_0;
    [ rewrite Rsqr_plus; repeat rewrite Rsqr_sqrt;
      [ replace (Rsqr (x0 - x1)) with
        (Rsqr (x0 - x2) + Rsqr (x2 - x1) + 2 * (x0 - x2) * (x2 - x1));
        [ replace (Rsqr (y0 - y1)) with
          (Rsqr (y0 - y2) + Rsqr (y2 - y1) + 2 * (y0 - y2) * (y2 - y1));
          [ apply Rplus_le_reg_l with
            (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
              Rsqr (y2 - y1));
            replace
            (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
              Rsqr (y2 - y1) +
              (Rsqr (x0 - x2) + Rsqr (x2 - x1) + 2 * (x0 - x2) * (x2 - x1) +
                (Rsqr (y0 - y2) + Rsqr (y2 - y1) + 2 * (y0 - y2) * (y2 - y1))))
            with (2 * ((x0 - x2) * (x2 - x1) + (y0 - y2) * (y2 - y1)));
              [ replace
                (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
                  Rsqr (y2 - y1) +
                  (Rsqr (x0 - x2) + Rsqr (y0 - y2) +
                    (Rsqr (x2 - x1) + Rsqr (y2 - y1)) +
                    2 * sqrt (Rsqr (x0 - x2) + Rsqr (y0 - y2)) *
                    sqrt (Rsqr (x2 - x1) + Rsqr (y2 - y1)))) with
                (2 *
                  (sqrt (Rsqr (x0 - x2) + Rsqr (y0 - y2)) *
                    sqrt (Rsqr (x2 - x1) + Rsqr (y2 - y1))));
                [ apply Rmult_le_compat_l;
                  [ left; cut (0%nat <> 2%nat);
                    [ intros; generalize (lt_INR_0 2 (neq_O_lt 2 H));
                      intro H0; assumption
                      | discriminate ]
                    | apply sqrt_cauchy ]
                  | ring ]
                | ring ]
            | ring_Rsqr ]
          | ring_Rsqr ]
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr ]
      | apply sqrt_positivity; apply Rplus_le_le_0_compat; apply Rle_0_sqr
      | apply Rplus_le_le_0_compat; apply sqrt_positivity;
        apply Rplus_le_le_0_compat; apply Rle_0_sqr ].
Qed.

(******************************************************************)
(** *                       Translation                           *)
(******************************************************************)

Definition xt (x tx:R) : R := x + tx.
Definition yt (y ty:R) : R := y + ty.

Lemma translation_0 : forall x y:R, xt x 0 = x /\ yt y 0 = y.
Proof.
  intros x y; split; [ unfold xt | unfold yt ]; ring.
Qed.

Lemma isometric_translation :
  forall x1 x2 y1 y2 tx ty:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt x1 tx - xt x2 tx) + Rsqr (yt y1 ty - yt y2 ty).
Proof.
  intros; unfold Rsqr, xt, yt; ring.
Qed.

(******************************************************************)
(** *                         Rotation                            *)
(******************************************************************)

Definition xr (x y theta:R) : R := x * cos theta + y * sin theta.
Definition yr (x y theta:R) : R := - x * sin theta + y * cos theta.

Lemma rotation_0 : forall x y:R, xr x y 0 = x /\ yr x y 0 = y.
Proof.
  intros x y; unfold xr, yr; split; rewrite cos_0; rewrite sin_0; ring.
Qed.

Lemma rotation_PI2 :
  forall x y:R, xr x y (PI / 2) = y /\ yr x y (PI / 2) = - x.
Proof.
  intros x y; unfold xr, yr; split; rewrite cos_PI2; rewrite sin_PI2;
    ring.
Qed.

Lemma isometric_rotation_0 :
  forall x1 y1 x2 y2 theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr x1 y1 theta - xr x2 y2 theta) +
    Rsqr (yr x1 y1 theta - yr x2 y2 theta).
Proof.
  intros; unfold xr, yr;
    replace
    (x1 * cos theta + y1 * sin theta - (x2 * cos theta + y2 * sin theta)) with
    (cos theta * (x1 - x2) + sin theta * (y1 - y2));
    [ replace
      (- x1 * sin theta + y1 * cos theta - (- x2 * sin theta + y2 * cos theta))
      with (cos theta * (y1 - y2) + sin theta * (x2 - x1));
        [ repeat rewrite Rsqr_plus; repeat rewrite Rsqr_mult; repeat rewrite cos2;
          ring_simplify; replace (x2 - x1) with (- (x1 - x2));
          [ rewrite <- Rsqr_neg; ring | ring ]
          | ring ]
      | ring ].
Qed.

Lemma isometric_rotation :
  forall x1 y1 x2 y2 theta:R,
    dist_euc x1 y1 x2 y2 =
    dist_euc (xr x1 y1 theta) (yr x1 y1 theta) (xr x2 y2 theta)
    (yr x2 y2 theta).
Proof.
  unfold dist_euc; intros; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat
      | apply sqrt_positivity; apply Rplus_le_le_0_compat
      | repeat rewrite Rsqr_sqrt;
        [ apply isometric_rotation_0
          | apply Rplus_le_le_0_compat
          | apply Rplus_le_le_0_compat ] ]; apply Rle_0_sqr.
Qed.

(******************************************************************)
(** *                       Similarity                            *)
(******************************************************************)

Lemma isometric_rot_trans :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr (xt x1 tx) (yt y1 ty) theta - xr (xt x2 tx) (yt y2 ty) theta) +
    Rsqr (yr (xt x1 tx) (yt y1 ty) theta - yr (xt x2 tx) (yt y2 ty) theta).
Proof.
  intros; rewrite <- isometric_rotation_0; apply isometric_translation.
Qed.

Lemma isometric_trans_rot :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt (xr x1 y1 theta) tx - xt (xr x2 y2 theta) tx) +
    Rsqr (yt (yr x1 y1 theta) ty - yt (yr x2 y2 theta) ty).
Proof.
  intros; rewrite <- isometric_translation; apply isometric_rotation_0.
Qed.
