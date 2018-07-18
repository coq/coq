(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Lra.
Require Import Rbase.
Require Import Rtrigo1.
Require Import Ranalysis_reg.
Require Import Rfunctions.
Require Import AltSeries.
Require Import Rseries.
Require Import SeqProp.
Require Import PartSum.
Require Import Ratan.
Require Import Omega.

Local Open Scope R_scope.

(* Proving a few formulas in the style of John Machin to compute Pi *)

Definition atan_sub u v := (u - v)/(1 + u * v).

Lemma atan_sub_correct :
 forall u v, 1 + u * v <> 0 -> -PI/2 < atan u - atan v < PI/2 ->
   -PI/2 < atan (atan_sub u v) < PI/2 ->
   atan u = atan v + atan (atan_sub u v).
Proof.
intros u v pn0 uvint aint.
assert (cos (atan u) <> 0).
 destruct (atan_bound u); apply Rgt_not_eq, cos_gt_0; auto.
 rewrite <- Ropp_div; assumption.
assert (cos (atan v) <> 0).
 destruct (atan_bound v); apply Rgt_not_eq, cos_gt_0; auto.
 rewrite <- Ropp_div; assumption.
assert (t : forall a b c, a - b = c -> a = b + c) by (intros; subst; field).
apply t, tan_is_inj; clear t; try assumption.
rewrite tan_minus; auto.
  rewrite !atan_right_inv; reflexivity.
apply Rgt_not_eq, cos_gt_0; rewrite <- ?Ropp_div; tauto.
rewrite !atan_right_inv; assumption.
Qed.

Lemma tech : forall x y , -1 <= x <= 1 -> -1 < y < 1 -> 
  -PI/2 < atan x - atan y < PI/2.
Proof.
assert (ut := PI_RGT_0).
intros x y [xm1 x1] [ym1 y1].
assert (-(PI/4) <= atan x).
 destruct xm1 as [xm1 | xm1].
  rewrite <- atan_1, <- atan_opp; apply Rlt_le, atan_increasing.
  assumption.
 solve[rewrite <- xm1; change (-1) with (-(1)); rewrite atan_opp, atan_1; apply Rle_refl].
assert (-(PI/4) < atan y).
 rewrite <- atan_1, <- atan_opp; apply atan_increasing.
 assumption.
assert (atan x <= PI/4).
 destruct x1 as [x1 | x1].
  rewrite <- atan_1; apply Rlt_le, atan_increasing.
  assumption.
 solve[rewrite x1, atan_1; apply Rle_refl].
assert (atan y < PI/4).
  rewrite <- atan_1; apply atan_increasing.
  assumption.
rewrite Ropp_div; split; lra.
Qed.

(* A simple formula, reasonably efficient. *)
Lemma Machin_2_3 : PI/4 = atan(/2) + atan(/3).
Proof.
assert (utility : 0 < PI/2) by (apply PI2_RGT_0).
rewrite <- atan_1.
rewrite (atan_sub_correct 1 (/2)).
   apply f_equal, f_equal; unfold atan_sub; field.
  apply Rgt_not_eq; lra.
 apply tech; try split; try lra.
apply atan_bound.
Qed.

Lemma Machin_4_5_239 : PI/4 = 4 * atan (/5) - atan(/239).
Proof.
rewrite <- atan_1.
rewrite (atan_sub_correct 1 (/5));
 [ | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
replace (4 * atan (/5) - atan (/239)) with
  (atan (/5) + (atan (/5) + (atan (/5) + (atan (/5) + -
     atan (/239))))) by ring.
apply f_equal.
replace (atan_sub 1 (/5)) with (2/3) by
  (unfold atan_sub; field).
rewrite (atan_sub_correct (2/3) (/5));
 [apply f_equal | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
replace (atan_sub (2/3) (/5)) with (7/17)  by
  (unfold atan_sub; field).
rewrite (atan_sub_correct (7/17) (/5));
 [apply f_equal | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
replace (atan_sub (7/17) (/5)) with (9/46) by
  (unfold atan_sub; field).
rewrite (atan_sub_correct (9/46) (/5));
 [apply f_equal | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
rewrite <- atan_opp; apply f_equal.
unfold atan_sub; field.
Qed.

Lemma Machin_2_3_7 : PI/4 = 2 * atan(/3) + (atan (/7)).
Proof.
rewrite <- atan_1.
rewrite (atan_sub_correct 1 (/3));
 [ | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
replace (2 * atan (/3) + atan (/7)) with
  (atan (/3) + (atan (/3) + atan (/7))) by ring.
apply f_equal.
replace (atan_sub 1 (/3)) with (/2) by
  (unfold atan_sub; field).
rewrite (atan_sub_correct (/2) (/3));
 [apply f_equal | apply Rgt_not_eq; lra | apply tech; try split; lra |
     apply atan_bound ].
apply f_equal; unfold atan_sub; field.
Qed.

(* More efficient way to compute approximations of PI. *)

Definition PI_2_3_7_tg n := 
  2 * Ratan_seq (/3) n + Ratan_seq (/7) n.

Lemma PI_2_3_7_ineq :
  forall N : nat,
    sum_f_R0 (tg_alt PI_2_3_7_tg) (S (2 * N)) <= PI / 4 <=
    sum_f_R0 (tg_alt PI_2_3_7_tg) (2 * N).
Proof.
assert (dec3 : 0 <= /3 <= 1) by (split; lra).
assert (dec7 : 0 <= /7 <= 1) by (split; lra).
assert (decr : Un_decreasing PI_2_3_7_tg).
 apply Ratan_seq_decreasing in dec3.
 apply Ratan_seq_decreasing in dec7.
 intros n; apply Rplus_le_compat.
  apply Rmult_le_compat_l; [ lra | exact (dec3 n)].
 exact (dec7 n).
assert (cv : Un_cv PI_2_3_7_tg 0).
 apply Ratan_seq_converging in dec3.
 apply Ratan_seq_converging in dec7.
 intros eps ep.
 assert (ep' : 0 < eps /3) by lra.
 destruct (dec3 _ ep') as [N1 Pn1]; destruct (dec7 _ ep') as [N2 Pn2].
 exists (N1 + N2)%nat; intros n Nn.
 unfold PI_2_3_7_tg.
 rewrite <- (Rplus_0_l 0).
 apply Rle_lt_trans with
    (1 := R_dist_plus (2 * Ratan_seq (/3) n) 0 (Ratan_seq (/7) n) 0).
 replace eps with (2 * eps/3 + eps/3) by field.
 apply Rplus_lt_compat.
  unfold R_dist, Rminus, Rdiv.
  rewrite <- (Rmult_0_r 2), <- Ropp_mult_distr_r_reverse.
  rewrite <- Rmult_plus_distr_l, Rabs_mult, (Rabs_pos_eq 2);[|lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l;[lra | ].
   apply (Pn1 n); omega.
  apply (Pn2 n); omega.
rewrite Machin_2_3_7.
rewrite !atan_eq_ps_atan; try (split; lra).
unfold ps_atan; destruct (in_int (/3)); destruct (in_int (/7));
  try match goal with id : ~ _ |- _ => case id; split; lra end.
destruct (ps_atan_exists_1 (/3)) as [v3 Pv3].
destruct (ps_atan_exists_1 (/7)) as [v7 Pv7].
assert (main : Un_cv (sum_f_R0 (tg_alt PI_2_3_7_tg)) (2 * v3 + v7)).
 assert (main :Un_cv (fun n => 2 * sum_f_R0 (tg_alt (Ratan_seq (/3))) n +
                        sum_f_R0 (tg_alt (Ratan_seq (/7))) n) (2 * v3 + v7)).
  apply CV_plus;[ | assumption].
  apply CV_mult;[ | assumption].
  exists 0%nat; intros; rewrite R_dist_eq; assumption.
 apply Un_cv_ext with (2 := main).
 intros n; rewrite scal_sum, <- plus_sum; apply sum_eq; intros.
 rewrite Rmult_comm; unfold PI_2_3_7_tg, tg_alt; field.
intros N; apply (alternated_series_ineq _ _ _ decr cv main).
Qed.
