(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require SeqSeries.
Require Rtrigo_def.
Require Cos_rel.
Require Max.
V7only [Import nat_scope.]. Open Local Scope nat_scope.
V7only [Import R_scope.]. Open Local Scope R_scope.

Definition Majxy [x,y:R] : nat->R := [n:nat](Rdiv (pow (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (4) (S n))) (INR (fact n))).

Lemma Majxy_cv_R0 : (x,y:R) (Un_cv (Majxy x y) R0).
Intros.
Pose C := (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))).
Pose C0 := (pow C (4)).
Cut ``0<C``.
Intro.
Cut ``0<C0``.
Intro.
Assert H1 := (cv_speed_pow_fact C0).
Unfold Un_cv in H1; Unfold R_dist in H1.
Unfold Un_cv; Unfold R_dist; Intros.
Cut ``0<eps/C0``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Assumption]].
Elim (H1 ``eps/C0`` H3); Intros N0 H4.
Exists N0; Intros.
Replace (Majxy x y n) with ``(pow C0 (S n))/(INR (fact n))``.
Simpl.
Apply Rlt_monotony_contra with ``(Rabsolu (/C0))``.
Apply Rabsolu_pos_lt.
Apply Rinv_neq_R0.
Red; Intro; Rewrite H6 in H0; Elim (Rlt_antirefl ? H0).
Rewrite <- Rabsolu_mult.
Unfold Rminus; Rewrite Rmult_Rplus_distr.
Rewrite Ropp_O; Rewrite Rmult_Or.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite (Rabsolu_right ``/C0``).
Rewrite <- (Rmult_sym eps).
Replace ``(pow C0 n)*/(INR (fact n))+0`` with ``(pow C0 n)*/(INR (fact n))-0``; [Idtac | Ring].
Unfold Rdiv in H4; Apply H4; Assumption.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Assumption.
Red; Intro; Rewrite H6 in H0; Elim (Rlt_antirefl ? H0).
Unfold Majxy.
Unfold C0.
Rewrite pow_mult.
Unfold C; Reflexivity.
Unfold C0; Apply pow_lt; Assumption.
Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C.
Apply RmaxLess1.
Qed.

Lemma reste1_maj : (x,y:R;N:nat) (lt O N) -> ``(Rabsolu (Reste1 x y N))<=(Majxy x y (pred N))``.
Intros.
Pose C := (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))).
Unfold Reste1.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (Rabsolu (sum_f_R0
          [l:nat]
           ``(pow ( -1) (S (plus l k)))/
           (INR (fact (mult (S (S O)) (S (plus l k)))))*
           (pow x (mult (S (S O)) (S (plus l k))))*
           (pow ( -1) (minus N l))/
           (INR (fact (mult (S (S O)) (minus N l))))*
           (pow y (mult (S (S O)) (minus N l)))`` (pred (minus N k))))
     (pred N)).
Apply (sum_Rabsolu [k:nat]
        (sum_f_R0
          [l:nat]
           ``(pow ( -1) (S (plus l k)))/
           (INR (fact (mult (S (S O)) (S (plus l k)))))*
           (pow x (mult (S (S O)) (S (plus l k))))*
           (pow ( -1) (minus N l))/
           (INR (fact (mult (S (S O)) (minus N l))))*
           (pow y (mult (S (S O)) (minus N l)))`` (pred (minus N k))) (pred N)).
Apply Rle_trans with (sum_f_R0
     [k:nat]
          (sum_f_R0
            [l:nat]
             (Rabsolu (``(pow ( -1) (S (plus l k)))/
             (INR (fact (mult (S (S O)) (S (plus l k)))))*
             (pow x (mult (S (S O)) (S (plus l k))))*
             (pow ( -1) (minus N l))/
             (INR (fact (mult (S (S O)) (minus N l))))*
             (pow y (mult (S (S O)) (minus N l)))``)) (pred (minus N k)))
     (pred N)).
Apply sum_Rle.
Intros.
Apply (sum_Rabsolu [l:nat]
        ``(pow ( -1) (S (plus l n)))/
        (INR (fact (mult (S (S O)) (S (plus l n)))))*
        (pow x (mult (S (S O)) (S (plus l n))))*
        (pow ( -1) (minus N l))/
        (INR (fact (mult (S (S O)) (minus N l))))*
        (pow y (mult (S (S O)) (minus N l)))`` (pred (minus N n))).
Apply Rle_trans with (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``/(INR (mult (fact (mult (S (S O)) (S (plus l k)))) (fact (mult (S (S O)) (minus N l)))))*(pow C (mult (S (S O)) (S (plus N k))))`` (pred (minus N k))) (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Unfold Rdiv; Repeat Rewrite Rabsolu_mult.
Do 2 Rewrite pow_1_abs.
Do 2 Rewrite Rmult_1l.
Rewrite (Rabsolu_right ``/(INR (fact (mult (S (S O)) (S (plus n0 n)))))``).
Rewrite (Rabsolu_right ``/(INR (fact (mult (S (S O)) (minus N n0))))``).
Rewrite mult_INR.
Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Rewrite <- Rmult_assoc.
Rewrite <- (Rmult_sym ``/(INR (fact (mult (S (S O)) (minus N n0))))``).
Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Do 2 Rewrite <- Pow_Rabsolu.
Apply Rle_trans with ``(pow (Rabsolu x) (mult (S (S O)) (S (plus n0 n))))*(pow C (mult (S (S O)) (minus N n0)))``.
Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Apply pow_incr.
Split.
Apply Rabsolu_pos.
Unfold C.
Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)); Apply RmaxLess2.
Apply Rle_trans with ``(pow C (mult (S (S O)) (S (plus n0 n))))*(pow C (mult (S (S O)) (minus N n0)))``.
Do 2 Rewrite <- (Rmult_sym ``(pow C (mult (S (S O)) (minus N n0)))``).
Apply Rle_monotony.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Apply pow_incr.
Split.
Apply Rabsolu_pos.
Unfold C; Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)).
Apply RmaxLess1.
Apply RmaxLess2.
Right.
Replace (mult (2) (S (plus N n))) with (plus (mult (2) (minus N n0)) (mult (2) (S (plus n0 n)))).
Rewrite pow_add.
Apply Rmult_sym.
Apply INR_eq; Rewrite plus_INR; Do 3 Rewrite mult_INR.
Rewrite minus_INR.
Repeat Rewrite S_INR; Do 2 Rewrite plus_INR; Ring.
Apply le_trans with (pred (minus N n)).
Exact H1.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (sum_f_R0
          [l:nat]
           ``/(INR
              (mult (fact (mult (S (S O)) (S (plus l k))))
              (fact (mult (S (S O)) (minus N l)))))*
           (pow C (mult (S (S (S (S O)))) N))`` (pred (minus N k)))
     (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Apply Rle_monotony.
Left; Apply Rlt_Rinv.
Rewrite mult_INR; Apply Rmult_lt_pos; Apply INR_fact_lt_0.
Apply Rle_pow.
Unfold C; Apply RmaxLess1.
Replace (mult (4) N) with (mult (2) (mult (2) N)); [Idtac | Ring].
Apply mult_le.
Replace (mult (2) N) with (S (plus N (pred N))).
Apply le_n_S.
Apply le_reg_l; Assumption.
Rewrite pred_of_minus.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Rewrite minus_INR.
Repeat Rewrite S_INR; Ring.
Apply lt_le_S; Assumption.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (sum_f_R0
          [l:nat]
         ``(pow C (mult (S (S (S (S O)))) N))*(Rsqr (/(INR (fact (S (plus N k))))))`` (pred (minus N k)))
     (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) N))``).
Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Replace ``/(INR
      (mult (fact (mult (S (S O)) (S (plus n0 n))))
      (fact (mult (S (S O)) (minus N n0)))))`` with ``(Binomial.C (mult (S (S O)) (S (plus N n))) (mult (S (S O)) (S (plus n0 n))))/(INR (fact (mult (S (S O)) (S (plus N n)))))``.
Apply Rle_trans with ``(Binomial.C (mult (S (S O)) (S (plus N n))) (S (plus N n)))/(INR (fact (mult (S (S O)) (S (plus N n)))))``.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/(INR (fact (mult (S (S O)) (S (plus N n)))))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply C_maj.
Apply mult_le.
Apply le_n_S.
Apply le_reg_r.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Right.
Unfold Rdiv; Rewrite Rmult_sym.
Unfold Binomial.C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace (minus (mult (2) (S (plus N n))) (S (plus N n))) with (S (plus N n)).
Rewrite Rinv_Rmult.
Unfold Rsqr; Reflexivity.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Rewrite S_INR; Rewrite minus_INR.
Rewrite mult_INR; Repeat Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_2n.
Apply INR_fact_neq_0.
Unfold Rdiv; Rewrite Rmult_sym.
Unfold Binomial.C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace (minus (mult (2) (S (plus N n))) (mult (2) (S (plus n0 n)))) with (mult (2) (minus N n0)).
Rewrite mult_INR.
Reflexivity.
Apply INR_eq; Rewrite minus_INR.
Do 3 Rewrite mult_INR; Repeat Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite minus_INR.
Ring.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply mult_le.
Apply le_n_S.
Apply le_reg_r.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_fact_neq_0.
Apply Rle_trans with (sum_f_R0 [k:nat]``(INR N)/(INR (fact (S N)))*(pow C (mult (S (S (S (S O)))) N))`` (pred N)).
Apply sum_Rle; Intros.
Rewrite <- (scal_sum [_:nat]``(pow C (mult (S (S (S (S O)))) N))`` (pred (minus N n)) ``(Rsqr (/(INR (fact (S (plus N n))))))``).
Rewrite sum_cte.
Rewrite <- Rmult_assoc.
Do 2 Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) N))``).
Rewrite Rmult_assoc.
Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Apply Rle_trans with ``(Rsqr (/(INR (fact (S (plus N n))))))*(INR N)``.
Apply Rle_monotony.
Apply pos_Rsqr.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_INR.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Rewrite Rmult_sym; Unfold Rdiv; Apply Rle_monotony.
Apply pos_INR.
Apply Rle_trans with ``/(INR (fact (S (plus N n))))``.
Pattern 2 ``/(INR (fact (S (plus N n))))``; Rewrite <- Rmult_1r.
Unfold Rsqr.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_monotony_contra with ``(INR (fact (S (plus N n))))``.
Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Replace R1 with (INR (S O)).
Apply le_INR.
Apply lt_le_S.
Apply INR_lt; Apply INR_fact_lt_0.
Reflexivity.
Apply INR_fact_neq_0.
Apply Rle_monotony_contra with ``(INR (fact (S (plus N n))))``.
Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with ``(INR (fact (S N)))``.
Apply INR_fact_lt_0.
Rewrite Rmult_1r.
Rewrite (Rmult_sym (INR (fact (S N)))).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Apply le_INR.
Apply fact_growing.
Apply le_n_S.
Apply le_plus_l.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Rewrite sum_cte.
Apply Rle_trans with ``(pow C (mult (S (S (S (S O)))) N))/(INR (fact (pred N)))``.
Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) N))``).
Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Cut (S (pred N)) = N.
Intro; Rewrite H0.
Pattern 2 N; Rewrite <- H0.
Do 2 Rewrite fact_simpl.
Rewrite H0.
Repeat Rewrite mult_INR.
Repeat Rewrite Rinv_Rmult.
Rewrite (Rmult_sym ``/(INR (S N))``).
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Pattern 2 ``/(INR (fact (pred N)))``; Rewrite <- Rmult_1r.
Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_monotony_contra with (INR (S N)).
Apply lt_INR_0; Apply lt_O_Sn.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Rewrite Rmult_1l.
Apply le_INR; Apply le_n_Sn.
Apply not_O_INR; Discriminate.
Apply not_O_INR.
Red; Intro; Rewrite H1 in H; Elim (lt_n_n ? H).
Apply not_O_INR.
Red; Intro; Rewrite H1 in H; Elim (lt_n_n ? H).
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply prod_neq_R0.
Apply not_O_INR.
Red; Intro; Rewrite H1 in H; Elim (lt_n_n ? H).
Apply INR_fact_neq_0.
Symmetry; Apply S_pred with O; Assumption.
Right.
Unfold Majxy.
Unfold C.
Replace (S (pred N)) with N.
Reflexivity.
Apply S_pred with O; Assumption.
Qed.

Lemma reste2_maj : (x,y:R;N:nat) (lt O N) -> ``(Rabsolu (Reste2 x y N))<=(Majxy x y N)``.
Intros.
Pose C := (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))).
Unfold Reste2.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (Rabsolu (sum_f_R0
          [l:nat]
           ``(pow ( -1) (S (plus l k)))/
           (INR (fact (plus (mult (S (S O)) (S (plus l k))) (S O))))*
           (pow x (plus (mult (S (S O)) (S (plus l k))) (S O)))*
           (pow ( -1) (minus N l))/
           (INR (fact (plus (mult (S (S O)) (minus N l)) (S O))))*
           (pow y (plus (mult (S (S O)) (minus N l)) (S O)))`` (pred (minus N k))))
     (pred N)).
Apply (sum_Rabsolu [k:nat]
        (sum_f_R0
          [l:nat]
           ``(pow ( -1) (S (plus l k)))/
           (INR (fact (plus (mult (S (S O)) (S (plus l k))) (S O))))*
           (pow x (plus (mult (S (S O)) (S (plus l k))) (S O)))*
           (pow ( -1) (minus N l))/
           (INR (fact (plus (mult (S (S O)) (minus N l)) (S O))))*
           (pow y (plus (mult (S (S O)) (minus N l)) (S O)))`` (pred (minus N k))) (pred N)).
Apply Rle_trans with (sum_f_R0
     [k:nat]
          (sum_f_R0
            [l:nat]
             (Rabsolu (``(pow ( -1) (S (plus l k)))/
             (INR (fact (plus (mult (S (S O)) (S (plus l k))) (S O))))*
             (pow x (plus (mult (S (S O)) (S (plus l k))) (S O)))*
             (pow ( -1) (minus N l))/
             (INR (fact (plus (mult (S (S O)) (minus N l)) (S O))))*
             (pow y (plus (mult (S (S O)) (minus N l)) (S O)))``)) (pred (minus N k)))
     (pred N)).
Apply sum_Rle.
Intros.
Apply (sum_Rabsolu [l:nat]
        ``(pow ( -1) (S (plus l n)))/
        (INR (fact (plus (mult (S (S O)) (S (plus l n))) (S O))))*
        (pow x (plus (mult (S (S O)) (S (plus l n))) (S O)))*
        (pow ( -1) (minus N l))/
        (INR (fact (plus (mult (S (S O)) (minus N l)) (S O))))*
        (pow y (plus (mult (S (S O)) (minus N l)) (S O)))`` (pred (minus N n))).
Apply Rle_trans with (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``/(INR (mult (fact (plus (mult (S (S O)) (S (plus l k))) (S O))) (fact (plus (mult (S (S O)) (minus N l)) (S O)))))*(pow C (mult (S (S O)) (S (S (plus N k)))))`` (pred (minus N k))) (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Unfold Rdiv; Repeat Rewrite Rabsolu_mult.
Do 2 Rewrite pow_1_abs.
Do 2 Rewrite Rmult_1l.
Rewrite (Rabsolu_right ``/(INR (fact (plus (mult (S (S O)) (S (plus n0 n))) (S O))))``).
Rewrite (Rabsolu_right ``/(INR (fact (plus (mult (S (S O)) (minus N n0)) (S O))))``).
Rewrite mult_INR.
Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Rewrite <- Rmult_assoc.
Rewrite <- (Rmult_sym ``/(INR (fact (plus (mult (S (S O)) (minus N n0)) (S O))))``).
Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Do 2 Rewrite <- Pow_Rabsolu.
Apply Rle_trans with ``(pow (Rabsolu x) (plus (mult (S (S O)) (S (plus n0 n))) (S O)))*(pow C (plus (mult (S (S O)) (minus N n0)) (S O)))``.
Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Apply pow_incr.
Split.
Apply Rabsolu_pos.
Unfold C.
Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)); Apply RmaxLess2.
Apply Rle_trans with ``(pow C (plus (mult (S (S O)) (S (plus n0 n))) (S O)))*(pow C (plus (mult (S (S O)) (minus N n0)) (S O)))``.
Do 2 Rewrite <- (Rmult_sym ``(pow C (plus (mult (S (S O)) (minus N n0)) (S O)))``).
Apply Rle_monotony.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Apply pow_incr.
Split.
Apply Rabsolu_pos.
Unfold C; Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)).
Apply RmaxLess1.
Apply RmaxLess2.
Right.
Replace (mult (2) (S (S (plus N n)))) with (plus (plus (mult (2) (minus N n0)) (S O)) (plus (mult (2) (S (plus n0 n))) (S O))).
Repeat Rewrite pow_add.
Ring.
Apply INR_eq; Repeat Rewrite plus_INR; Do 3 Rewrite mult_INR.
Rewrite minus_INR.
Repeat Rewrite S_INR; Do 2 Rewrite plus_INR; Ring.
Apply le_trans with (pred (minus N n)).
Exact H1.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply Rle_sym1; Left; Apply Rlt_Rinv.
Apply INR_fact_lt_0.
Apply Rle_sym1; Left; Apply Rlt_Rinv.
Apply INR_fact_lt_0.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (sum_f_R0
          [l:nat]
           ``/(INR
              (mult (fact (plus (mult (S (S O)) (S (plus l k))) (S O)))
              (fact (plus (mult (S (S O)) (minus N l)) (S O)))))*
           (pow C (mult (S (S (S (S O)))) (S N)))`` (pred (minus N k)))
     (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Apply Rle_monotony.
Left; Apply Rlt_Rinv.
Rewrite mult_INR; Apply Rmult_lt_pos; Apply INR_fact_lt_0.
Apply Rle_pow.
Unfold C; Apply RmaxLess1.
Replace (mult (4) (S N)) with (mult (2) (mult (2) (S N))); [Idtac | Ring].
Apply mult_le.
Replace (mult (2) (S N)) with (S (S (plus N N))).
Repeat Apply le_n_S.
Apply le_reg_l.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_eq; Do 2Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR.
Repeat Rewrite S_INR; Ring.
Apply Rle_trans with (sum_f_R0
     [k:nat]
        (sum_f_R0
          [l:nat]
         ``(pow C (mult (S (S (S (S O)))) (S N)))*(Rsqr (/(INR (fact (S (S (plus N k)))))))`` (pred (minus N k)))
     (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) (S N)))``).
Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Replace ``/(INR
      (mult (fact (plus (mult (S (S O)) (S (plus n0 n))) (S O)))
      (fact (plus (mult (S (S O)) (minus N n0)) (S O)))))`` with ``(Binomial.C (mult (S (S O)) (S (S (plus N n)))) (plus (mult (S (S O)) (S (plus n0 n))) (S O)))/(INR (fact (mult (S (S O)) (S (S (plus N n))))))``.
Apply Rle_trans with ``(Binomial.C (mult (S (S O)) (S (S (plus N n)))) (S (S (plus N n))))/(INR (fact (mult (S (S O)) (S (S (plus N n))))))``.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/(INR (fact (mult (S (S O)) (S (S (plus N n))))))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply C_maj.
Apply le_trans with (mult (2) (S (S (plus n0 n)))).
Replace (mult (2) (S (S (plus n0 n)))) with (S (plus (mult (2) (S (plus n0 n))) (1))).
Apply le_n_Sn.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Rewrite plus_INR; Ring.
Apply mult_le.
Repeat Apply le_n_S.
Apply le_reg_r.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Right.
Unfold Rdiv; Rewrite Rmult_sym.
Unfold Binomial.C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace (minus (mult (2) (S (S (plus N n)))) (S (S (plus N n)))) with (S (S (plus N n))).
Rewrite Rinv_Rmult.
Unfold Rsqr; Reflexivity.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Do 2 Rewrite S_INR; Rewrite minus_INR.
Rewrite mult_INR; Repeat Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_2n.
Apply INR_fact_neq_0.
Unfold Rdiv; Rewrite Rmult_sym.
Unfold Binomial.C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace (minus (mult (2) (S (S (plus N n)))) (plus (mult (2) (S (plus n0 n))) (S O))) with (plus (mult (2) (minus N n0)) (S O)).
Rewrite mult_INR.
Reflexivity.
Apply INR_eq; Rewrite minus_INR.
Do 2 Rewrite plus_INR; Do 3 Rewrite mult_INR; Repeat Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite minus_INR.
Ring.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_trans with (mult (2) (S (S (plus n0 n)))).
Replace (mult (2) (S (S (plus n0 n)))) with (S (plus (mult (2) (S (plus n0 n))) (1))).
Apply le_n_Sn.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Rewrite plus_INR; Ring.
Apply mult_le.
Repeat Apply le_n_S.
Apply le_reg_r.
Apply le_trans with (pred (minus N n)).
Assumption.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_fact_neq_0.
Apply Rle_trans with (sum_f_R0 [k:nat]``(INR N)/(INR (fact (S (S N))))*(pow C (mult (S (S (S (S O)))) (S N)))`` (pred N)).
Apply sum_Rle; Intros.
Rewrite <- (scal_sum [_:nat]``(pow C (mult (S (S (S (S O)))) (S N)))`` (pred (minus N n)) ``(Rsqr (/(INR (fact (S (S (plus N n)))))))``).
Rewrite sum_cte.
Rewrite <- Rmult_assoc.
Do 2 Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) (S N)))``).
Rewrite Rmult_assoc.
Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Apply Rle_trans with ``(Rsqr (/(INR (fact (S (S (plus N n)))))))*(INR N)``.
Apply Rle_monotony.
Apply pos_Rsqr.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_INR.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n O) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n; Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Rewrite Rmult_sym; Unfold Rdiv; Apply Rle_monotony.
Apply pos_INR.
Apply Rle_trans with ``/(INR (fact (S (S (plus N n)))))``.
Pattern 2 ``/(INR (fact (S (S (plus N n)))))``; Rewrite <- Rmult_1r.
Unfold Rsqr.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_monotony_contra with ``(INR (fact (S (S (plus N n)))))``.
Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Replace R1 with (INR (S O)).
Apply le_INR.
Apply lt_le_S.
Apply INR_lt; Apply INR_fact_lt_0.
Reflexivity.
Apply INR_fact_neq_0.
Apply Rle_monotony_contra with ``(INR (fact (S (S (plus N n)))))``.
Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with ``(INR (fact (S (S N))))``.
Apply INR_fact_lt_0.
Rewrite Rmult_1r.
Rewrite (Rmult_sym (INR (fact (S (S N))))).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Apply le_INR.
Apply fact_growing.
Repeat Apply le_n_S.
Apply le_plus_l.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Rewrite sum_cte.
Apply Rle_trans with ``(pow C (mult (S (S (S (S O)))) (S N)))/(INR (fact N))``.
Rewrite <- (Rmult_sym ``(pow C (mult (S (S (S (S O)))) (S N)))``).
Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Apply pow_le.
Left; Apply Rlt_le_trans with R1.
Apply Rlt_R0_R1.
Unfold C; Apply RmaxLess1.
Cut (S (pred N)) = N.
Intro; Rewrite H0.
Do 2 Rewrite fact_simpl.
Repeat Rewrite mult_INR.
Repeat Rewrite Rinv_Rmult.
Apply Rle_trans with ``(INR (S (S N)))*(/(INR (S (S N)))*(/(INR (S N))*/(INR (fact N))))*
   (INR N)``.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym (INR N)).
Rewrite (Rmult_sym (INR (S (S N)))).
Apply Rle_monotony.
Repeat Apply Rmult_le_pos.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply lt_O_Sn.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply lt_O_Sn.
Left; Apply Rlt_Rinv.
Apply INR_fact_lt_0.
Apply pos_INR.
Apply le_INR.
Apply le_trans with (S N); Apply le_n_Sn.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Apply Rle_trans with ``/(INR (S N))*/(INR (fact N))*(INR (S N))``.
Repeat Rewrite Rmult_assoc.
Repeat Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply lt_O_Sn.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply le_INR; Apply le_n_Sn.
Rewrite (Rmult_sym ``/(INR (S N))``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Right; Reflexivity.
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply prod_neq_R0; [Apply not_O_INR; Discriminate | Apply INR_fact_neq_0].
Symmetry; Apply S_pred with O; Assumption.
Right.
Unfold Majxy.
Unfold C.
Reflexivity.
Qed.

Lemma reste1_cv_R0 : (x,y:R) (Un_cv (Reste1 x y) R0).
Intros.
Assert H := (Majxy_cv_R0 x y).
Unfold Un_cv in H; Unfold R_dist in H.
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H eps H0); Intros N0 H1.
Exists (S N0); Intros.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or.
Apply Rle_lt_trans with (Rabsolu (Majxy x y (pred n))).
Rewrite (Rabsolu_right (Majxy x y (pred n))).
Apply reste1_maj.
Apply lt_le_trans with (S N0).
Apply lt_O_Sn.
Assumption.
Apply Rle_sym1.
Unfold Majxy.
Unfold Rdiv; Apply Rmult_le_pos.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Replace (Majxy x y (pred n)) with ``(Majxy x y (pred n))-0``; [Idtac | Ring].
Apply H1.
Unfold ge; Apply le_S_n.
Replace (S (pred n)) with n.
Assumption.
Apply S_pred with O.
Apply lt_le_trans with (S N0); [Apply lt_O_Sn | Assumption].
Qed.

Lemma reste2_cv_R0 : (x,y:R) (Un_cv (Reste2 x y) R0).
Intros.
Assert H := (Majxy_cv_R0 x y).
Unfold Un_cv in H; Unfold R_dist in H.
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H eps H0); Intros N0 H1.
Exists (S N0); Intros.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or.
Apply Rle_lt_trans with (Rabsolu (Majxy x y n)).
Rewrite (Rabsolu_right (Majxy x y n)).
Apply reste2_maj.
Apply lt_le_trans with (S N0).
Apply lt_O_Sn.
Assumption.
Apply Rle_sym1.
Unfold Majxy.
Unfold Rdiv; Apply Rmult_le_pos.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Replace (Majxy x y n) with ``(Majxy x y n)-0``; [Idtac | Ring].
Apply H1.
Unfold ge; Apply le_trans with (S N0).
Apply le_n_Sn.
Exact H2.
Qed.

Lemma reste_cv_R0 : (x,y:R) (Un_cv (Reste x y) R0).
Intros.
Unfold Reste.
Pose An := [n:nat](Reste2 x y n).
Pose Bn := [n:nat](Reste1 x y (S n)).
Cut (Un_cv [n:nat]``(An n)-(Bn n)`` ``0-0``) -> (Un_cv [N:nat]``(Reste2 x y N)-(Reste1 x y (S N))`` ``0``).
Intro.
Apply H.
Apply CV_minus.
Unfold An.
Replace [n:nat](Reste2 x y n) with (Reste2 x y).
Apply reste2_cv_R0.
Reflexivity.
Unfold Bn.
Assert H0 := (reste1_cv_R0 x y).
Unfold Un_cv in H0; Unfold R_dist in H0.
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H0 eps H1); Intros N0 H2.
Exists N0; Intros.
Apply H2.
Unfold ge; Apply le_trans with (S N0).
Apply le_n_Sn.
Apply le_n_S; Assumption.
Unfold An Bn.
Intro.
Replace R0 with ``0-0``; [Idtac | Ring].
Exact H.
Qed.

Theorem cos_plus : (x,y:R) ``(cos (x+y))==(cos x)*(cos y)-(sin x)*(sin y)``. 
Intros. 
Cut (Un_cv (C1 x y) ``(cos x)*(cos y)-(sin x)*(sin y)``). 
Cut (Un_cv (C1 x y) ``(cos (x+y))``). 
Intros. 
Apply UL_sequence with (C1 x y); Assumption. 
Apply C1_cvg. 
Unfold Un_cv; Unfold R_dist. 
Intros. 
Assert H0 := (A1_cvg x). 
Assert H1 := (A1_cvg y). 
Assert H2 := (B1_cvg x). 
Assert H3 := (B1_cvg y). 
Assert H4 := (CV_mult ? ? ? ? H0 H1). 
Assert H5 := (CV_mult ? ? ? ? H2 H3). 
Assert H6 := (reste_cv_R0 x y).
Unfold Un_cv in H4; Unfold Un_cv in H5; Unfold Un_cv in H6.
Unfold R_dist in H4; Unfold R_dist in H5; Unfold R_dist in H6. 
Cut ``0<eps/3``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (H4 ``eps/3`` H7); Intros N1 H8. 
Elim (H5 ``eps/3`` H7); Intros N2 H9. 
Elim (H6 ``eps/3`` H7); Intros N3 H10.
Pose N := (S (S (max (max N1 N2) N3))). 
Exists N. 
Intros. 
Cut n = (S (pred n)). 
Intro; Rewrite H12. 
Rewrite <- cos_plus_form. 
Rewrite <- H12. 
Apply Rle_lt_trans with ``(Rabsolu ((A1 x n)*(A1 y n)-(cos x)*(cos y)))+(Rabsolu ((sin x)*(sin y)-(B1 x (pred n))*(B1 y (pred n))+(Reste x y (pred n))))``. 
Replace ``(A1 x n)*(A1 y n)-(B1 x (pred n))*(B1 y (pred n))+
     (Reste x y (pred n))-((cos x)*(cos y)-(sin x)*(sin y))`` with ``((A1 x n)*(A1 y n)-(cos x)*(cos y))+((sin x)*(sin y)-(B1 x (pred n))*(B1 y (pred n))+(Reste x y (pred n)))``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``eps/3+(eps/3+eps/3)``.
Apply Rplus_lt. 
Apply H8. 
Unfold ge; Apply le_trans with N. 
Unfold N. 
Apply le_trans with (max N1 N2). 
Apply le_max_l. 
Apply le_trans with (max (max N1 N2) N3).
Apply le_max_l.
Apply le_trans with (S (max (max N1 N2) N3)); Apply le_n_Sn.
Assumption. 
Apply Rle_lt_trans with ``(Rabsolu ((sin x)*(sin y)-(B1 x (pred n))*(B1 y (pred n))))+(Rabsolu (Reste x y (pred n)))``.
Apply Rabsolu_triang.
Apply Rplus_lt.
Rewrite <- Rabsolu_Ropp. 
Rewrite Ropp_distr2. 
Apply H9. 
Unfold ge; Apply le_trans with (max N1 N2). 
Apply le_max_r. 
Apply le_S_n. 
Rewrite <- H12. 
Apply le_trans with N.
Unfold N.
Apply le_n_S.
Apply le_trans with (max (max N1 N2) N3).
Apply le_max_l.
Apply le_n_Sn.
Assumption.
Replace (Reste x y (pred n)) with ``(Reste x y (pred n))-0``.
Apply H10.
Unfold ge.
Apply le_S_n.
Rewrite <- H12.
Apply le_trans with N.
Unfold N.
Apply le_n_S.
Apply le_trans with (max (max N1 N2) N3).
Apply le_max_r.
Apply le_n_Sn.
Assumption.
Ring.
Pattern 4 eps; Replace eps with ``3*eps/3``.
Ring.
Unfold Rdiv.
Rewrite <- Rmult_assoc.
Apply Rinv_r_simpl_m.
DiscrR.
Apply lt_le_trans with (pred N).
Unfold N; Simpl; Apply lt_O_Sn.
Apply le_S_n.
Rewrite <- H12.
Replace (S (pred N)) with N.
Assumption.
Unfold N; Simpl; Reflexivity.
Cut (lt O N). 
Intro. 
Cut (lt O n). 
Intro. 
Apply S_pred with O; Assumption.
Apply lt_le_trans with N; Assumption. 
Unfold N; Apply lt_O_Sn.
Qed.
