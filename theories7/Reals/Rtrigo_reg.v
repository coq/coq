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
Require Rtrigo.
Require Ranalysis1.
Require PSeries_reg.
V7only [Import nat_scope. Import Z_scope. Import R_scope.].
Open Local Scope nat_scope.
Open Local Scope R_scope.

Lemma CVN_R_cos : (fn:nat->R->R) (fn == [N:nat][x:R]``(pow (-1) N)/(INR (fact (mult (S (S O)) N)))*(pow x (mult (S (S O)) N))``) -> (CVN_R fn).
Unfold CVN_R; Intros.
Cut (r::R)<>``0``.
Intro hyp_r; Unfold CVN_r.
Apply Specif.existT with [n:nat]``/(INR (fact (mult (S (S O)) n)))*(pow r (mult (S (S O)) n))``.
Cut (SigT ? [l:R](Un_cv [n:nat](sum_f_R0 [k:nat](Rabsolu ``/(INR (fact (mult (S (S O)) k)))*(pow r (mult (S (S O)) k))``) n) l)).
Intro; Elim X; Intros.
Apply existTT with x.
Split.
Apply p.
Intros; Rewrite H; Unfold Rdiv; Do 2 Rewrite Rabsolu_mult.
Rewrite pow_1_abs; Rewrite Rmult_1l.
Cut ``0</(INR (fact (mult (S (S O)) n)))``.
Intro; Rewrite (Rabsolu_right  ? (Rle_sym1 ? ? (Rlt_le ? ? H1))).
Apply Rle_monotony.
Left; Apply H1.
Rewrite <- Pow_Rabsolu; Apply pow_maj_Rabs.
Rewrite Rabsolu_Rabsolu.
Unfold Boule in H0; Rewrite minus_R0 in H0.
Left; Apply H0.
Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Alembert_C2.
Intro; Apply Rabsolu_no_R0.
Apply prod_neq_R0.
Apply Rinv_neq_R0.
Apply INR_fact_neq_0.
Apply pow_nonzero; Assumption.
Assert H0 := Alembert_cos.
Unfold cos_n in H0; Unfold Un_cv in H0; Unfold Un_cv; Intros.
Cut ``0<eps/(Rsqr r)``.
Intro; Elim (H0 ? H2); Intros N0 H3.
Exists N0; Intros.
Unfold R_dist; Assert H5 := (H3 ? H4).
Unfold R_dist in H5; Replace ``(Rabsolu ((Rabsolu (/(INR (fact (mult (S (S O)) (S n))))*(pow r (mult (S (S O)) (S n)))))/(Rabsolu (/(INR (fact (mult (S (S O)) n)))*(pow r (mult (S (S O)) n))))))`` with ``(Rsqr r)*(Rabsolu ((pow ( -1) (S n))/(INR (fact (mult (S (S O)) (S n))))/((pow ( -1) n)/(INR (fact (mult (S (S O)) n))))))``.
Apply Rlt_monotony_contra with ``/(Rsqr r)``.
Apply Rlt_Rinv; Apply Rsqr_pos_lt; Assumption.
Pattern 1 ``/(Rsqr r)``; Replace ``/(Rsqr r)`` with ``(Rabsolu (/(Rsqr r)))``.
Rewrite <- Rabsolu_mult; Rewrite Rminus_distr; Rewrite Rmult_Or; Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps); Apply H5.
Unfold Rsqr; Apply prod_neq_R0; Assumption.
Rewrite Rabsolu_Rinv.
Rewrite Rabsolu_right.
Reflexivity.
Apply Rle_sym1; Apply pos_Rsqr.
Unfold Rsqr; Apply prod_neq_R0; Assumption.
Rewrite (Rmult_sym (Rsqr r)); Unfold Rdiv; Repeat Rewrite Rabsolu_mult; Rewrite Rabsolu_Rabsolu; Rewrite pow_1_abs; Rewrite Rmult_1l; Repeat Rewrite Rmult_assoc; Apply Rmult_mult_r.
Rewrite Rabsolu_Rinv.
Rewrite Rabsolu_mult; Rewrite (pow_1_abs n); Rewrite Rmult_1l; Rewrite <- Rabsolu_Rinv.
Rewrite Rinv_Rinv.
Rewrite Rinv_Rmult.
Rewrite Rabsolu_Rinv.
Rewrite Rinv_Rinv.
Rewrite (Rmult_sym ``(Rabsolu (Rabsolu (pow r (mult (S (S O)) (S n)))))``); Rewrite Rabsolu_mult; Rewrite Rabsolu_Rabsolu; Rewrite Rmult_assoc; Apply Rmult_mult_r.
Rewrite Rabsolu_Rinv.
Do 2 Rewrite Rabsolu_Rabsolu; Repeat Rewrite Rabsolu_right.
Replace ``(pow r (mult (S (S O)) (S n)))`` with ``(pow r (mult (S (S O)) n))*r*r``.
Repeat Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Unfold Rsqr; Ring.
Apply pow_nonzero; Assumption.
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply Rle_sym1; Apply pow_le; Left; Apply (cond_pos r).
Apply Rle_sym1; Apply pow_le; Left; Apply (cond_pos r).
Apply Rabsolu_no_R0; Apply pow_nonzero; Assumption.
Apply Rabsolu_no_R0; Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply Rabsolu_no_R0; Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Apply Rabsolu_no_R0; Apply pow_nonzero; Assumption.
Apply INR_fact_neq_0.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Apply prod_neq_R0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply H1.
Apply Rlt_Rinv; Apply Rsqr_pos_lt; Assumption.
Assert H0 := (cond_pos r); Red; Intro; Rewrite H1 in H0; Elim (Rlt_antirefl ? H0).
Qed.

(**********)
Lemma continuity_cos : (continuity cos).
Pose fn := [N:nat][x:R]``(pow (-1) N)/(INR (fact (mult (S (S O)) N)))*(pow x (mult (S (S O)) N))``.
Cut (CVN_R fn).
Intro; Cut (x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l)).
Intro cv; Cut ((n:nat)(continuity (fn n))).
Intro; Cut (x:R)(cos x)==(SFL fn cv x).
Intro; Cut (continuity (SFL fn cv))->(continuity cos).
Intro; Apply H1.
Apply SFL_continuity; Assumption.
Unfold continuity; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Elim (H1 x ? H2); Intros.
Exists x0; Intros.
Elim H3; Intros.
Split.
Apply H4.
Intros; Rewrite (H0 x); Rewrite (H0 x1); Apply H5; Apply H6.
Intro; Unfold cos SFL.
Case (cv x); Case (exist_cos (Rsqr x)); Intros.
Symmetry; EApply UL_sequence.
Apply u.
Unfold cos_in in c; Unfold infinit_sum in c; Unfold Un_cv; Intros.
Elim (c ? H0); Intros N0 H1.
Exists N0; Intros.
Unfold R_dist in H1; Unfold R_dist SP.
Replace (sum_f_R0 [k:nat](fn k x) n) with (sum_f_R0 [i:nat]``(cos_n i)*(pow (Rsqr x) i)`` n).
Apply H1; Assumption.
Apply sum_eq; Intros.
Unfold cos_n fn; Apply Rmult_mult_r.
Unfold Rsqr; Rewrite pow_sqr; Reflexivity.
Intro; Unfold fn; Replace [x:R]``(pow ( -1) n)/(INR (fact (mult (S (S O)) n)))*(pow x (mult (S (S O)) n))`` with (mult_fct (fct_cte ``(pow ( -1) n)/(INR (fact (mult (S (S O)) n)))``) (pow_fct (mult (S (S O)) n))); [Idtac | Reflexivity].
Apply continuity_mult.
Apply derivable_continuous; Apply derivable_const.
Apply derivable_continuous; Apply (derivable_pow (mult (2) n)).
Apply CVN_R_CVS; Apply X.
Apply CVN_R_cos; Unfold fn; Reflexivity.
Qed.

(**********)
Lemma continuity_sin : (continuity sin).
Unfold continuity; Intro.
Assert H0 := (continuity_cos ``PI/2-x``).
Unfold continuity_pt in H0; Unfold continue_in in H0; Unfold limit1_in in H0; Unfold limit_in in H0; Simpl in H0; Unfold R_dist in H0; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Elim (H0 ? H); Intros.
Exists x0; Intros.
Elim H1; Intros.
Split.
Assumption.
Intros; Rewrite <- (cos_shift x); Rewrite <- (cos_shift x1); Apply H3.
Elim H4; Intros.
Split.
Unfold D_x no_cond; Split.
Trivial.
Red; Intro; Unfold D_x no_cond in H5; Elim H5; Intros _ H8; Elim H8; Rewrite <- (Ropp_Ropp x); Rewrite <- (Ropp_Ropp x1); Apply eq_Ropp; Apply r_Rplus_plus with ``PI/2``; Apply H7.
Replace ``PI/2-x1-(PI/2-x)`` with ``x-x1``; [Idtac | Ring]; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr3; Apply H6.
Qed.

Lemma CVN_R_sin : (fn:nat->R->R) (fn == [N:nat][x:R]``(pow ( -1) N)/(INR (fact (plus (mult (S (S O)) N) (S O))))*(pow x (mult (S (S O)) N))``) -> (CVN_R fn).
Unfold CVN_R; Unfold CVN_r; Intros fn H r.
Apply Specif.existT with [n:nat]``/(INR (fact (plus (mult (S (S O)) n) (S O))))*(pow r (mult (S (S O)) n))``.
Cut (SigT ? [l:R](Un_cv [n:nat](sum_f_R0 [k:nat](Rabsolu ``/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow r (mult (S (S O)) k))``) n) l)).
Intro; Elim X; Intros.
Apply existTT with x.
Split.
Apply p.
Intros; Rewrite H; Unfold Rdiv; Do 2 Rewrite Rabsolu_mult; Rewrite pow_1_abs; Rewrite Rmult_1l.
Cut ``0</(INR (fact (plus (mult (S (S O)) n) (S O))))``.
Intro; Rewrite (Rabsolu_right  ? (Rle_sym1 ? ? (Rlt_le ? ? H1))).
Apply Rle_monotony.
Left; Apply H1.
Rewrite <- Pow_Rabsolu; Apply pow_maj_Rabs.
Rewrite Rabsolu_Rabsolu; Unfold Boule in H0; Rewrite minus_R0 in H0; Left; Apply H0.
Apply Rlt_Rinv; Apply INR_fact_lt_0.
Cut (r::R)<>``0``.
Intro; Apply Alembert_C2.
Intro; Apply Rabsolu_no_R0.
Apply prod_neq_R0.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Apply pow_nonzero; Assumption.
Assert H1 := Alembert_sin.
Unfold sin_n in H1; Unfold Un_cv in H1; Unfold Un_cv; Intros.
Cut ``0<eps/(Rsqr r)``.
Intro; Elim (H1 ? H3); Intros N0 H4.
Exists N0; Intros.
Unfold R_dist; Assert H6 := (H4 ? H5).
Unfold R_dist in H5; Replace ``(Rabsolu ((Rabsolu (/(INR (fact (plus (mult (S (S O)) (S n)) (S O))))*(pow r (mult (S (S O)) (S n)))))/(Rabsolu (/(INR (fact (plus (mult (S (S O)) n) (S O))))*(pow r (mult (S (S O)) n))))))`` with ``(Rsqr r)*(Rabsolu ((pow ( -1) (S n))/(INR (fact (plus (mult (S (S O)) (S n)) (S O))))/((pow ( -1) n)/(INR (fact (plus (mult (S (S O)) n) (S O)))))))``.
Apply Rlt_monotony_contra with ``/(Rsqr r)``.
Apply Rlt_Rinv; Apply Rsqr_pos_lt; Assumption.
Pattern 1 ``/(Rsqr r)``; Rewrite <- (Rabsolu_right ``/(Rsqr r)``).
Rewrite <- Rabsolu_mult.
Rewrite Rminus_distr.
Rewrite Rmult_Or; Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps).
Apply H6.
Unfold Rsqr; Apply prod_neq_R0; Assumption.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply Rsqr_pos_lt; Assumption.
Unfold Rdiv; Rewrite (Rmult_sym (Rsqr r)); Repeat Rewrite Rabsolu_mult; Rewrite Rabsolu_Rabsolu; Rewrite pow_1_abs.
Rewrite Rmult_1l.
Repeat Rewrite Rmult_assoc; Apply Rmult_mult_r.
Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rinv.
Rewrite pow_1_abs; Rewrite Rinv_R1; Rewrite Rmult_1l.
Rewrite Rinv_Rmult.
Rewrite <- Rabsolu_Rinv.
Rewrite Rinv_Rinv.
Rewrite Rabsolu_mult.
Do 2 Rewrite Rabsolu_Rabsolu.
Rewrite (Rmult_sym ``(Rabsolu (pow r (mult (S (S O)) (S n))))``).
Rewrite Rmult_assoc; Apply Rmult_mult_r.
Rewrite Rabsolu_Rinv.
Rewrite Rabsolu_Rabsolu.
Repeat Rewrite Rabsolu_right.
Replace ``(pow r (mult (S (S O)) (S n)))`` with ``(pow r (mult (S (S O)) n))*r*r``.
Do 2 Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Unfold Rsqr; Ring.
Apply pow_nonzero; Assumption.
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply Rle_sym1; Apply pow_le; Left; Apply (cond_pos r).
Apply Rle_sym1; Apply pow_le; Left; Apply (cond_pos r).
Apply Rabsolu_no_R0; Apply pow_nonzero; Assumption.
Apply INR_fact_neq_0.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Apply Rabsolu_no_R0; Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Apply Rabsolu_no_R0; Apply pow_nonzero; Assumption.
Apply pow_nonzero; DiscrR.
Apply INR_fact_neq_0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rsqr_pos_lt; Assumption].
Assert H0 := (cond_pos r); Red; Intro; Rewrite H1 in H0; Elim (Rlt_antirefl ? H0).
Qed.

(* (sin h)/h -> 1 when h -> 0 *)
Lemma derivable_pt_lim_sin_0 : (derivable_pt_lim sin R0 R1).
Unfold derivable_pt_lim; Intros.
Pose fn := [N:nat][x:R]``(pow ( -1) N)/(INR (fact (plus (mult (S (S O)) N) (S O))))*(pow x (mult (S (S O)) N))``.
Cut (CVN_R fn).
Intro; Cut (x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l)).
Intro cv.
Pose r := (mkposreal ? Rlt_R0_R1).
Cut (CVN_r fn r).
Intro; Cut ((n:nat; y:R)(Boule ``0`` r y)->(continuity_pt (fn n) y)).
Intro; Cut (Boule R0 r R0).
Intro; Assert H2 := (SFL_continuity_pt ? cv ? X0 H0 ? H1).
Unfold continuity_pt in H2; Unfold continue_in in H2; Unfold limit1_in in H2; Unfold limit_in in H2; Simpl in H2; Unfold R_dist in H2.
Elim (H2 ? H); Intros alp H3.
Elim H3; Intros.
Exists (mkposreal ? H4).
Simpl; Intros.
Rewrite sin_0; Rewrite Rplus_Ol; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or.
Cut ``(Rabsolu ((SFL fn cv h)-(SFL fn cv 0))) < eps``.
Intro; Cut (SFL fn cv R0)==R1.
Intro; Cut (SFL fn cv h)==``(sin h)/h``.
Intro; Rewrite H9 in H8; Rewrite H10 in H8.
Apply H8.
Unfold SFL sin.
Case (cv h); Intros.
Case (exist_sin (Rsqr h)); Intros.
Unfold Rdiv; Rewrite (Rinv_r_simpl_m h x0 H6).
EApply UL_sequence.
Apply u.
Unfold sin_in in s; Unfold sin_n infinit_sum in s; Unfold SP fn Un_cv; Intros.
Elim (s ? H10); Intros N0 H11.
Exists N0; Intros.
Unfold R_dist; Unfold R_dist in H11.
Replace (sum_f_R0 [k:nat]``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow h (mult (S (S O)) k))`` n) with (sum_f_R0 [i:nat]``(pow ( -1) i)/(INR (fact (plus (mult (S (S O)) i) (S O))))*(pow (Rsqr h) i)`` n).
Apply H11; Assumption.
Apply sum_eq; Intros; Apply Rmult_mult_r; Unfold Rsqr; Rewrite pow_sqr; Reflexivity.
Unfold SFL sin.
Case (cv R0); Intros.
EApply UL_sequence.
Apply u.
Unfold SP fn; Unfold Un_cv; Intros; Exists (S O); Intros.
Unfold R_dist; Replace (sum_f_R0 [k:nat]``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow 0 (mult (S (S O)) k))`` n) with R1.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Rewrite decomp_sum.
Simpl; Rewrite Rmult_1r; Unfold Rdiv; Rewrite Rinv_R1; Rewrite Rmult_1r; Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rplus_plus_r.
Symmetry; Apply sum_eq_R0; Intros.
Rewrite Rmult_Ol; Rewrite Rmult_Or; Reflexivity.
Unfold ge in H10; Apply lt_le_trans with (1); [Apply lt_n_Sn | Apply H10].
Apply H5.
Split.
Unfold D_x no_cond; Split.
Trivial.
Apply not_sym; Apply H6.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply H7.
Unfold Boule; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_R0; Apply (cond_pos r).
Intros; Unfold fn; Replace [x:R]``(pow ( -1) n)/(INR (fact (plus (mult (S (S O)) n) (S O))))*(pow x (mult (S (S O)) n))`` with (mult_fct (fct_cte ``(pow ( -1) n)/(INR (fact (plus (mult (S (S O)) n) (S O))))``) (pow_fct (mult (S (S O)) n))); [Idtac | Reflexivity].
Apply continuity_pt_mult.
Apply derivable_continuous_pt.
Apply derivable_pt_const.
Apply derivable_continuous_pt.
Apply (derivable_pt_pow (mult (2) n) y).
Apply (X r).
Apply (CVN_R_CVS ? X).
Apply CVN_R_sin; Unfold fn; Reflexivity.
Qed.

(* ((cos h)-1)/h -> 0 when h -> 0 *)
Lemma derivable_pt_lim_cos_0 : (derivable_pt_lim cos ``0`` ``0``).
Unfold derivable_pt_lim; Intros.
Assert H0 := derivable_pt_lim_sin_0.
Unfold derivable_pt_lim in H0.
Cut ``0<eps/2``.
Intro; Elim (H0 ? H1); Intros del H2.
Cut (continuity_pt sin ``0``).
Intro; Unfold continuity_pt in H3; Unfold continue_in in H3; Unfold limit1_in in H3; Unfold limit_in in H3; Simpl in H3; Unfold R_dist in H3.
Cut ``0<eps/2``; [Intro | Assumption].
Elim (H3 ? H4); Intros del_c H5.
Cut ``0<(Rmin del del_c)``.
Intro; Pose delta := (mkposreal ? H6).
Exists delta; Intros.
Rewrite Rplus_Ol; Replace ``((cos h)-(cos 0))`` with ``-2*(Rsqr (sin (h/2)))``.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or.
Unfold Rdiv; Do 2 Rewrite Ropp_mul1.
Rewrite Rabsolu_Ropp.
Replace ``2*(Rsqr (sin (h*/2)))*/h`` with ``(sin (h/2))*((sin (h/2))/(h/2)-1)+(sin (h/2))``.
Apply Rle_lt_trans with ``(Rabsolu ((sin (h/2))*((sin (h/2))/(h/2)-1)))+(Rabsolu ((sin (h/2))))``.
Apply Rabsolu_triang.
Rewrite (double_var eps); Apply Rplus_lt.
Apply Rle_lt_trans with ``(Rabsolu ((sin (h/2))/(h/2)-1))``.
Rewrite Rabsolu_mult; Rewrite Rmult_sym; Pattern 2 ``(Rabsolu ((sin (h/2))/(h/2)-1))``; Rewrite <- Rmult_1r; Apply Rle_monotony.
Apply Rabsolu_pos.
Assert H9 := (SIN_bound ``h/2``).
Unfold Rabsolu; Case (case_Rabsolu ``(sin (h/2))``); Intro.
Pattern 3 R1; Rewrite <- (Ropp_Ropp ``1``).
Apply Rle_Ropp1.
Elim H9; Intros; Assumption.
Elim H9; Intros; Assumption.
Cut ``(Rabsolu (h/2))<del``.
Intro; Cut ``h/2<>0``.
Intro; Assert H11 := (H2 ? H10 H9). 
Rewrite Rplus_Ol in H11; Rewrite sin_0 in H11.
Rewrite minus_R0 in H11; Apply H11.
Unfold Rdiv; Apply prod_neq_R0.
Apply H7.
Apply Rinv_neq_R0; DiscrR.
Apply Rlt_trans with ``del/2``.
Unfold Rdiv; Rewrite Rabsolu_mult.
Rewrite (Rabsolu_right ``/2``).
Do 2 Rewrite <- (Rmult_sym ``/2``); Apply Rlt_monotony.
Apply Rlt_Rinv; Sup0.
Apply Rlt_le_trans with (pos delta).
Apply H8.
Unfold delta; Simpl; Apply Rmin_l.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Sup0.
Rewrite <- (Rplus_Or ``del/2``); Pattern 1 del; Rewrite (double_var del); Apply Rlt_compatibility; Unfold Rdiv; Apply Rmult_lt_pos.
Apply (cond_pos del).
Apply Rlt_Rinv; Sup0.
Elim H5; Intros; Assert H11 := (H10 ``h/2``).
Rewrite sin_0 in H11; Do 2 Rewrite minus_R0 in H11.
Apply H11.
Split.
Unfold D_x no_cond; Split.
Trivial.
Apply not_sym; Unfold Rdiv; Apply prod_neq_R0.
Apply H7.
Apply Rinv_neq_R0; DiscrR.
Apply Rlt_trans with ``del_c/2``.
Unfold Rdiv; Rewrite Rabsolu_mult.
Rewrite (Rabsolu_right ``/2``).
Do 2 Rewrite <- (Rmult_sym ``/2``).
Apply Rlt_monotony.
Apply Rlt_Rinv; Sup0.
Apply Rlt_le_trans with (pos delta).
Apply H8.
Unfold delta; Simpl; Apply Rmin_r.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Sup0.
Rewrite <- (Rplus_Or ``del_c/2``); Pattern 2 del_c; Rewrite (double_var del_c); Apply Rlt_compatibility.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply H9.
Apply Rlt_Rinv; Sup0.
Rewrite Rminus_distr; Rewrite Rmult_1r; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Rewrite (Rmult_sym ``2``); Unfold Rdiv Rsqr.
Repeat Rewrite Rmult_assoc.
Repeat Apply Rmult_mult_r.
Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Apply Rmult_sym.
DiscrR.
Apply H7.
Apply Rinv_neq_R0; DiscrR.
Pattern 2 h; Replace h with ``2*(h/2)``.
Rewrite (cos_2a_sin ``h/2``).
Rewrite cos_0; Unfold Rsqr; Ring.
Unfold Rdiv; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
DiscrR.
Unfold Rmin; Case (total_order_Rle del del_c); Intro.
Apply (cond_pos del).
Elim H5; Intros; Assumption.
Apply continuity_sin.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Qed.

(**********)
Theorem derivable_pt_lim_sin : (x:R)(derivable_pt_lim sin x (cos x)).
Intro; Assert H0 := derivable_pt_lim_sin_0.
Assert H := derivable_pt_lim_cos_0.
Unfold derivable_pt_lim in H0 H.
Unfold derivable_pt_lim; Intros.
Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Apply H1 | Apply Rlt_Rinv; Sup0]].
Elim (H0 ? H2); Intros alp1 H3.
Elim (H ? H2); Intros alp2 H4.
Pose alp := (Rmin alp1 alp2).
Cut ``0<alp``.
Intro; Exists (mkposreal ? H5); Intros.
Replace ``((sin (x+h))-(sin x))/h-(cos x)`` with ``(sin x)*((cos h)-1)/h+(cos x)*((sin h)/h-1)``.
Apply Rle_lt_trans with ``(Rabsolu ((sin x)*((cos h)-1)/h))+(Rabsolu ((cos x)*((sin h)/h-1)))``.
Apply Rabsolu_triang.
Rewrite (double_var eps); Apply Rplus_lt.
Apply Rle_lt_trans with ``(Rabsolu ((cos h)-1)/h)``.
Rewrite Rabsolu_mult; Rewrite Rmult_sym; Pattern 2 ``(Rabsolu (((cos h)-1)/h))``; Rewrite <- Rmult_1r; Apply Rle_monotony.
Apply Rabsolu_pos.
Assert H8 := (SIN_bound x); Elim H8; Intros.
Unfold Rabsolu; Case (case_Rabsolu (sin x)); Intro.
Rewrite <- (Ropp_Ropp R1).
Apply Rle_Ropp1; Assumption.
Assumption.
Cut ``(Rabsolu h)<alp2``.
Intro; Assert H9 := (H4 ? H6 H8).
Rewrite cos_0 in H9; Rewrite Rplus_Ol in H9; Rewrite minus_R0 in H9; Apply H9.
Apply Rlt_le_trans with alp.
Apply H7.
Unfold alp; Apply Rmin_r.
Apply Rle_lt_trans with ``(Rabsolu ((sin h)/h-1))``.
Rewrite Rabsolu_mult; Rewrite Rmult_sym; Pattern 2 ``(Rabsolu ((sin h)/h-1))``; Rewrite <- Rmult_1r; Apply Rle_monotony.
Apply Rabsolu_pos.
Assert H8 := (COS_bound x); Elim H8; Intros.
Unfold Rabsolu; Case (case_Rabsolu (cos x)); Intro.
Rewrite <- (Ropp_Ropp R1); Apply Rle_Ropp1; Assumption.
Assumption.
Cut ``(Rabsolu h)<alp1``.
Intro; Assert H9 := (H3 ? H6 H8).
Rewrite sin_0 in H9; Rewrite Rplus_Ol in H9; Rewrite minus_R0 in H9; Apply H9.
Apply Rlt_le_trans with alp.
Apply H7.
Unfold alp; Apply Rmin_l.
Rewrite sin_plus; Unfold Rminus Rdiv; Repeat Rewrite Rmult_Rplus_distrl; Repeat Rewrite Rmult_Rplus_distr; Repeat Rewrite Rmult_assoc; Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Rewrite (Rplus_sym ``(sin x)*( -1*/h)``); Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Rewrite Ropp_mul3; Rewrite Ropp_mul1; Rewrite Rmult_1r; Rewrite Rmult_1l; Rewrite Ropp_mul3; Rewrite <- Ropp_mul1; Apply Rplus_sym.
Unfold alp; Unfold Rmin; Case (total_order_Rle alp1 alp2); Intro.
Apply (cond_pos alp1).
Apply (cond_pos alp2).
Qed.

Lemma derivable_pt_lim_cos : (x:R) (derivable_pt_lim cos x ``-(sin x)``).
Intro; Cut (h:R)``(sin (h+PI/2))``==(cos h).
Intro; Replace ``-(sin x)`` with (Rmult (cos ``x+PI/2``) (Rplus R1 R0)).
Generalize (derivable_pt_lim_comp (plus_fct id (fct_cte ``PI/2``)) sin); Intros.
Cut (derivable_pt_lim (plus_fct id (fct_cte ``PI/2``)) x ``1+0``).
Cut (derivable_pt_lim sin (plus_fct id (fct_cte ``PI/2``) x) ``(cos (x+PI/2))``).
Intros; Generalize (H0 ? ? ? H2 H1); Replace (comp sin (plus_fct id (fct_cte ``PI/2``))) with [x:R]``(sin (x+PI/2))``; [Idtac | Reflexivity].
Unfold derivable_pt_lim; Intros.
Elim (H3 eps H4); Intros.
Exists x0.
Intros; Rewrite <- (H ``x+h``); Rewrite <- (H x); Apply H5; Assumption.
Apply derivable_pt_lim_sin.
Apply derivable_pt_lim_plus.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Rewrite sin_cos; Rewrite <- (Rplus_sym x); Ring.
Intro; Rewrite cos_sin; Rewrite Rplus_sym; Reflexivity.
Qed.

Lemma derivable_pt_sin : (x:R) (derivable_pt sin x).
Unfold derivable_pt; Intro.
Apply Specif.existT with (cos x).
Apply derivable_pt_lim_sin.
Qed.

Lemma derivable_pt_cos : (x:R) (derivable_pt cos x).
Unfold derivable_pt; Intro.
Apply Specif.existT with ``-(sin x)``.
Apply derivable_pt_lim_cos.
Qed.

Lemma derivable_sin : (derivable sin).
Unfold derivable; Intro; Apply derivable_pt_sin.
Qed.

Lemma derivable_cos : (derivable cos).
Unfold derivable; Intro; Apply derivable_pt_cos.
Qed.

Lemma derive_pt_sin : (x:R) ``(derive_pt sin x (derivable_pt_sin ?))==(cos x)``.
Intros; Apply derive_pt_eq_0.
Apply derivable_pt_lim_sin.
Qed.

Lemma derive_pt_cos : (x:R) ``(derive_pt cos x (derivable_pt_cos ?))==-(sin x)``.
Intros; Apply derive_pt_eq_0.
Apply derivable_pt_lim_cos.
Qed.
