(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Sumbool.
Require Rbase.
Require Rfunctions.
Require SeqSeries.
Require Ranalysis1.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Fixpoint Dichotomy_lb [x,y:R;P:R->bool;N:nat] : R :=
Cases N of 
  O => x
| (S n) => let down = (Dichotomy_lb x y P n) in let up = (Dichotomy_ub x y P n) in let z = ``(down+up)/2``  in if (P z) then down else z
end
with Dichotomy_ub [x,y:R;P:R->bool;N:nat] : R :=
Cases N of 
  O => y
| (S n) => let down = (Dichotomy_lb x y P n) in let up = (Dichotomy_ub x y P n) in let z = ``(down+up)/2``  in if (P z) then z else up
end.

Definition dicho_lb [x,y:R;P:R->bool] : nat->R := [N:nat](Dichotomy_lb x y P N).
Definition dicho_up [x,y:R;P:R->bool] : nat->R := [N:nat](Dichotomy_ub x y P N).

(**********)
Lemma dicho_comp : (x,y:R;P:R->bool;n:nat) ``x<=y`` -> ``(dicho_lb x y P n)<=(dicho_up x y P n)``.
Intros.
Induction n.
Simpl; Assumption.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 1 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Rewrite double.
Apply Rle_compatibility.
Assumption.
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 3 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Rewrite double.
Rewrite <- (Rplus_sym (Dichotomy_ub x y P n)).
Apply Rle_compatibility.
Assumption.
Qed.

Lemma dicho_lb_growing : (x,y:R;P:R->bool) ``x<=y`` -> (Un_growing (dicho_lb x y P)).
Intros.
Unfold Un_growing.
Intro.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Right; Reflexivity.
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 1 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Rewrite double.
Apply Rle_compatibility.
Replace (Dichotomy_ub x y P n) with (dicho_up x y P n); [Apply dicho_comp; Assumption | Reflexivity].
Qed.

Lemma dicho_up_decreasing : (x,y:R;P:R->bool) ``x<=y`` -> (Un_decreasing (dicho_up x y P)).
Intros.
Unfold Un_decreasing.
Intro.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 3 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Rewrite double.
Replace (Dichotomy_ub x y P n) with (dicho_up x y P n); [Idtac | Reflexivity].
Replace (Dichotomy_lb x y P n) with (dicho_lb x y P n); [Idtac | Reflexivity].
Rewrite <- (Rplus_sym ``(dicho_up x y P n)``).
Apply Rle_compatibility.
Apply dicho_comp; Assumption.
Right; Reflexivity.
Qed.

Lemma dicho_lb_maj_y : (x,y:R;P:R->bool) ``x<=y`` -> (n:nat)``(dicho_lb x y P n)<=y``.
Intros.
Induction n.
Simpl; Assumption.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Assumption.
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 3 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Rewrite Rmult_1r | DiscrR].
Rewrite double; Apply Rplus_le.
Assumption.
Pattern 2 y; Replace y with (Dichotomy_ub x y P O); [Idtac | Reflexivity].
Apply decreasing_prop.
Assert H0 := (dicho_up_decreasing x y P H).
Assumption.
Apply le_O_n.
Qed.

Lemma dicho_lb_maj : (x,y:R;P:R->bool) ``x<=y`` -> (has_ub (dicho_lb x y P)).
Intros.
Cut (n:nat)``(dicho_lb x y P n)<=y``.
Intro.
Unfold has_ub.
Unfold bound.
Exists y.
Unfold is_upper_bound.
Intros.
Elim H1; Intros.
Rewrite H2; Apply H0.
Apply dicho_lb_maj_y; Assumption.
Qed.

Lemma dicho_up_min_x : (x,y:R;P:R->bool) ``x<=y`` -> (n:nat)``x<=(dicho_up x y P n)``.
Intros.
Induction n.
Simpl; Assumption.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Sup0.
Pattern 1 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Rewrite Rmult_1r | DiscrR].
Rewrite double; Apply Rplus_le.
Pattern 1 x; Replace x with (Dichotomy_lb x y P O); [Idtac | Reflexivity].
Apply tech9.
Assert H0 := (dicho_lb_growing x y P H).
Assumption.
Apply le_O_n.
Assumption.
Assumption.
Qed.

Lemma dicho_up_min : (x,y:R;P:R->bool) ``x<=y`` -> (has_lb (dicho_up x y P)).
Intros.
Cut (n:nat)``x<=(dicho_up x y P n)``.
Intro.
Unfold has_lb.
Unfold bound.
Exists ``-x``.
Unfold is_upper_bound.
Intros.
Elim H1; Intros.
Rewrite H2.
Unfold opp_seq.
Apply Rle_Ropp1.
Apply H0.
Apply dicho_up_min_x; Assumption.
Qed.

Lemma dicho_lb_cv : (x,y:R;P:R->bool) ``x<=y`` -> (sigTT R [l:R](Un_cv (dicho_lb x y P) l)).
Intros.
Apply growing_cv.
Apply dicho_lb_growing; Assumption.
Apply dicho_lb_maj; Assumption.
Qed.

Lemma dicho_up_cv : (x,y:R;P:R->bool) ``x<=y`` -> (sigTT R [l:R](Un_cv (dicho_up x y P) l)).
Intros.
Apply decreasing_cv.
Apply dicho_up_decreasing; Assumption.
Apply dicho_up_min; Assumption.
Qed.

Lemma dicho_lb_dicho_up : (x,y:R;P:R->bool;n:nat) ``x<=y`` -> ``(dicho_up x y P n)-(dicho_lb x y P n)==(y-x)/(pow 2 n)``.
Intros.
Induction n.
Simpl.
Unfold Rdiv; Rewrite Rinv_R1; Ring.
Simpl.
Case (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``).
Unfold Rdiv.
Replace ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))*/2-
   (Dichotomy_lb x y P n)`` with ``((dicho_up x y P n)-(dicho_lb x y P n))/2``.
Unfold Rdiv; Rewrite Hrecn.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Ring.
DiscrR.
Apply pow_nonzero; DiscrR.
Pattern 2 (Dichotomy_lb x y P n); Rewrite (double_var (Dichotomy_lb x y P n)); Unfold dicho_up dicho_lb Rminus Rdiv; Ring.
Replace ``(Dichotomy_ub x y P n)-((Dichotomy_lb x y P n)+
   (Dichotomy_ub x y P n))/2`` with ``((dicho_up x y P n)-(dicho_lb x y P n))/2``.
Unfold Rdiv; Rewrite Hrecn.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Ring.
DiscrR.
Apply pow_nonzero; DiscrR.
Pattern 1 (Dichotomy_ub x y P n); Rewrite (double_var (Dichotomy_ub x y P n)); Unfold dicho_up dicho_lb Rminus Rdiv; Ring.
Qed.

Definition pow_2_n := [n:nat](pow ``2`` n).

Lemma pow_2_n_neq_R0 : (n:nat) ``(pow_2_n n)<>0``.
Intro.
Unfold pow_2_n.
Apply pow_nonzero.
DiscrR.
Qed.

Lemma pow_2_n_growing : (Un_growing pow_2_n).
Unfold Un_growing.
Intro.
Replace (S n) with (plus n (1)); [Unfold pow_2_n; Rewrite pow_add | Ring].
Pattern 1 (pow ``2`` n); Rewrite <- Rmult_1r.
Apply Rle_monotony.
Left; Apply pow_lt; Sup0.
Simpl.
Rewrite Rmult_1r.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply Rlt_R0_R1.
Qed.

Lemma pow_2_n_infty : (cv_infty pow_2_n).
Cut (N:nat)``(INR N)<=(pow 2 N)``.
Intros.
Unfold cv_infty.
Intro.
Case (total_order_T R0 M); Intro.
Elim s; Intro.
Pose N := (up M).
Cut `0<=N`.
Intro.
Elim (IZN N H0); Intros N0 H1.
Exists N0.
Intros.
Apply Rlt_le_trans with (INR N0).
Rewrite INR_IZR_INZ.
Rewrite <- H1.
Unfold N.
Assert H3 := (archimed M).
Elim H3; Intros; Assumption.
Apply Rle_trans with (pow_2_n N0).
Unfold pow_2_n; Apply H.
Apply Rle_sym2.
Apply growing_prop.
Apply pow_2_n_growing.
Assumption.
Apply le_IZR.
Unfold N.
Simpl.
Assert H0 := (archimed M); Elim H0; Intros.
Left; Apply Rlt_trans with M; Assumption.
Exists O; Intros.
Rewrite <- b.
Unfold pow_2_n; Apply pow_lt; Sup0.
Exists O; Intros.
Apply Rlt_trans with R0.
Assumption.
Unfold pow_2_n; Apply pow_lt; Sup0.
Induction N.
Simpl.
Left; Apply Rlt_R0_R1.
Intros.
Pattern 2 (S n); Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite S_INR; Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Apply Rle_trans with ``(pow 2 n)``.
Rewrite <- (Rplus_sym R1).
Rewrite <- (Rmult_1r (INR n)).
Apply (poly n R1).
Apply Rlt_R0_R1.
Pattern 1 (pow ``2`` n); Rewrite <- Rplus_Or.
Rewrite <- (Rmult_sym ``2``).
Rewrite double.
Apply Rle_compatibility.
Left; Apply pow_lt; Sup0.
Qed.

Lemma cv_dicho : (x,y,l1,l2:R;P:R->bool) ``x<=y`` -> (Un_cv (dicho_lb x y P) l1) -> (Un_cv (dicho_up x y P) l2) -> l1==l2.
Intros.
Assert H2 := (CV_minus ? ? ? ? H0 H1).
Cut (Un_cv [i:nat]``(dicho_lb x y P i)-(dicho_up x y P i)`` R0).
Intro.
Assert H4 := (UL_sequence ? ? ? H2 H3).
Symmetry; Apply Rminus_eq_right; Assumption.
Unfold Un_cv; Unfold R_dist.
Intros.
Assert H4 := (cv_infty_cv_R0 pow_2_n pow_2_n_neq_R0 pow_2_n_infty).
Case (total_order_T x y); Intro.
Elim s; Intro.
Unfold Un_cv in H4; Unfold R_dist in H4.
Cut ``0<y-x``.
Intro Hyp.
Cut ``0<eps/(y-x)``.
Intro.
Elim (H4 ``eps/(y-x)`` H5); Intros N H6.
Exists N; Intros.
Replace ``(dicho_lb x y P n)-(dicho_up x y P n)-0`` with ``(dicho_lb x y P n)-(dicho_up x y P n)``; [Idtac | Ring].
Rewrite <- Rabsolu_Ropp.
Rewrite Ropp_distr3.
Rewrite dicho_lb_dicho_up.
Unfold Rdiv; Rewrite Rabsolu_mult.
Rewrite (Rabsolu_right ``y-x``).
Apply Rlt_monotony_contra with ``/(y-x)``.
Apply Rlt_Rinv; Assumption.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace ``/(pow 2 n)`` with ``/(pow 2 n)-0``; [Unfold pow_2_n Rdiv in H6; Rewrite <- (Rmult_sym eps); Apply H6; Assumption | Ring].
Red; Intro; Rewrite H8 in Hyp; Elim (Rlt_antirefl ? Hyp).
Apply Rle_sym1.
Apply Rle_anti_compatibility with x; Rewrite Rplus_Or.
Replace ``x+(y-x)`` with y; [Assumption | Ring].
Assumption.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Assumption].
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or.
Replace ``x+(y-x)`` with y; [Assumption | Ring].
Exists O; Intros.
Replace ``(dicho_lb x y P n)-(dicho_up x y P n)-0`` with ``(dicho_lb x y P n)-(dicho_up x y P n)``; [Idtac | Ring].
Rewrite <- Rabsolu_Ropp.
Rewrite Ropp_distr3.
Rewrite dicho_lb_dicho_up.
Rewrite b.
Unfold Rminus Rdiv; Rewrite Rplus_Ropp_r; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Assumption.
Assumption.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Qed.

Definition cond_positivity [x:R] : bool := Cases (total_order_Rle R0 x) of 
  (leftT _) => true 
| (rightT _) => false end.

(* Sequential caracterisation of continuity *)
Lemma continuity_seq : (f:R->R;Un:nat->R;l:R) (continuity_pt f l) -> (Un_cv Un l) -> (Un_cv [i:nat](f (Un i)) (f l)).
Unfold continuity_pt Un_cv; Unfold continue_in.
Unfold limit1_in.
Unfold limit_in.
Unfold dist.
Simpl.
Unfold R_dist.
Intros.
Elim (H eps H1); Intros alp H2.
Elim H2; Intros.
Elim (H0 alp H3); Intros N H5.
Exists N; Intros.
Case (Req_EM (Un n) l); Intro.
Rewrite H7; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Apply H4.
Split.
Unfold D_x no_cond.
Split.
Trivial.
Apply not_sym; Assumption.
Apply H5; Assumption.
Qed.

Lemma dicho_lb_car : (x,y:R;P:R->bool;n:nat) (P x)=false -> (P (dicho_lb x y P n))=false.
Intros.
Induction n.
Simpl.
Assumption.
Simpl.
Assert X := (sumbool_of_bool (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``)).
Elim X; Intro.
Rewrite a.
Unfold dicho_lb in Hrecn; Assumption.
Rewrite b.
Assumption.
Qed.

Lemma dicho_up_car : (x,y:R;P:R->bool;n:nat) (P y)=true -> (P (dicho_up x y P n))=true.
Intros.
Induction n.
Simpl.
Assumption.
Simpl.
Assert X := (sumbool_of_bool (P ``((Dichotomy_lb x y P n)+(Dichotomy_ub x y P n))/2``)).
Elim X; Intro.
Rewrite a.
Unfold dicho_lb in Hrecn; Assumption.
Rewrite b.
Assumption.
Qed.

(* Intermediate Value Theorem *)
Lemma IVT : (f:R->R;x,y:R) (continuity f) -> ``x<y`` -> ``(f x)<0`` -> ``0<(f y)`` -> (sigTT R [z:R]``x<=z<=y``/\``(f z)==0``).
Intros.
Cut ``x<=y``.
Intro.
Generalize (dicho_lb_cv x y [z:R](cond_positivity (f z)) H3). 
Generalize (dicho_up_cv x y [z:R](cond_positivity (f z)) H3). 
Intros.
Elim X; Intros.
Elim X0; Intros.
Assert H4 := (cv_dicho ? ? ? ? ? H3 p0 p).
Rewrite H4 in p0.
Apply existTT with x0.
Split.
Split.
Apply Rle_trans with (dicho_lb x y [z:R](cond_positivity (f z)) O).
Simpl.
Right; Reflexivity.
Apply growing_ineq.
Apply dicho_lb_growing; Assumption.
Assumption.
Apply Rle_trans with (dicho_up x y [z:R](cond_positivity (f z)) O).
Apply decreasing_ineq.
Apply dicho_up_decreasing; Assumption.
Assumption.
Right; Reflexivity.
2:Left; Assumption.
Pose Vn := [n:nat](dicho_lb x y [z:R](cond_positivity (f z)) n).
Pose Wn := [n:nat](dicho_up x y [z:R](cond_positivity (f z)) n).
Cut ((n:nat)``(f (Vn n))<=0``)->``(f x0)<=0``.
Cut ((n:nat)``0<=(f (Wn n))``)->``0<=(f x0)``.
Intros.
Cut (n:nat)``(f (Vn n))<=0``.
Cut (n:nat)``0<=(f (Wn n))``.
Intros.
Assert H9 := (H6 H8).
Assert H10 := (H5 H7).
Apply Rle_antisym; Assumption.
Intro.
Unfold Wn.
Cut (z:R) (cond_positivity z)=true <-> ``0<=z``.
Intro.
Assert H8 := (dicho_up_car x y [z:R](cond_positivity (f z)) n).
Elim (H7 (f (dicho_up x y [z:R](cond_positivity (f z)) n))); Intros.
Apply H9.
Apply H8.
Elim (H7 (f y)); Intros.
Apply H12.
Left; Assumption.
Intro.
Unfold cond_positivity.
Case (total_order_Rle R0 z); Intro.
Split.
Intro; Assumption.
Intro; Reflexivity.
Split.
Intro; Elim diff_false_true; Assumption.
Intro.
Elim n0; Assumption.
Unfold Vn.
Cut (z:R) (cond_positivity z)=false <-> ``z<0``.
Intros.
Assert H8 := (dicho_lb_car x y [z:R](cond_positivity (f z)) n).
Left.
Elim (H7 (f (dicho_lb x y [z:R](cond_positivity (f z)) n))); Intros.
Apply H9.
Apply H8.
Elim (H7 (f x)); Intros.
Apply H12.
Assumption.
Intro.
Unfold cond_positivity.
Case (total_order_Rle R0 z); Intro.
Split.
Intro; Elim diff_true_false; Assumption.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H7)).
Split.
Intro; Auto with real.
Intro; Reflexivity.
Cut (Un_cv Wn x0).
Intros.
Assert H7 := (continuity_seq f Wn x0 (H x0) H5).
Case (total_order_T R0 (f x0)); Intro.
Elim s; Intro.
Left; Assumption.
Rewrite <- b; Right; Reflexivity.
Unfold Un_cv in H7; Unfold R_dist in H7.
Cut ``0< -(f x0)``.
Intro.
Elim (H7 ``-(f x0)`` H8); Intros.
Cut (ge x2 x2); [Intro | Unfold ge; Apply le_n].
Assert H11 := (H9 x2 H10).
Rewrite Rabsolu_right in H11.
Pattern 1 ``-(f x0)`` in H11; Rewrite <- Rplus_Or in H11.
Unfold Rminus in H11; Rewrite (Rplus_sym (f (Wn x2))) in H11.
Assert H12 := (Rlt_anti_compatibility ? ? ? H11).
Assert H13 := (H6 x2).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H13 H12)).
Apply Rle_sym1; Left; Unfold Rminus; Apply ge0_plus_gt0_is_gt0.
Apply H6.
Exact H8.
Apply Rgt_RO_Ropp; Assumption.
Unfold Wn; Assumption.
Cut (Un_cv Vn x0).
Intros.
Assert H7 := (continuity_seq f Vn x0 (H x0) H5).
Case (total_order_T R0 (f x0)); Intro.
Elim s; Intro.
Unfold Un_cv in H7; Unfold R_dist in H7.
Elim (H7 ``(f x0)`` a); Intros.
Cut (ge x2 x2); [Intro | Unfold ge; Apply le_n].
Assert H10 := (H8 x2 H9).
Rewrite Rabsolu_left in H10.
Pattern 2 ``(f x0)`` in H10; Rewrite <- Rplus_Or in H10.
Rewrite Ropp_distr3 in H10.
Unfold Rminus in H10.
Assert H11 := (Rlt_anti_compatibility ? ? ? H10).
Assert H12 := (H6 x2).
Cut ``0<(f (Vn x2))``.
Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H13 H12)).
Rewrite <- (Ropp_Ropp (f (Vn x2))).
Apply Rgt_RO_Ropp; Assumption.
Apply Rlt_anti_compatibility with ``(f x0)-(f (Vn x2))``.
Rewrite Rplus_Or; Replace ``(f x0)-(f (Vn x2))+((f (Vn x2))-(f x0))`` with R0; [Unfold Rminus; Apply gt0_plus_ge0_is_gt0 | Ring].
Assumption.
Apply Rge_RO_Ropp; Apply Rle_sym1; Apply H6.
Right; Rewrite <- b; Reflexivity.
Left; Assumption.
Unfold Vn; Assumption.
Qed.

Lemma IVT_cor : (f:R->R;x,y:R) (continuity f) -> ``x<=y`` -> ``(f x)*(f y)<=0`` -> (sigTT R [z:R]``x<=z<=y``/\``(f z)==0``).
Intros.
Case (total_order_T R0 (f x)); Intro.
Case (total_order_T R0 (f y)); Intro.
Elim s; Intro.
Elim s0; Intro.
Cut ``0<(f x)*(f y)``; [Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 H2)) | Apply Rmult_lt_pos; Assumption].
Exists y.
Split.
Split; [Assumption | Right; Reflexivity].
Symmetry; Exact b.
Exists x.
Split.
Split; [Right; Reflexivity | Assumption].
Symmetry; Exact b.
Elim s; Intro.
Cut ``x<y``.
Intro.
Assert H3 := (IVT (opp_fct f) x y (continuity_opp f H) H2).
Cut ``(opp_fct f x)<0``.
Cut ``0<(opp_fct f y)``.
Intros.
Elim (H3 H5 H4); Intros.
Apply existTT with x0.
Elim p; Intros.
Split.
Assumption.
Unfold opp_fct in H7.
Rewrite <- (Ropp_Ropp (f x0)).
Apply eq_RoppO; Assumption.
Unfold opp_fct; Apply Rgt_RO_Ropp; Assumption.
Unfold opp_fct.
Apply Rlt_anti_compatibility with (f x); Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Assumption.
Inversion H0.
Assumption.
Rewrite H2 in a.
Elim (Rlt_antirefl ? (Rlt_trans ? ? ? r a)).
Apply existTT with x.
Split.
Split; [Right; Reflexivity | Assumption].
Symmetry; Assumption.
Case (total_order_T R0 (f y)); Intro.
Elim s; Intro.
Cut ``x<y``.
Intro.
Apply IVT; Assumption.
Inversion H0.
Assumption.
Rewrite H2 in r.
Elim (Rlt_antirefl ? (Rlt_trans ? ? ? r a)).
Apply existTT with y.
Split.
Split; [Assumption | Right; Reflexivity].
Symmetry; Assumption.
Cut ``0<(f x)*(f y)``.
Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H2 H1)).
Rewrite <- Ropp_mul2; Apply Rmult_lt_pos; Apply Rgt_RO_Ropp; Assumption.
Qed.

(* We can now define the square root function as the reciprocal transformation of the square root function *)
Lemma Rsqrt_exists : (y:R) ``0<=y`` -> (sigTT R [z:R]``0<=z``/\``y==(Rsqr z)``).
Intros.
Pose f := [x:R]``(Rsqr x)-y``.
Cut ``(f 0)<=0``.
Intro.
Cut (continuity f).
Intro.
Case (total_order_T y R1); Intro.
Elim s; Intro.
Cut ``0<=(f 1)``.
Intro.
Cut ``(f 0)*(f 1)<=0``.
Intro.
Assert X := (IVT_cor f R0 R1 H1 (Rlt_le ? ? Rlt_R0_R1) H3).
Elim X; Intros t H4.
Apply existTT with t.
Elim H4; Intros.
Split.
Elim H5; Intros; Assumption.
Unfold f in H6.
Apply Rminus_eq_right; Exact H6.
Rewrite Rmult_sym; Pattern 2 R0; Rewrite <- (Rmult_Or (f R1)).
Apply Rle_monotony; Assumption.
Unfold f.
Rewrite Rsqr_1.
Apply Rle_anti_compatibility with y.
Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Left; Assumption.
Apply existTT with R1.
Split.
Left; Apply Rlt_R0_R1.
Rewrite b; Symmetry; Apply Rsqr_1.
Cut ``0<=(f y)``.
Intro.
Cut ``(f 0)*(f y)<=0``.
Intro.
Assert X := (IVT_cor f R0 y H1 H H3).
Elim X; Intros t H4.
Apply existTT with t.
Elim H4; Intros.
Split.
Elim H5; Intros; Assumption.
Unfold f in H6.
Apply Rminus_eq_right; Exact H6.
Rewrite Rmult_sym; Pattern 2 R0; Rewrite <- (Rmult_Or (f y)).
Apply Rle_monotony; Assumption.
Unfold f.
Apply Rle_anti_compatibility with y.
Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Pattern 1 y; Rewrite <- Rmult_1r.
Unfold Rsqr; Apply Rle_monotony.
Assumption.
Left; Exact r.
Replace f with (minus_fct Rsqr (fct_cte y)).
Apply continuity_minus.
Apply derivable_continuous; Apply derivable_Rsqr.
Apply derivable_continuous; Apply derivable_const.
Reflexivity.
Unfold f; Rewrite Rsqr_O.
Unfold Rminus; Rewrite Rplus_Ol.
Apply Rle_sym2.
Apply Rle_RO_Ropp; Assumption.
Qed.

(* Definition of the square root: R+->R *)
Definition Rsqrt [y:nonnegreal] : R := Cases (Rsqrt_exists (nonneg y) (cond_nonneg y)) of (existTT a b) => a end.

(**********)
Lemma Rsqrt_positivity : (x:nonnegreal) ``0<=(Rsqrt x)``.
Intro.
Assert X := (Rsqrt_exists (nonneg x) (cond_nonneg x)).
Elim X; Intros.
Cut x0==(Rsqrt x).
Intros.
Elim p; Intros.
Rewrite H in H0; Assumption.
Unfold Rsqrt.
Case (Rsqrt_exists x (cond_nonneg x)).
Intros.
Elim p; Elim a; Intros.
Apply Rsqr_inj.
Assumption.
Assumption.
Rewrite <- H0; Rewrite <- H2; Reflexivity.
Qed.

(**********)
Lemma Rsqrt_Rsqrt : (x:nonnegreal) ``(Rsqrt x)*(Rsqrt x)==x``.
Intros.
Assert X := (Rsqrt_exists (nonneg x) (cond_nonneg x)).
Elim X; Intros.
Cut x0==(Rsqrt x).
Intros.
Rewrite <- H.
Elim p; Intros.
Rewrite H1; Reflexivity.
Unfold Rsqrt.
Case (Rsqrt_exists x (cond_nonneg x)).
Intros.
Elim p; Elim a; Intros.
Apply Rsqr_inj.
Assumption.
Assumption.
Rewrite <- H0; Rewrite <- H2; Reflexivity.
Qed.
