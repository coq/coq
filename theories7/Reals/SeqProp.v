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
Require Rseries.
Require Classical.
Require Max.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Definition Un_decreasing [Un:nat->R] : Prop := (n:nat) (Rle (Un (S n)) (Un n)).
Definition opp_seq [Un:nat->R] : nat->R := [n:nat]``-(Un n)``.
Definition has_ub [Un:nat->R] : Prop := (bound (EUn Un)).
Definition has_lb [Un:nat->R] : Prop := (bound (EUn (opp_seq Un))).

(**********)
Lemma growing_cv : (Un:nat->R) (Un_growing Un) -> (has_ub Un) -> (sigTT R [l:R](Un_cv Un l)).
Unfold Un_growing Un_cv;Intros; 
 NewDestruct (complet (EUn Un) H0 (EUn_noempty Un)) as [x [H2 H3]].
 Exists x;Intros eps H1.
 Unfold is_upper_bound in H2 H3.
Assert H5:(n:nat)(Rle (Un n) x).
  Intro n; Apply (H2 (Un n) (Un_in_EUn Un n)).
Cut (Ex [N:nat] (Rlt (Rminus x eps) (Un N))).
Intro H6;NewDestruct H6 as [N H6];Exists N.
Intros n H7;Unfold R_dist;Apply (Rabsolu_def1 (Rminus (Un n) x) eps).
Unfold Rgt in H1.
 Apply (Rle_lt_trans (Rminus (Un n) x) R0 eps
                     (Rle_minus (Un n) x (H5 n)) H1).
Fold Un_growing in H;Generalize (growing_prop Un n N H H7);Intro H8.
 Generalize (Rlt_le_trans (Rminus x eps) (Un N) (Un n) H6
                          (Rle_sym2 (Un N) (Un n) H8));Intro H9;
 Generalize (Rlt_compatibility (Ropp x) (Rminus x eps) (Un n) H9);
 Unfold Rminus;Rewrite <-(Rplus_assoc (Ropp x) x (Ropp eps));
 Rewrite (Rplus_sym (Ropp x) (Un n));Fold (Rminus (Un n) x);
 Rewrite Rplus_Ropp_l;Rewrite (let (H1,H2)=(Rplus_ne (Ropp eps)) in H2);
 Trivial.
Cut ~((N:nat)(Rle (Un N) (Rminus x eps))).
Intro H6;Apply (not_all_not_ex nat ([N:nat](Rlt (Rminus x eps) (Un N)))).
 Intro H7; Apply H6; Intro N; Apply Rnot_lt_le; Apply H7.
Intro H7;Generalize (Un_bound_imp Un (Rminus x eps) H7);Intro H8;
 Unfold is_upper_bound in H8;Generalize (H3 (Rminus x eps) H8);
 Apply Rlt_le_not; Apply tech_Rgt_minus; Exact H1.
Qed.

Lemma decreasing_growing : (Un:nat->R) (Un_decreasing Un) -> (Un_growing (opp_seq Un)).
Intro.
Unfold Un_growing opp_seq Un_decreasing.
Intros.
Apply Rle_Ropp1.
Apply H.
Qed.

Lemma decreasing_cv : (Un:nat->R) (Un_decreasing Un) -> (has_lb Un) -> (sigTT R [l:R](Un_cv Un l)).
Intros.
Cut (sigTT R [l:R](Un_cv (opp_seq Un) l)) -> (sigTT R [l:R](Un_cv Un l)).
Intro.
Apply X.
Apply growing_cv.
Apply decreasing_growing; Assumption.
Exact H0.
Intro.
Elim X; Intros.
Apply existTT with ``-x``.
Unfold Un_cv in p.
Unfold R_dist in p.
Unfold opp_seq in p.
Unfold Un_cv.
Unfold R_dist.
Intros.
Elim (p eps H1); Intros.
Exists x0; Intros.
Assert H4 := (H2 n H3).
Rewrite <- Rabsolu_Ropp.
Replace ``-((Un n)- -x)`` with ``-(Un n)-x``; [Assumption | Ring].
Qed.

(***********)
Lemma maj_sup : (Un:nat->R) (has_ub Un) -> (sigTT R [l:R](is_lub (EUn Un) l)).
Intros.
Unfold has_ub in H.
Apply complet.
Assumption.
Exists (Un O).
Unfold EUn.
Exists O; Reflexivity.
Qed.

(**********)
Lemma min_inf : (Un:nat->R) (has_lb Un) -> (sigTT R [l:R](is_lub (EUn (opp_seq Un)) l)).
Intros; Unfold has_lb in H.
Apply complet.
Assumption.
Exists ``-(Un O)``.
Exists O.
Reflexivity.
Qed.

Definition majorant [Un:nat->R;pr:(has_ub Un)] : R := Cases (maj_sup Un pr) of (existTT a b) => a end.

Definition minorant [Un:nat->R;pr:(has_lb Un)] : R := Cases (min_inf Un pr) of (existTT a b) => ``-a`` end.

Lemma maj_ss : (Un:nat->R;k:nat) (has_ub Un) -> (has_ub [i:nat](Un (plus k i))).
Intros.
Unfold has_ub in H.
Unfold bound in H.
Elim H; Intros.
Unfold is_upper_bound in H0.
Unfold has_ub.
Exists x.
Unfold is_upper_bound.
Intros.
Apply H0.
Elim H1; Intros.
Exists (plus k x1); Assumption.
Qed.

Lemma min_ss : (Un:nat->R;k:nat) (has_lb Un) -> (has_lb [i:nat](Un (plus k i))).
Intros.
Unfold has_lb in H.
Unfold bound in H.
Elim H; Intros.
Unfold is_upper_bound in H0.
Unfold has_lb.
Exists x.
Unfold is_upper_bound.
Intros.
Apply H0.
Elim H1; Intros.
Exists (plus k x1); Assumption.
Qed.

Definition sequence_majorant [Un:nat->R;pr:(has_ub Un)] : nat -> R := [i:nat](majorant [k:nat](Un (plus i k)) (maj_ss Un i pr)).

Definition sequence_minorant [Un:nat->R;pr:(has_lb Un)] : nat -> R := [i:nat](minorant [k:nat](Un (plus i k)) (min_ss Un i pr)).

Lemma Wn_decreasing : (Un:nat->R;pr:(has_ub Un)) (Un_decreasing (sequence_majorant Un pr)). 
Intros.
Unfold Un_decreasing.
Intro.
Unfold sequence_majorant.
Assert H := (maj_sup [k:nat](Un (plus (S n) k)) (maj_ss Un (S n) pr)).
Assert H0 := (maj_sup [k:nat](Un (plus n k)) (maj_ss Un n pr)).
Elim H; Intros.
Elim H0; Intros.
Cut (majorant ([k:nat](Un (plus (S n) k))) (maj_ss Un (S n) pr)) == x; [Intro Maj1; Rewrite Maj1 | Idtac].
Cut (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr)) == x0; [Intro Maj2; Rewrite Maj2 | Idtac].
Unfold is_lub in p.
Unfold is_lub in p0.
Elim p; Intros.
Apply H2.
Elim p0; Intros.
Unfold is_upper_bound.
Intros.
Unfold is_upper_bound in H3.
Apply H3.
Elim H5; Intros.
Exists (plus (1) x2).
Replace (plus n (plus (S O) x2)) with (plus (S n) x2).
Assumption.
Replace (S n) with (plus (1) n); [Ring | Ring].
Cut (is_lub (EUn [k:nat](Un (plus n k))) (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr))).
Intro.
Unfold is_lub in p0; Unfold is_lub in H1.
Elim p0; Intros; Elim H1; Intros.
Assert H6 := (H5 x0 H2).
Assert H7 := (H3 (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr)) H4).
Apply Rle_antisym; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus n k)) (maj_ss Un n pr)).
Trivial.
Cut (is_lub (EUn [k:nat](Un (plus (S n) k))) (majorant ([k:nat](Un (plus (S n) k))) (maj_ss Un (S n) pr))).
Intro.
Unfold is_lub in p; Unfold is_lub in H1.
Elim p; Intros; Elim H1; Intros.
Assert H6 := (H5 x H2).
Assert H7 := (H3 (majorant ([k:nat](Un (plus (S n) k))) (maj_ss Un (S n) pr)) H4).
Apply Rle_antisym; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus (S n) k)) (maj_ss Un (S n) pr)).
Trivial.
Qed.

Lemma Vn_growing : (Un:nat->R;pr:(has_lb Un)) (Un_growing (sequence_minorant Un pr)).
Intros.
Unfold Un_growing.
Intro.
Unfold sequence_minorant.
Assert H := (min_inf [k:nat](Un (plus (S n) k)) (min_ss Un (S n) pr)).
Assert H0 := (min_inf [k:nat](Un (plus n k)) (min_ss Un n pr)).
Elim H; Intros.
Elim H0; Intros.
Cut (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr)) == ``-x``; [Intro Maj1; Rewrite Maj1 | Idtac].
Cut (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr)) == ``-x0``; [Intro Maj2; Rewrite Maj2 | Idtac].
Unfold is_lub in p.
Unfold is_lub in p0.
Elim p; Intros.
Apply Rle_Ropp1.
Apply H2.
Elim p0; Intros.
Unfold is_upper_bound.
Intros.
Unfold is_upper_bound in H3.
Apply H3.
Elim H5; Intros.
Exists (plus (1) x2).
Unfold opp_seq in H6.
Unfold opp_seq.
Replace (plus n (plus (S O) x2)) with (plus (S n) x2).
Assumption.
Replace (S n) with (plus (1) n); [Ring | Ring].
Cut (is_lub (EUn (opp_seq [k:nat](Un (plus n k)))) (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr)))).
Intro.
Unfold is_lub in p0; Unfold is_lub in H1.
Elim p0; Intros; Elim H1; Intros.
Assert H6 := (H5 x0 H2).
Assert H7 := (H3 (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr))) H4).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr))).
Apply eq_Ropp; Apply Rle_antisym; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus n k)) (min_ss Un n pr)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Cut (is_lub (EUn (opp_seq [k:nat](Un (plus (S n) k)))) (Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr)))).
Intro.
Unfold is_lub in p; Unfold is_lub in H1.
Elim p; Intros; Elim H1; Intros.
Assert H6 := (H5 x H2).
Assert H7 := (H3 (Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr))) H4).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr))).
Apply eq_Ropp; Apply Rle_antisym; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus (S n) k)) (min_ss Un (S n) pr)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Qed.

(**********)
Lemma Vn_Un_Wn_order : (Un:nat->R;pr1:(has_ub Un);pr2:(has_lb Un)) (n:nat) ``((sequence_minorant Un pr2) n)<=(Un n)<=((sequence_majorant Un pr1) n)``. 
Intros.
Split.
Unfold sequence_minorant.
Cut (sigTT R [l:R](is_lub (EUn (opp_seq [i:nat](Un (plus n i)))) l)).
Intro.
Elim X; Intros.
Replace (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2)) with ``-x``.
Unfold is_lub in p.
Elim p; Intros.
Unfold is_upper_bound in H.
Rewrite <- (Ropp_Ropp (Un n)).
Apply Rle_Ropp1.
Apply H.
Exists O.
Unfold opp_seq.
Replace (plus n O) with n; [Reflexivity | Ring].
Cut (is_lub (EUn (opp_seq [k:nat](Un (plus n k)))) (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2)))).
Intro.
Unfold is_lub in p; Unfold is_lub in H.
Elim p; Intros; Elim H; Intros.
Assert H4 := (H3 x H0).
Assert H5 := (H1 (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2))) H2).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2))).
Apply eq_Ropp; Apply Rle_antisym; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus n k)) (min_ss Un n pr2)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Apply min_inf.
Apply min_ss; Assumption.
Unfold sequence_majorant.
Cut (sigTT R [l:R](is_lub (EUn [i:nat](Un (plus n i))) l)).
Intro.
Elim X; Intros.
Replace (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr1)) with ``x``.
Unfold is_lub in p.
Elim p; Intros.
Unfold is_upper_bound in H.
Apply H.
Exists O.
Replace (plus n O) with n; [Reflexivity | Ring].
Cut (is_lub (EUn [k:nat](Un (plus n k))) (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr1))).
Intro.
Unfold is_lub in p; Unfold is_lub in H.
Elim p; Intros; Elim H; Intros.
Assert H4 := (H3 x H0).
Assert H5 := (H1 (majorant ([k:nat](Un (plus n k))) (maj_ss Un n pr1)) H2).
Apply Rle_antisym; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus n k)) (maj_ss Un n pr1)).
Intro; Trivial.
Apply maj_sup.
Apply maj_ss; Assumption.
Qed.

Lemma min_maj : (Un:nat->R;pr1:(has_ub Un);pr2:(has_lb Un)) (has_ub (sequence_minorant Un pr2)).
Intros.
Assert H := (Vn_Un_Wn_order Un pr1 pr2).
Unfold has_ub.
Unfold bound.
Unfold has_ub in pr1.
Unfold bound in pr1.
Elim pr1; Intros.
Exists x.
Unfold is_upper_bound.
Intros.
Unfold is_upper_bound in H0.
Elim H1; Intros.
Rewrite H2.
Apply Rle_trans with (Un x1).
Assert H3 := (H x1); Elim H3; Intros; Assumption.
Apply H0.
Exists x1; Reflexivity.
Qed.

Lemma maj_min : (Un:nat->R;pr1:(has_ub Un);pr2:(has_lb Un)) (has_lb (sequence_majorant Un pr1)). 
Intros.
Assert H := (Vn_Un_Wn_order Un pr1 pr2).
Unfold has_lb.
Unfold bound.
Unfold has_lb in pr2.
Unfold bound in pr2.
Elim pr2; Intros.
Exists x.
Unfold is_upper_bound.
Intros.
Unfold is_upper_bound in H0.
Elim H1; Intros.
Rewrite H2.
Apply Rle_trans with ((opp_seq Un) x1).
Assert H3 := (H x1); Elim H3; Intros.
Unfold opp_seq; Apply Rle_Ropp1.
Assumption.
Apply H0.
Exists x1; Reflexivity.
Qed.

(**********)
Lemma cauchy_maj : (Un:nat->R) (Cauchy_crit Un) -> (has_ub Un).
Intros.
Unfold has_ub.
Apply cauchy_bound.
Assumption.
Qed.

(**********)
Lemma cauchy_opp : (Un:nat->R) (Cauchy_crit Un) -> (Cauchy_crit (opp_seq Un)).
Intro.
Unfold Cauchy_crit.
Unfold R_dist.
Intros.
Elim (H eps H0); Intros.
Exists x; Intros.
Unfold opp_seq.
Rewrite <- Rabsolu_Ropp.
Replace ``-( -(Un n)- -(Un m))`` with ``(Un n)-(Un m)``; [Apply H1; Assumption | Ring].
Qed.

(**********)
Lemma cauchy_min : (Un:nat->R) (Cauchy_crit Un) -> (has_lb Un).
Intros.
Unfold has_lb.
Assert H0 := (cauchy_opp ? H).
Apply cauchy_bound.
Assumption.
Qed.

(**********)
Lemma maj_cv : (Un:nat->R;pr:(Cauchy_crit Un)) (sigTT R [l:R](Un_cv (sequence_majorant Un (cauchy_maj Un pr)) l)).
Intros.
Apply decreasing_cv.
Apply Wn_decreasing.
Apply maj_min.
Apply cauchy_min.
Assumption.
Qed.

(**********)
Lemma min_cv : (Un:nat->R;pr:(Cauchy_crit Un)) (sigTT R [l:R](Un_cv (sequence_minorant Un (cauchy_min Un pr)) l)).
Intros.
Apply growing_cv.
Apply Vn_growing.
Apply min_maj.
Apply cauchy_maj.
Assumption.
Qed.

Lemma cond_eq : (x,y:R) ((eps:R)``0<eps``->``(Rabsolu (x-y))<eps``) -> x==y.
Intros.
Case (total_order_T x y); Intro.
Elim s; Intro.
Cut ``0<y-x``.
Intro.
Assert H1 := (H ``y-x`` H0).
Rewrite <- Rabsolu_Ropp in H1.
Cut ``-(x-y)==y-x``; [Intro; Rewrite H2 in H1 | Ring].
Rewrite Rabsolu_right in H1.
Elim (Rlt_antirefl ? H1).
Left; Assumption.
Apply Rlt_anti_compatibility with x.
Rewrite Rplus_Or; Replace ``x+(y-x)`` with y; [Assumption | Ring].
Assumption.
Cut ``0<x-y``.
Intro.
Assert H1 := (H ``x-y`` H0).
Rewrite Rabsolu_right in H1.
Elim (Rlt_antirefl ? H1).
Left; Assumption.
Apply Rlt_anti_compatibility with y.
Rewrite Rplus_Or; Replace ``y+(x-y)`` with x; [Assumption | Ring].
Qed.

Lemma not_Rlt : (r1,r2:R)~(``r1<r2``)->``r1>=r2``.
Intros r1 r2 ; Generalize (total_order r1 r2) ; Unfold Rge.
Tauto.
Qed. 

(**********)
Lemma approx_maj : (Un:nat->R;pr:(has_ub Un)) (eps:R) ``0<eps`` -> (EX k : nat | ``(Rabsolu ((majorant Un pr)-(Un k))) < eps``).
Intros.
Pose P := [k:nat]``(Rabsolu ((majorant Un pr)-(Un k))) < eps``.
Unfold P.
Cut (EX k:nat | (P k)) -> (EX k:nat | ``(Rabsolu ((majorant Un pr)-(Un k))) < eps``).
Intros.
Apply H0.
Apply not_all_not_ex.
Red; Intro.
2:Unfold P; Trivial.
Unfold P in H1.
Cut (n:nat)``(Rabsolu ((majorant Un pr)-(Un n))) >= eps``.
Intro.
Cut (is_lub (EUn Un) (majorant Un pr)).
Intro.
Unfold is_lub in H3.
Unfold is_upper_bound in H3.
Elim H3; Intros.
Cut (n:nat)``eps<=(majorant Un pr)-(Un n)``.
Intro.
Cut (n:nat)``(Un n)<=(majorant Un pr)-eps``.
Intro.
Cut ((x:R)(EUn Un x)->``x <= (majorant Un pr)-eps``).
Intro.
Assert H9 := (H5 ``(majorant Un pr)-eps`` H8).
Cut ``eps<=0``.
Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H H10)).
Apply Rle_anti_compatibility with ``(majorant Un pr)-eps``.
Rewrite Rplus_Or.
Replace ``(majorant Un pr)-eps+eps`` with (majorant Un pr); [Assumption | Ring].
Intros.
Unfold EUn in H8.
Elim H8; Intros.
Rewrite H9; Apply H7.
Intro.
Assert H7 := (H6 n).
Apply Rle_anti_compatibility with ``eps-(Un n)``.
Replace ``eps-(Un n)+(Un n)`` with ``eps``.
Replace ``eps-(Un n)+((majorant Un pr)-eps)`` with ``(majorant Un pr)-(Un n)``.
Assumption.
Ring.
Ring.
Intro.
Assert H6 := (H2 n).
Rewrite Rabsolu_right in H6.
Apply Rle_sym2.
Assumption.
Apply Rle_sym1.
Apply Rle_anti_compatibility with (Un n).
Rewrite Rplus_Or; Replace ``(Un n)+((majorant Un pr)-(Un n))`` with (majorant Un pr); [Apply H4 | Ring].
Exists n; Reflexivity.
Unfold majorant.
Case (maj_sup Un pr).
Trivial.
Intro.
Assert H2 := (H1 n).
Apply not_Rlt; Assumption.
Qed.

(**********)
Lemma approx_min : (Un:nat->R;pr:(has_lb Un)) (eps:R) ``0<eps`` -> (EX k :nat | ``(Rabsolu ((minorant Un pr)-(Un k))) < eps``).
Intros.
Pose P := [k:nat]``(Rabsolu ((minorant Un pr)-(Un k))) < eps``.
Unfold P.
Cut (EX k:nat | (P k)) -> (EX k:nat | ``(Rabsolu ((minorant Un pr)-(Un k))) < eps``).
Intros.
Apply H0.
Apply not_all_not_ex.
Red; Intro.
2:Unfold P; Trivial.
Unfold P in H1.
Cut (n:nat)``(Rabsolu ((minorant Un pr)-(Un n))) >= eps``.
Intro.
Cut (is_lub (EUn (opp_seq Un)) ``-(minorant Un pr)``).
Intro.
Unfold is_lub in H3.
Unfold is_upper_bound in H3.
Elim H3; Intros.
Cut (n:nat)``eps<=(Un n)-(minorant Un pr)``.
Intro.
Cut (n:nat)``((opp_seq Un) n)<=-(minorant Un pr)-eps``.
Intro.
Cut ((x:R)(EUn (opp_seq Un) x)->``x <= -(minorant Un pr)-eps``).
Intro.
Assert H9 := (H5 ``-(minorant Un pr)-eps`` H8).
Cut ``eps<=0``.
Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H H10)).
Apply Rle_anti_compatibility with ``-(minorant Un pr)-eps``.
Rewrite Rplus_Or.
Replace ``-(minorant Un pr)-eps+eps`` with ``-(minorant Un pr)``; [Assumption | Ring].
Intros.
Unfold EUn in H8.
Elim H8; Intros.
Rewrite H9; Apply H7.
Intro.
Assert H7 := (H6 n).
Unfold opp_seq.
Apply Rle_anti_compatibility with ``eps+(Un n)``.
Replace ``eps+(Un n)+ -(Un n)`` with ``eps``.
Replace ``eps+(Un n)+(-(minorant Un pr)-eps)`` with ``(Un n)-(minorant Un pr)``.
Assumption.
Ring.
Ring.
Intro.
Assert H6 := (H2 n).
Rewrite Rabsolu_left1 in H6.
Apply Rle_sym2.
Replace ``(Un n)-(minorant Un pr)`` with `` -((minorant Un pr)-(Un n))``; [Assumption | Ring].
Apply Rle_anti_compatibility with ``-(minorant Un pr)``.
Rewrite Rplus_Or; Replace ``-(minorant Un pr)+((minorant Un pr)-(Un n))`` with ``-(Un n)``.
Apply H4.
Exists n; Reflexivity.
Ring.
Unfold minorant.
Case (min_inf Un pr).
Intro.
Rewrite Ropp_Ropp.
Trivial.
Intro.
Assert H2 := (H1 n).
Apply not_Rlt; Assumption.
Qed.

(* Unicity of limit for convergent sequences *) 
Lemma UL_sequence : (Un:nat->R;l1,l2:R) (Un_cv Un l1) -> (Un_cv Un l2) -> l1==l2. 
Intros Un l1 l2; Unfold Un_cv; Unfold R_dist; Intros. 
Apply cond_eq. 
Intros; Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (H ``eps/2`` H2); Intros. 
Elim (H0 ``eps/2`` H2); Intros. 
Pose N := (max x x0). 
Apply Rle_lt_trans with ``(Rabsolu (l1 -(Un N)))+(Rabsolu ((Un N)-l2))``. 
Replace ``l1-l2`` with ``(l1-(Un N))+((Un N)-l2)``; [Apply Rabsolu_triang | Ring]. 
Rewrite (double_var eps); Apply Rplus_lt. 
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H3; Unfold ge N; Apply le_max_l. 
Apply H4; Unfold ge N; Apply le_max_r. 
Qed.

(**********) 
Lemma CV_plus : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)+(Bn i)`` ``l1+l2``). 
Unfold Un_cv; Unfold R_dist; Intros. 
Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (H ``eps/2`` H2); Intros. 
Elim (H0 ``eps/2`` H2); Intros. 
Pose N := (max x x0). 
Exists N; Intros. 
Replace ``(An n)+(Bn n)-(l1+l2)`` with ``((An n)-l1)+((Bn n)-l2)``; [Idtac | Ring]. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)-l1))+(Rabsolu ((Bn n)-l2))``. 
Apply Rabsolu_triang. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply H3; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_l | Assumption]. 
Apply H4; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_r | Assumption]. 
Qed.

(**********) 
Lemma cv_cvabs : (Un:nat->R;l:R) (Un_cv Un l) -> (Un_cv [i:nat](Rabsolu (Un i)) (Rabsolu l)). 
Unfold Un_cv; Unfold R_dist; Intros. 
Elim (H eps H0); Intros. 
Exists x; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((Un n)-l))``. 
Apply Rabsolu_triang_inv2. 
Apply H1; Assumption. 
Qed. 

(**********) 
Lemma CV_Cauchy : (Un:nat->R) (sigTT R [l:R](Un_cv Un l)) -> (Cauchy_crit Un). 
Intros; Elim X; Intros. 
Unfold Cauchy_crit; Intros. 
Unfold Un_cv in p; Unfold R_dist in p. 
Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (p ``eps/2`` H0); Intros. 
Exists x0; Intros. 
Unfold R_dist; Apply Rle_lt_trans with ``(Rabsolu ((Un n)-x))+(Rabsolu (x-(Un m)))``. 
Replace ``(Un n)-(Un m)`` with ``((Un n)-x)+(x-(Un m))``; [Apply Rabsolu_triang | Ring]. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply H1; Assumption. 
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H1; Assumption. 
Qed. 

(**********)
Lemma maj_by_pos : (Un:nat->R) (sigTT R [l:R](Un_cv Un l)) -> (EXT l:R | ``0<l``/\((n:nat)``(Rabsolu (Un n))<=l``)). 
Intros; Elim X; Intros. 
Cut (sigTT R [l:R](Un_cv [k:nat](Rabsolu (Un k)) l)). 
Intro. 
Assert H := (CV_Cauchy [k:nat](Rabsolu (Un k)) X0). 
Assert H0 := (cauchy_bound [k:nat](Rabsolu (Un k)) H). 
Elim H0; Intros. 
Exists ``x0+1``. 
Cut ``0<=x0``. 
Intro. 
Split. 
Apply ge0_plus_gt0_is_gt0; [Assumption | Apply Rlt_R0_R1]. 
Intros. 
Apply Rle_trans with x0. 
Unfold is_upper_bound in H1. 
Apply H1. 
Exists n; Reflexivity. 
Pattern 1 x0; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply Rlt_R0_R1. 
Apply Rle_trans with (Rabsolu (Un O)). 
Apply Rabsolu_pos. 
Unfold is_upper_bound in H1. 
Apply H1. 
Exists O; Reflexivity. 
Apply existTT with (Rabsolu x). 
Apply cv_cvabs; Assumption. 
Qed. 
 
(**********) 
Lemma CV_mult : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)*(Bn i)`` ``l1*l2``). 
Intros. 
Cut (sigTT R [l:R](Un_cv An l)). 
Intro. 
Assert H1 := (maj_by_pos An X). 
Elim H1; Intros M H2. 
Elim H2; Intros. 
Unfold Un_cv; Unfold R_dist; Intros. 
Cut ``0<eps/(2*M)``. 
Intro. 
Case (Req_EM l2 R0); Intro. 
Unfold Un_cv in H0; Unfold R_dist in H0. 
Elim (H0 ``eps/(2*M)`` H6); Intros. 
Exists x; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))+(Rabsolu ((An n)*l2-l1*l2))``. 
Replace ``(An n)*(Bn n)-l1*l2`` with ``((An n)*(Bn n)-(An n)*l2)+((An n)*l2-l1*l2)``; [Apply Rabsolu_triang | Ring]. 
Replace ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))`` with ``(Rabsolu (An n))*(Rabsolu ((Bn n)-l2))``. 
Replace ``(Rabsolu ((An n)*l2-l1*l2))`` with R0. 
Rewrite Rplus_Or. 
Apply Rle_lt_trans with ``M*(Rabsolu ((Bn n)-l2))``. 
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu ((Bn n)-l2))``). 
Apply Rle_monotony. 
Apply Rabsolu_pos. 
Apply H4. 
Apply Rlt_monotony_contra with ``/M``. 
Apply Rlt_Rinv; Apply H3. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Rewrite (Rmult_sym ``/M``). 
Apply Rlt_trans with  ``eps/(2*M)``. 
Apply H8; Assumption. 
Unfold Rdiv; Rewrite Rinv_Rmult. 
Apply Rlt_monotony_contra with ``2``. 
Sup0.
Replace ``2*(eps*(/2*/M))`` with ``(2*/2)*(eps*/M)``; [Idtac | Ring]. 
Rewrite <- Rinv_r_sym. 
Rewrite Rmult_1l; Rewrite double. 
Pattern 1 ``eps*/M``; Rewrite <- Rplus_Or. 
Apply Rlt_compatibility; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Assumption]. 
DiscrR. 
DiscrR. 
Red; Intro; Rewrite H10 in H3; Elim (Rlt_antirefl ? H3). 
Red; Intro; Rewrite H10 in H3; Elim (Rlt_antirefl ? H3). 
Rewrite H7; Do 2 Rewrite Rmult_Or; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Reflexivity. 
Replace ``(An n)*(Bn n)-(An n)*l2`` with ``(An n)*((Bn n)-l2)``; [Idtac | Ring]. 
Symmetry; Apply Rabsolu_mult. 
Cut ``0<eps/(2*(Rabsolu l2))``. 
Intro. 
Unfold Un_cv in H; Unfold R_dist in H; Unfold Un_cv in H0; Unfold R_dist in H0. 
Elim (H ``eps/(2*(Rabsolu l2))`` H8); Intros N1 H9. 
Elim (H0 ``eps/(2*M)`` H6); Intros N2 H10. 
Pose N := (max N1 N2). 
Exists N; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))+(Rabsolu ((An n)*l2-l1*l2))``. 
Replace ``(An n)*(Bn n)-l1*l2`` with ``((An n)*(Bn n)-(An n)*l2)+((An n)*l2-l1*l2)``; [Apply Rabsolu_triang | Ring]. 
Replace ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))`` with ``(Rabsolu (An n))*(Rabsolu ((Bn n)-l2))``. 
Replace ``(Rabsolu ((An n)*l2-l1*l2))`` with ``(Rabsolu l2)*(Rabsolu ((An n)-l1))``. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply Rle_lt_trans with ``M*(Rabsolu ((Bn n)-l2))``. 
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu ((Bn n)-l2))``). 
Apply Rle_monotony. 
Apply Rabsolu_pos. 
Apply H4. 
Apply Rlt_monotony_contra with ``/M``. 
Apply Rlt_Rinv; Apply H3. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Rewrite (Rmult_sym ``/M``). 
Apply Rlt_le_trans with  ``eps/(2*M)``. 
Apply H10. 
Unfold ge; Apply le_trans with N. 
Unfold N; Apply le_max_r. 
Assumption. 
Unfold Rdiv; Rewrite Rinv_Rmult. 
Right; Ring. 
DiscrR. 
Red; Intro; Rewrite H12 in H3; Elim (Rlt_antirefl ? H3). 
Red; Intro; Rewrite H12 in H3; Elim (Rlt_antirefl ? H3). 
Apply Rlt_monotony_contra with ``/(Rabsolu l2)``. 
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Apply Rlt_le_trans with ``eps/(2*(Rabsolu l2))``. 
Apply H9. 
Unfold ge; Apply le_trans with N. 
Unfold N; Apply le_max_l. 
Assumption. 
Unfold Rdiv; Right; Rewrite Rinv_Rmult. 
Ring. 
DiscrR. 
Apply Rabsolu_no_R0; Assumption. 
Apply Rabsolu_no_R0; Assumption. 
Replace ``(An n)*l2-l1*l2`` with ``l2*((An n)-l1)``; [Symmetry; Apply Rabsolu_mult | Ring]. 
Replace ``(An n)*(Bn n)-(An n)*l2`` with ``(An n)*((Bn n)-l2)``; [Symmetry; Apply Rabsolu_mult | Ring]. 
Unfold Rdiv; Apply Rmult_lt_pos. 
Assumption. 
Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Apply Rabsolu_pos_lt; Assumption]. 
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Assumption]]. 
Apply existTT with l1; Assumption. 
Qed. 

Lemma tech9 : (Un:nat->R) (Un_growing Un) -> ((m,n:nat)(le m n)->``(Un m)<=(Un n)``).
Intros; Unfold Un_growing in H.
Induction n.
Induction m.
Right; Reflexivity.
Elim (le_Sn_O ? H0).
Cut (le m n)\/m=(S n).
Intro; Elim H1; Intro.
Apply Rle_trans with (Un n).
Apply Hrecn; Assumption.
Apply H.
Rewrite H2; Right; Reflexivity.
Inversion H0.
Right; Reflexivity.
Left; Assumption.
Qed.

Lemma tech10 : (Un:nat->R;x:R) (Un_growing Un) -> (is_lub (EUn Un) x) -> (Un_cv Un x).
Intros; Cut (bound (EUn Un)).
Intro; Assert H2 := (Un_cv_crit ? H H1).
Elim H2; Intros.
Case (total_order_T x x0); Intro.
Elim s; Intro.
Cut (n:nat)``(Un n)<=x``.
Intro; Unfold Un_cv in H3; Cut ``0<x0-x``.
Intro; Elim (H3 ``x0-x`` H5); Intros.
Cut (ge x1 x1).
Intro; Assert H8 := (H6 x1 H7).
Unfold R_dist in H8; Rewrite Rabsolu_left1 in H8.
Rewrite Ropp_distr2 in H8; Unfold Rminus in H8.
Assert H9 := (Rlt_anti_compatibility ``x0`` ? ? H8).
Assert H10 := (Ropp_Rlt ? ? H9).
Assert H11 := (H4 x1).
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H10 H11)).
Apply Rle_minus; Apply Rle_trans with x.
Apply H4.
Left; Assumption.
Unfold ge; Apply le_n.
Apply Rgt_minus; Assumption.
Intro; Unfold is_lub in H0; Unfold is_upper_bound in H0; Elim H0; Intros.
Apply H4; Unfold EUn; Exists n; Reflexivity.
Rewrite b; Assumption.
Cut ((n:nat)``(Un n)<=x0``).
Intro; Unfold is_lub in H0; Unfold is_upper_bound in H0; Elim H0; Intros.
Cut (y:R)(EUn Un y)->``y<=x0``.
Intro; Assert H8 := (H6 ? H7). 
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H8 r)).
Unfold EUn; Intros; Elim H7; Intros.
Rewrite H8; Apply H4.
Intro; Case (total_order_Rle (Un n) x0); Intro.
Assumption.
Cut (n0:nat)(le n n0) -> ``x0<(Un n0)``. 
Intro; Unfold Un_cv in H3; Cut ``0<(Un n)-x0``.
Intro; Elim (H3 ``(Un n)-x0`` H5); Intros.
Cut (ge (max n x1) x1).
Intro; Assert H8 := (H6 (max n x1) H7).
Unfold R_dist in H8.
Rewrite Rabsolu_right in H8.
Unfold Rminus in H8; Do 2 Rewrite <- (Rplus_sym ``-x0``) in H8.
Assert H9 := (Rlt_anti_compatibility ? ? ? H8).
Cut ``(Un n)<=(Un (max n x1))``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H10 H9)).
Apply tech9; [Assumption | Apply le_max_l].
Apply Rge_trans with ``(Un n)-x0``.
Unfold Rminus; Apply Rle_sym1; Do 2 Rewrite <- (Rplus_sym ``-x0``); Apply Rle_compatibility.
Apply tech9; [Assumption | Apply le_max_l].
Left; Assumption.
Unfold ge; Apply le_max_r.
Apply Rlt_anti_compatibility with x0.
Rewrite Rplus_Or; Unfold Rminus; Rewrite (Rplus_sym x0); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply H4; Apply le_n.
Intros; Apply Rlt_le_trans with (Un n).
Case (total_order_Rlt_Rle x0 (Un n)); Intro.
Assumption.
Elim n0; Assumption.
Apply tech9; Assumption.
Unfold bound; Exists x; Unfold is_lub in H0; Elim H0; Intros; Assumption.
Qed.

Lemma tech13 : (An:nat->R;k:R) ``0<=k<1`` -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (EXT k0 : R | ``k<k0<1`` /\ (EX N:nat | (n:nat) (le N n)->``(Rabsolu ((An (S n))/(An n)))<k0``)).
Intros; Exists ``k+(1-k)/2``.
Split.
Split.
Pattern 1 k; Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with k; Rewrite Rplus_Or; Replace ``k+(1-k)`` with R1; [Elim H; Intros; Assumption | Ring].
Apply Rlt_Rinv; Sup0.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite Rmult_1r; Rewrite Rmult_Rplus_distr; Pattern 1 ``2``; Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR]; Rewrite Rmult_1r; Replace ``2*k+(1-k)`` with ``1+k``; [Idtac | Ring].
Elim H; Intros.
Apply Rlt_compatibility; Assumption.
Unfold Un_cv in H0; Cut ``0<(1-k)/2``.
Intro; Elim (H0 ``(1-k)/2`` H1); Intros.
Exists x; Intros.
Assert H4 := (H2 n H3).
Unfold R_dist in H4; Rewrite <- Rabsolu_Rabsolu; Replace ``(Rabsolu ((An (S n))/(An n)))`` with ``((Rabsolu ((An (S n))/(An n)))-k)+k``; [Idtac | Ring]; Apply Rle_lt_trans with ``(Rabsolu ((Rabsolu ((An (S n))/(An n)))-k))+(Rabsolu k)``.
Apply Rabsolu_triang.
Rewrite (Rabsolu_right k).
Apply Rlt_anti_compatibility with ``-k``; Rewrite <- (Rplus_sym k); Repeat Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Repeat Rewrite Rplus_Ol; Apply H4.
Apply Rle_sym1; Elim H; Intros; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with k; Rewrite Rplus_Or; Elim H; Intros; Replace ``k+(1-k)`` with R1; [Assumption | Ring].
Apply Rlt_Rinv; Sup0.
Qed.

(**********)
Lemma growing_ineq : (Un:nat->R;l:R) (Un_growing Un) -> (Un_cv Un l) -> ((n:nat)``(Un n)<=l``). 
Intros; Case (total_order_T (Un n) l); Intro.
Elim s; Intro.
Left; Assumption.
Right; Assumption.
Cut ``0<(Un n)-l``.
Intro; Unfold Un_cv in H0; Unfold R_dist in H0.
Elim (H0 ``(Un n)-l`` H1); Intros N1 H2.
Pose N := (max n N1).
Cut ``(Un n)-l<=(Un N)-l``.
Intro; Cut ``(Un N)-l<(Un n)-l``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H3 H4)).
Apply Rle_lt_trans with ``(Rabsolu ((Un N)-l))``.
Apply Rle_Rabsolu.
Apply H2.
Unfold ge N; Apply le_max_r.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-l``); Apply Rle_compatibility.
Apply tech9.
Assumption.
Unfold N; Apply le_max_l.
Apply Rlt_anti_compatibility with l.
Rewrite Rplus_Or.
Replace ``l+((Un n)-l)`` with (Un n); [Assumption | Ring].
Qed.

(* Un->l => (-Un) -> (-l) *)
Lemma CV_opp : (An:nat->R;l:R) (Un_cv An l) -> (Un_cv (opp_seq An) ``-l``).
Intros An l.
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H eps H0); Intros.
Exists x; Intros.
Unfold opp_seq; Replace ``-(An n)- (-l)`` with ``-((An n)-l)``; [Rewrite Rabsolu_Ropp | Ring].
Apply H1; Assumption.
Qed.

(**********)
Lemma decreasing_ineq : (Un:nat->R;l:R) (Un_decreasing Un) -> (Un_cv Un l) -> ((n:nat)``l<=(Un n)``).
Intros.
Assert H1 := (decreasing_growing ? H).
Assert H2 := (CV_opp ? ? H0).
Assert H3 := (growing_ineq ? ? H1 H2).
Apply Ropp_Rle.
Unfold opp_seq in H3; Apply H3.
Qed.

(**********)
Lemma CV_minus : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)-(Bn i)`` ``l1-l2``). 
Intros. 
Replace [i:nat]``(An i)-(Bn i)`` with [i:nat]``(An i)+((opp_seq Bn) i)``. 
Unfold Rminus; Apply CV_plus. 
Assumption. 
Apply CV_opp; Assumption. 
Unfold Rminus opp_seq; Reflexivity. 
Qed. 

(* Un -> +oo *)
Definition cv_infty [Un:nat->R] : Prop := (M:R)(EXT N:nat | (n:nat) (le N n) -> ``M<(Un n)``).

(* Un -> +oo => /Un -> O *)
Lemma cv_infty_cv_R0 : (Un:nat->R) ((n:nat)``(Un n)<>0``) -> (cv_infty Un) -> (Un_cv [n:nat]``/(Un n)`` R0).
Unfold cv_infty Un_cv; Unfold R_dist; Intros.
Elim (H0 ``/eps``); Intros N0 H2.
Exists N0; Intros.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite (Rabsolu_Rinv ? (H n)).
Apply Rlt_monotony_contra with (Rabsolu (Un n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with ``/eps``.
Apply Rlt_Rinv; Assumption.
Rewrite Rmult_1r; Rewrite (Rmult_sym ``/eps``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rlt_le_trans with (Un n).
Apply H2; Assumption.
Apply Rle_Rabsolu.
Red; Intro; Rewrite H4 in H1; Elim (Rlt_antirefl ? H1).
Apply Rabsolu_no_R0; Apply H.
Qed.

(**********)
Lemma decreasing_prop : (Un:nat->R;m,n:nat) (Un_decreasing Un) -> (le m n) -> ``(Un n)<=(Un m)``.
Unfold Un_decreasing; Intros.
Induction n.
Induction m.
Right; Reflexivity.
Elim (le_Sn_O ? H0).
Cut (le m n)\/m=(S n).
Intro; Elim H1; Intro.
Apply Rle_trans with (Un n).
Apply H.
Apply Hrecn; Assumption.
Rewrite H2; Right; Reflexivity.
Inversion H0; [Right; Reflexivity | Left; Assumption].
Qed.

(* |x|^n/n! -> 0 *)
Lemma cv_speed_pow_fact : (x:R) (Un_cv [n:nat]``(pow x n)/(INR (fact n))`` R0).
Intro; Cut (Un_cv [n:nat]``(pow (Rabsolu x) n)/(INR (fact n))`` R0) -> (Un_cv [n:nat]``(pow x n)/(INR (fact n))`` ``0``).
Intro; Apply H.
Unfold Un_cv; Unfold R_dist; Intros; Case (Req_EM x R0); Intro.
Exists (S O); Intros.
Rewrite H1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_R0; Rewrite pow_ne_zero; [Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Assumption | Red; Intro; Rewrite H3 in H2; Elim (le_Sn_n ? H2)].
Assert H2 := (Rabsolu_pos_lt x H1); Pose M := (up (Rabsolu x)); Cut `0<=M`.
Intro; Elim (IZN M H3); Intros M_nat H4.
Pose Un := [n:nat]``(pow (Rabsolu x) (plus M_nat n))/(INR (fact (plus M_nat n)))``.
Cut (Un_cv Un R0); Unfold Un_cv; Unfold R_dist; Intros.
Elim (H5 eps H0); Intros N H6.
Exists (plus M_nat N); Intros; Cut (EX p:nat | (ge p N)/\n=(plus M_nat p)).
Intro; Elim H8; Intros p H9.
Elim H9; Intros; Rewrite H11; Unfold Un in H6; Apply H6; Assumption.
Exists (minus n M_nat).
Split.
Unfold ge; Apply simpl_le_plus_l with M_nat; Rewrite <- le_plus_minus.
Assumption.
Apply le_trans with (plus M_nat N).
Apply le_plus_l.
Assumption.
Apply le_plus_minus; Apply le_trans with (plus M_nat N); [Apply le_plus_l | Assumption].
Pose Vn := [n:nat]``(Rabsolu x)*(Un O)/(INR (S n))``.
Cut (le (1) M_nat).
Intro; Cut (n:nat)``0<(Un n)``.
Intro; Cut (Un_decreasing Un).
Intro; Cut (n:nat)``(Un (S n))<=(Vn n)``.
Intro; Cut (Un_cv Vn R0).
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H10 eps0 H5); Intros N1 H11.
Exists (S N1); Intros.
Cut (n:nat)``0<(Vn n)``.
Intro; Apply Rle_lt_trans with ``(Rabsolu ((Vn (pred n))-0))``.
Repeat Rewrite Rabsolu_right.
Unfold Rminus; Rewrite Ropp_O; Do 2 Rewrite Rplus_Or; Replace n with (S (pred n)).
Apply H9.
Inversion H12; Simpl; Reflexivity.
Apply Rle_sym1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Left; Apply H13.
Apply Rle_sym1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Left; Apply H7.
Apply H11; Unfold ge; Apply le_S_n; Replace (S (pred n)) with n; [Unfold ge in H12; Exact H12 | Inversion H12; Simpl; Reflexivity].
Intro; Apply Rlt_le_trans with (Un (S n0)); [Apply H7 | Apply H9].
Cut (cv_infty [n:nat](INR (S n))).
Intro; Cut (Un_cv [n:nat]``/(INR (S n))`` R0).
Unfold Un_cv R_dist; Intros; Unfold Vn.
Cut ``0<eps1/((Rabsolu x)*(Un O))``.
Intro; Elim (H11 ? H13); Intros N H14.
Exists N; Intros; Replace ``(Rabsolu x)*(Un O)/(INR (S n))-0`` with ``((Rabsolu x)*(Un O))*(/(INR (S n))-0)``; [Idtac | Unfold Rdiv; Ring].
Rewrite Rabsolu_mult; Apply Rlt_monotony_contra with ``/(Rabsolu ((Rabsolu x)*(Un O)))``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Apply prod_neq_R0.
Apply Rabsolu_no_R0; Assumption.
Assert H16 := (H7 O); Red; Intro; Rewrite H17 in H16; Elim (Rlt_antirefl ? H16).
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace ``/(Rabsolu ((Rabsolu x)*(Un O)))*eps1`` with ``eps1/((Rabsolu x)*(Un O))``.
Apply H14; Assumption.
Unfold Rdiv; Rewrite (Rabsolu_right ``(Rabsolu x)*(Un O)``).
Apply Rmult_sym.
Apply Rle_sym1; Apply Rmult_le_pos.
Apply Rabsolu_pos.
Left; Apply H7.
Apply Rabsolu_no_R0.
Apply prod_neq_R0; [Apply Rabsolu_no_R0; Assumption | Assert H16 := (H7 O); Red; Intro; Rewrite H17 in H16; Elim (Rlt_antirefl ? H16)].
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Assumption.
Apply H7.
Apply (cv_infty_cv_R0 [n:nat]``(INR (S n))``).
Intro; Apply not_O_INR; Discriminate.
Assumption.
Unfold cv_infty; Intro; Case (total_order_T M0 R0); Intro.
Elim s; Intro.
Exists O; Intros.
Apply Rlt_trans with R0; [Assumption | Apply lt_INR_0; Apply lt_O_Sn].
Exists O; Intros; Rewrite b; Apply lt_INR_0; Apply lt_O_Sn.
Pose M0_z := (up M0).
Assert H10 := (archimed M0).
Cut `0<=M0_z`.
Intro; Elim (IZN ? H11); Intros M0_nat H12.
Exists M0_nat; Intros.
Apply Rlt_le_trans with (IZR M0_z).
Elim H10; Intros; Assumption.
Rewrite H12; Rewrite <- INR_IZR_INZ; Apply le_INR.
Apply le_trans with n; [Assumption | Apply le_n_Sn].
Apply le_IZR; Left; Simpl; Unfold M0_z; Apply Rlt_trans with M0; [Assumption | Elim H10; Intros; Assumption].
Intro; Apply Rle_trans with ``(Rabsolu x)*(Un n)*/(INR (S n))``.
Unfold Un; Replace (plus M_nat (S n)) with (plus (plus M_nat n) (1)).
Rewrite pow_add; Replace (pow (Rabsolu x) (S O)) with (Rabsolu x); [Idtac | Simpl; Ring].
Unfold Rdiv; Rewrite <- (Rmult_sym (Rabsolu x)); Repeat Rewrite Rmult_assoc; Repeat Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply pow_lt; Assumption.
Replace (plus (plus M_nat n) (S O)) with (S (plus M_nat n)).
Rewrite fact_simpl; Rewrite mult_sym; Rewrite mult_INR; Rewrite Rinv_Rmult.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H10 := (sym_eq ? ? ? H9); Elim (fact_neq_0 ? H10).
Left; Apply Rinv_lt.
Apply Rmult_lt_pos; Apply lt_INR_0; Apply lt_O_Sn.
Apply lt_INR; Apply lt_n_S.
Pattern 1 n; Replace n with (plus O n); [Idtac | Reflexivity].
Apply lt_reg_r.
Apply lt_le_trans with (S O); [Apply lt_O_Sn | Assumption].
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply INR_eq; Rewrite S_INR; Do 3 Rewrite plus_INR; Reflexivity.
Apply INR_eq; Do 3 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Unfold Vn; Rewrite Rmult_assoc; Unfold Rdiv; Rewrite (Rmult_sym (Un O)); Rewrite (Rmult_sym (Un n)).
Repeat Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply lt_O_Sn.
Apply decreasing_prop; [Assumption | Apply le_O_n].
Unfold Un_decreasing; Intro; Unfold Un.
Replace (plus M_nat (S n)) with (plus (plus M_nat n) (1)).
Rewrite pow_add; Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply pow_lt; Assumption.
Replace (pow (Rabsolu x) (S O)) with (Rabsolu x); [Idtac | Simpl; Ring].
Replace (plus (plus M_nat n) (S O)) with (S (plus M_nat n)).
Apply Rle_monotony_contra with (INR (fact (S (plus M_nat n)))).
Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H9 := (sym_eq ? ? ? H8); Elim (fact_neq_0 ? H9).
Rewrite (Rmult_sym (Rabsolu x)); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Rewrite fact_simpl; Rewrite mult_INR; Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rle_trans with (INR M_nat).
Left; Rewrite INR_IZR_INZ.
Rewrite <- H4; Assert H8 := (archimed (Rabsolu x)); Elim H8; Intros; Assumption.
Apply le_INR; Apply le_trans with (S M_nat); [Apply le_n_Sn | Apply le_n_S; Apply le_plus_l].
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Rewrite S_INR; Do 3 Rewrite plus_INR; Reflexivity.
Apply INR_eq; Do 3 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Intro; Unfold Un; Unfold Rdiv; Apply Rmult_lt_pos.
Apply pow_lt; Assumption.
Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H8 := (sym_eq ? ? ? H7); Elim (fact_neq_0 ? H8).
Clear Un Vn; Apply INR_le; Simpl.
Induction M_nat.
Assert H6 := (archimed (Rabsolu x)); Fold M in H6; Elim H6; Intros. 
Rewrite H4 in H7; Rewrite <- INR_IZR_INZ in H7.
Simpl in H7; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H2 H7)).
Replace R1 with (INR (S O)); [Apply le_INR | Reflexivity]; Apply le_n_S; Apply le_O_n.
Apply le_IZR; Simpl; Left; Apply Rlt_trans with (Rabsolu x).
Assumption.
Elim (archimed (Rabsolu x)); Intros; Assumption.
Unfold Un_cv; Unfold R_dist; Intros; Elim (H eps H0); Intros.
Exists x0; Intros; Apply Rle_lt_trans with ``(Rabsolu ((pow (Rabsolu x) n)/(INR (fact n))-0))``.
Unfold Rminus; Rewrite Ropp_O; Do 2 Rewrite Rplus_Or; Rewrite (Rabsolu_right ``(pow (Rabsolu x) n)/(INR (fact n))``).
Unfold Rdiv; Rewrite Rabsolu_mult; Rewrite (Rabsolu_right ``/(INR (fact n))``).
Rewrite Pow_Rabsolu; Right; Reflexivity.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H4 := (sym_eq ? ? ? H3); Elim (fact_neq_0 ? H4).
Apply Rle_sym1; Unfold Rdiv; Apply Rmult_le_pos.
Case (Req_EM x R0); Intro.
Rewrite H3; Rewrite Rabsolu_R0.
Induction n; [Simpl; Left; Apply Rlt_R0_R1 | Simpl; Rewrite Rmult_Ol; Right; Reflexivity].
Left; Apply pow_lt; Apply Rabsolu_pos_lt; Assumption.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H4 := (sym_eq ? ? ? H3); Elim (fact_neq_0 ? H4).
Apply H1; Assumption.
Qed.
