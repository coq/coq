(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require Max.
Require Raxioms.
Require DiscrR.
Require Rbase.
Require Rseries.
Require Classical.


Definition Un_decreasing [Un:nat->R] : Prop := (n:nat) (Rle (Un (S n)) (Un n)).
Definition opp_sui [Un:nat->R] : nat->R := [n:nat]``-(Un n)``.
Definition majoree [Un:nat->R] : Prop := (bound (EUn Un)).
Definition minoree [Un:nat->R] : Prop := (bound (EUn (opp_sui Un))).

(* Toute suite croissante et majoree converge *)
(* Preuve inspiree de celle presente dans Rseries *)
Lemma growing_cv : (Un:nat->R) (Un_growing Un) -> (majoree Un) -> (sigTT R [l:R](Un_cv Un l)).
Unfold Un_growing Un_cv;Intros; 
 Generalize (complet (EUn Un) H0 (EUn_noempty Un));Intro H1.
 Elim H1;Clear H1;Intros;Split with x;Intros.
 Unfold is_lub in p;Unfold bound in H0;Unfold is_upper_bound in H0 p.
 Elim H0;Clear H0;Intros;Elim p;Clear p;Intros;
 Generalize (H3 x0 H0);Intro;Cut (n:nat)(Rle (Un n) x);Intro.
Cut (Ex [N:nat] (Rlt (Rminus x eps) (Un N))).
Intro;Elim H6;Clear H6;Intros;Split with x1.
Intros;Unfold R_dist;Apply (Rabsolu_def1 (Rminus (Un n) x) eps).
Unfold Rgt in H1.
 Apply (Rle_lt_trans (Rminus (Un n) x) R0 eps
                     (Rle_minus (Un n) x (H5 n)) H1).
Fold Un_growing in H;Generalize (growing_prop Un n x1 H H7);Intro.
 Generalize (Rlt_le_trans (Rminus x eps) (Un x1) (Un n) H6
                          (Rle_sym2 (Un x1) (Un n) H8));Intro;
 Generalize (Rlt_compatibility (Ropp x) (Rminus x eps) (Un n) H9);
 Unfold Rminus;Rewrite <-(Rplus_assoc (Ropp x) x (Ropp eps));
 Rewrite (Rplus_sym (Ropp x) (Un n));Fold (Rminus (Un n) x);
 Rewrite Rplus_Ropp_l;Rewrite (let (H1,H2)=(Rplus_ne (Ropp eps)) in H2);
 Trivial.
Cut ~((N:nat)(Rge (Rminus x eps) (Un N))).
Intro;Apply (not_all_not_ex nat ([N:nat](Rlt (Rminus x eps) (Un N)))).
 Red;Intro;Red in H6;Elim H6;Clear H6;Intro;
 Apply (Rlt_not_ge (Rminus x eps) (Un N) (H7 N)).
Red;Intro;Cut (N:nat)(Rle (Un N) (Rminus x eps)).
Intro;Generalize (Un_bound_imp Un (Rminus x eps) H7);Intro;
 Unfold is_upper_bound in H8;Generalize (H3 (Rminus x eps) H8);Intro;
 Generalize (Rle_minus x (Rminus x eps) H9);Unfold Rminus;
 Rewrite Ropp_distr1;Rewrite <- Rplus_assoc;Rewrite Rplus_Ropp_r.
 Rewrite (let (H1,H2)=(Rplus_ne (Ropp (Ropp eps))) in H2);
 Rewrite Ropp_Ropp;Intro;Unfold Rgt in H1;
 Generalize (Rle_not eps R0 H1);Intro;Auto.
Intro;Elim (H6 N);Intro;Unfold Rle.
Left;Unfold Rgt in H7;Assumption.
Right;Auto.
Apply (H2 (Un n) (Un_in_EUn Un n)).
Qed.

(* Pour toute suite decroissante, la suite "opposee" est croissante *)
Lemma decreasing_growing : (Un:nat->R) (Un_decreasing Un) -> (Un_growing (opp_sui Un)).
Intro.
Unfold Un_growing opp_sui Un_decreasing.
Intros.
Apply Rle_Ropp1.
Apply H.
Qed.

(* Toute suite decroissante et minoree converge *)
Lemma decreasing_cv : (Un:nat->R) (Un_decreasing Un) -> (minoree Un) -> (sigTT R [l:R](Un_cv Un l)).
Intros.
Cut (sigTT R [l:R](Un_cv (opp_sui Un) l)) -> (sigTT R [l:R](Un_cv Un l)).
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
Unfold opp_sui in p.
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
Lemma maj_sup : (Un:nat->R) (majoree Un) -> (sigTT R [l:R](is_lub (EUn Un) l)).
Intros.
Unfold majoree in H.
Apply complet.
Assumption.
Exists (Un O).
Unfold EUn.
Exists O; Reflexivity.
Qed.

(**********)
Lemma min_inf : (Un:nat->R) (minoree Un) -> (sigTT R [l:R](is_lub (EUn (opp_sui Un)) l)).
Intros; Unfold minoree in H.
Apply complet.
Assumption.
Exists ``-(Un O)``.
Exists O.
Reflexivity.
Qed.

Definition majorant [Un:nat->R;pr:(majoree Un)] : R := Cases (maj_sup Un pr) of (existTT a b) => a end.

Definition minorant [Un:nat->R;pr:(minoree Un)] : R := Cases (min_inf Un pr) of (existTT a b) => ``-a`` end.

(* Conservation de la propriete de majoration par extraction *)
Lemma maj_ss : (Un:nat->R;k:nat) (majoree Un) -> (majoree [i:nat](Un (plus k i))).
Intros.
Unfold majoree in H.
Unfold bound in H.
Elim H; Intros.
Unfold is_upper_bound in H0.
Unfold majoree.
Exists x.
Unfold is_upper_bound.
Intros.
Apply H0.
Elim H1; Intros.
Exists (plus k x1); Assumption.
Qed.

(* Conservation de la propriete de minoration par extraction *)
Lemma min_ss : (Un:nat->R;k:nat) (minoree Un) -> (minoree [i:nat](Un (plus k i))).
Intros.
Unfold minoree in H.
Unfold bound in H.
Elim H; Intros.
Unfold is_upper_bound in H0.
Unfold minoree.
Exists x.
Unfold is_upper_bound.
Intros.
Apply H0.
Elim H1; Intros.
Exists (plus k x1); Assumption.
Qed.

Definition suite_majorant [Un:nat->R;pr:(majoree Un)] : nat -> R := [i:nat](majorant [k:nat](Un (plus i k)) (maj_ss Un i pr)).

Definition suite_minorant [Un:nat->R;pr:(minoree Un)] : nat -> R := [i:nat](minorant [k:nat](Un (plus i k)) (min_ss Un i pr)).

(**********)
Lemma Rle_Rle_eq : (a,b:R) ``a<=b`` -> ``b<=a`` -> ``a==b``.
Intros.
Case (total_order_T a b); Intro.
Elim s; Intros.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? a0 H0)).
Assumption.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? r H)).
Qed.

(* La suite des majorants est decroissante *)
Lemma Wn_decreasing : (Un:nat->R;pr:(majoree Un)) (Un_decreasing (suite_majorant Un pr)). 
Intros.
Unfold Un_decreasing.
Intro.
Unfold suite_majorant.
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
Apply Rle_Rle_eq; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus n k)) (maj_ss Un n pr)).
Trivial.
Cut (is_lub (EUn [k:nat](Un (plus (S n) k))) (majorant ([k:nat](Un (plus (S n) k))) (maj_ss Un (S n) pr))).
Intro.
Unfold is_lub in p; Unfold is_lub in H1.
Elim p; Intros; Elim H1; Intros.
Assert H6 := (H5 x H2).
Assert H7 := (H3 (majorant ([k:nat](Un (plus (S n) k))) (maj_ss Un (S n) pr)) H4).
Apply Rle_Rle_eq; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus (S n) k)) (maj_ss Un (S n) pr)).
Trivial.
Qed.

(* La suite des minorants est croissante *)
Lemma Vn_growing : (Un:nat->R;pr:(minoree Un)) (Un_growing (suite_minorant Un pr)).
Intros.
Unfold Un_growing.
Intro.
Unfold suite_minorant.
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
Unfold opp_sui in H6.
Unfold opp_sui.
Replace (plus n (plus (S O) x2)) with (plus (S n) x2).
Assumption.
Replace (S n) with (plus (1) n); [Ring | Ring].
Cut (is_lub (EUn (opp_sui [k:nat](Un (plus n k)))) (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr)))).
Intro.
Unfold is_lub in p0; Unfold is_lub in H1.
Elim p0; Intros; Elim H1; Intros.
Assert H6 := (H5 x0 H2).
Assert H7 := (H3 (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr))) H4).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr))).
Apply eq_Ropp; Apply Rle_Rle_eq; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus n k)) (min_ss Un n pr)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Cut (is_lub (EUn (opp_sui [k:nat](Un (plus (S n) k)))) (Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr)))).
Intro.
Unfold is_lub in p; Unfold is_lub in H1.
Elim p; Intros; Elim H1; Intros.
Assert H6 := (H5 x H2).
Assert H7 := (H3 (Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr))) H4).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus (S n) k))) (min_ss Un (S n) pr))).
Apply eq_Ropp; Apply Rle_Rle_eq; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus (S n) k)) (min_ss Un (S n) pr)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Qed.

(* Encadrement Vn,Un,Wn *)
Lemma Vn_Un_Wn_order : (Un:nat->R;pr1:(majoree Un);pr2:(minoree Un)) (n:nat) ``((suite_minorant Un pr2) n)<=(Un n)<=((suite_majorant Un pr1) n)``. 
Intros.
Split.
Unfold suite_minorant.
Cut (sigTT R [l:R](is_lub (EUn (opp_sui [i:nat](Un (plus n i)))) l)).
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
Unfold opp_sui.
Replace (plus n O) with n; [Reflexivity | Ring].
Cut (is_lub (EUn (opp_sui [k:nat](Un (plus n k)))) (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2)))).
Intro.
Unfold is_lub in p; Unfold is_lub in H.
Elim p; Intros; Elim H; Intros.
Assert H4 := (H3 x H0).
Assert H5 := (H1 (Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2))) H2).
Rewrite <- (Ropp_Ropp (minorant ([k:nat](Un (plus n k))) (min_ss Un n pr2))).
Apply eq_Ropp; Apply Rle_Rle_eq; Assumption.
Unfold minorant.
Case (min_inf [k:nat](Un (plus n k)) (min_ss Un n pr2)).
Intro; Rewrite Ropp_Ropp.
Trivial.
Apply min_inf.
Apply min_ss; Assumption.
Unfold suite_majorant.
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
Apply Rle_Rle_eq; Assumption.
Unfold majorant.
Case (maj_sup [k:nat](Un (plus n k)) (maj_ss Un n pr1)).
Intro; Trivial.
Apply maj_sup.
Apply maj_ss; Assumption.
Qed.

(* La suite des minorants est majoree *)
Lemma min_maj : (Un:nat->R;pr1:(majoree Un);pr2:(minoree Un)) (majoree (suite_minorant Un pr2)).
Intros.
Assert H := (Vn_Un_Wn_order Un pr1 pr2).
Unfold majoree.
Unfold bound.
Unfold majoree in pr1.
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

(* La suite des majorants est minoree *)
Lemma maj_min : (Un:nat->R;pr1:(majoree Un);pr2:(minoree Un)) (minoree (suite_majorant Un pr1)). 
Intros.
Assert H := (Vn_Un_Wn_order Un pr1 pr2).
Unfold minoree.
Unfold bound.
Unfold minoree in pr2.
Unfold bound in pr2.
Elim pr2; Intros.
Exists x.
Unfold is_upper_bound.
Intros.
Unfold is_upper_bound in H0.
Elim H1; Intros.
Rewrite H2.
Apply Rle_trans with ((opp_sui Un) x1).
Assert H3 := (H x1); Elim H3; Intros.
Unfold opp_sui; Apply Rle_Ropp1.
Assumption.
Apply H0.
Exists x1; Reflexivity.
Qed.

(* Toute suite de Cauchy est majoree *)
Lemma cauchy_maj : (Un:nat->R) (Cauchy_crit Un) -> (majoree Un).
Intros.
Unfold majoree.
Apply cauchy_bound.
Assumption.
Qed.

(**********)
Lemma cauchy_opp : (Un:nat->R) (Cauchy_crit Un) -> (Cauchy_crit (opp_sui Un)).
Intro.
Unfold Cauchy_crit.
Unfold R_dist.
Intros.
Elim (H eps H0); Intros.
Exists x; Intros.
Unfold opp_sui.
Rewrite <- Rabsolu_Ropp.
Replace ``-( -(Un n)- -(Un m))`` with ``(Un n)-(Un m)``; [Apply H1; Assumption | Ring].
Qed.

(* Toute suite de Cauchy est minoree *)
Lemma cauchy_min : (Un:nat->R) (Cauchy_crit Un) -> (minoree Un).
Intros.
Unfold minoree.
Assert H0 := (cauchy_opp ? H).
Apply cauchy_bound.
Assumption.
Qed.

(* La suite des majorants converge *)
Lemma maj_cv : (Un:nat->R;pr:(Cauchy_crit Un)) (sigTT R [l:R](Un_cv (suite_majorant Un (cauchy_maj Un pr)) l)).
Intros.
Apply decreasing_cv.
Apply Wn_decreasing.
Apply maj_min.
Apply cauchy_min.
Assumption.
Qed.

(* La suite des minorants converge *)
Lemma min_cv : (Un:nat->R;pr:(Cauchy_crit Un)) (sigTT R [l:R](Un_cv (suite_minorant Un (cauchy_min Un pr)) l)).
Intros.
Apply growing_cv.
Apply Vn_growing.
Apply min_maj.
Apply cauchy_maj.
Assumption.
Qed.

(**********)
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

(**********)
Lemma not_Rlt : (r1,r2:R)~(``r1<r2``)->``r1>=r2``.
Intros r1 r2 ; Generalize (total_order r1 r2) ; Unfold Rge.
Tauto.
Qed. 

(* On peut approcher la borne sup de toute suite majoree *)
Lemma approx_maj : (Un:nat->R;pr:(majoree Un)) (eps:R) ``0<eps`` -> (EX k : nat | ``(Rabsolu ((majorant Un pr)-(Un k))) < eps``).
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

(* On peut approcher la borne inf de toute suite minoree *)
Lemma approx_min : (Un:nat->R;pr:(minoree Un)) (eps:R) ``0<eps`` -> (EX k :nat | ``(Rabsolu ((minorant Un pr)-(Un k))) < eps``).
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
Cut (is_lub (EUn (opp_sui Un)) ``-(minorant Un pr)``).
Intro.
Unfold is_lub in H3.
Unfold is_upper_bound in H3.
Elim H3; Intros.
Cut (n:nat)``eps<=(Un n)-(minorant Un pr)``.
Intro.
Cut (n:nat)``((opp_sui Un) n)<=-(minorant Un pr)-eps``.
Intro.
Cut ((x:R)(EUn (opp_sui Un) x)->``x <= -(minorant Un pr)-eps``).
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
Unfold opp_sui.
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

(****************************************************)
(*              R est complet :                     *)
(*    Toute suite de Cauchy de (R,| |) converge     *)
(*                                                  *)
(*  Preuve a l'aide des suites adjacentes Vn et Wn  *)
(****************************************************)

Theorem R_complet : (Un:nat->R) (Cauchy_crit Un) -> (sigTT R [l:R](Un_cv Un l)).
Intros.
Pose Vn := (suite_minorant Un (cauchy_min Un H)).
Pose Wn := (suite_majorant Un (cauchy_maj Un H)).
Assert H0 := (maj_cv Un H).
Fold Wn in H0.
Assert H1 := (min_cv Un H).
Fold Vn in H1.
Elim H0; Intros.
Elim H1; Intros.
Cut x==x0.
Intros.
Apply existTT with x.
Rewrite <- H2 in p0.
Unfold Un_cv.
Intros.
Unfold Un_cv in p; Unfold Un_cv in p0.
Cut ``0<eps/3``.
Intro.
Elim (p ``eps/3`` H4); Intros.
Elim (p0 ``eps/3`` H4); Intros.
Exists (max x1 x2).
Intros.
Unfold R_dist.
Apply Rle_lt_trans with ``(Rabsolu ((Un n)-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Replace ``(Un n)-x`` with ``((Un n)-(Vn n))+((Vn n)-x)``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((Wn n)-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu ((Vn n)-x))``).
Apply Rle_compatibility.
Repeat Rewrite Rabsolu_right.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-(Vn n)``); Apply Rle_compatibility.
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Assumption.
Apply Rle_sym1.
Unfold Rminus; Apply Rle_anti_compatibility with (Vn n).
Rewrite Rplus_Or.
Replace ``(Vn n)+((Wn n)+ -(Vn n))`` with (Wn n); [Idtac | Ring].
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Apply Rle_trans with (Un n); Assumption.
Apply Rle_sym1.
Unfold Rminus; Apply Rle_anti_compatibility with (Vn n).
Rewrite Rplus_Or.
Replace ``(Vn n)+((Un n)+ -(Vn n))`` with (Un n); [Idtac | Ring].
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Assumption.
Apply Rle_lt_trans with ``(Rabsolu ((Wn n)-x))+(Rabsolu (x-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu ((Vn n)-x))``).
Apply Rle_compatibility.
Replace ``(Wn n)-(Vn n)`` with ``((Wn n)-x)+(x-(Vn n))``; [Apply Rabsolu_triang | Ring].
Apply Rlt_le_trans with ``eps/3+eps/3+eps/3``.
Repeat Apply Rplus_lt.
Unfold R_dist in H5.
Apply H5.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_l.
Assumption.
Rewrite <- Rabsolu_Ropp.
Replace ``-(x-(Vn n))`` with ``(Vn n)-x``; [Idtac | Ring].
Unfold R_dist in H6.
Apply H6.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_r.
Assumption.
Unfold R_dist in H6.
Apply H6.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_r.
Assumption.
Right.
Pattern 4 eps; Replace ``eps`` with ``3*eps/3``.
Ring.
Unfold Rdiv; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m; DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Apply cond_eq.
Intros.
Cut ``0<eps/5``.
Intro.
Unfold Un_cv in p; Unfold Un_cv in p0.
Unfold R_dist in p; Unfold R_dist in p0.
Elim (p ``eps/5`` H3); Intros N1 H4.
Elim (p0 ``eps/5`` H3); Intros N2 H5.
Unfold Cauchy_crit in H.
Unfold R_dist in H.
Elim (H ``eps/5`` H3); Intros N3 H6.
Pose N := (max (max N1 N2) N3).
Apply Rle_lt_trans with ``(Rabsolu (x-(Wn N)))+(Rabsolu ((Wn N)-x0))``.
Replace ``x-x0`` with ``(x-(Wn N))+((Wn N)-x0)``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu (x-(Wn N)))+(Rabsolu ((Wn N)-(Vn N)))+(Rabsolu (((Vn N)-x0)))``.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Replace ``(Wn N)-x0`` with ``((Wn N)-(Vn N))+((Vn N)-x0)``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``eps/5+3*eps/5+eps/5``.
Repeat Apply Rplus_lt.
Rewrite <- Rabsolu_Ropp.
Replace ``-(x-(Wn N))`` with ``(Wn N)-x``; [Apply H4 | Ring].
Unfold ge N.
Apply le_trans with (max N1 N2); Apply le_max_l.
Unfold Wn Vn.
Unfold suite_majorant suite_minorant.
Assert H7 := (approx_maj [k:nat](Un (plus N k)) (maj_ss Un N (cauchy_maj Un H))).
Assert H8 := (approx_min [k:nat](Un (plus N k)) (min_ss Un N (cauchy_min Un H))).
Cut (Wn N)==(majorant ([k:nat](Un (plus N k))) (maj_ss Un N (cauchy_maj Un H))).
Cut (Vn N)==(minorant ([k:nat](Un (plus N k))) (min_ss Un N (cauchy_min Un H))).
Intros.
Rewrite <- H9; Rewrite <- H10.
Rewrite <- H9 in H8.
Rewrite <- H10 in H7.
Elim (H7 ``eps/5`` H3); Intros k2 H11.
Elim (H8 ``eps/5`` H3); Intros k1 H12.
Apply Rle_lt_trans with ``(Rabsolu ((Wn N)-(Un (plus N k2))))+(Rabsolu ((Un (plus N k2))-(Vn N)))``.
Replace ``(Wn N)-(Vn N)`` with ``((Wn N)-(Un (plus N k2)))+((Un (plus N k2))-(Vn N))``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((Wn N)-(Un (plus N k2))))+(Rabsolu ((Un (plus N k2))-(Un (plus N k1))))+(Rabsolu ((Un (plus N k1))-(Vn N)))``.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Replace ``(Un (plus N k2))-(Vn N)`` with ``((Un (plus N k2))-(Un (plus N k1)))+((Un (plus N k1))-(Vn N))``; [Apply Rabsolu_triang | Ring].
Replace ``3*eps/5`` with ``eps/5+eps/5+eps/5``; [Repeat Apply Rplus_lt | Ring].
Assumption.
Apply H6.
Unfold ge.
Apply le_trans with N.
Unfold N; Apply le_max_r.
Apply le_plus_l.
Unfold ge.
Apply le_trans with N.
Unfold N; Apply le_max_r.
Apply le_plus_l.
Rewrite <- Rabsolu_Ropp.
Replace ``-((Un (plus N k1))-(Vn N))`` with ``(Vn N)-(Un (plus N k1))``; [Assumption | Ring].
Reflexivity.
Reflexivity.
Apply H5.
Unfold ge; Apply le_trans with (max N1 N2).
Apply le_max_r.
Unfold N; Apply le_max_l.
Pattern 4 eps; Replace ``eps`` with ``5*eps/5``.
Ring.
Unfold Rdiv; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv.
Sup0; Try Apply lt_O_Sn.
Qed.