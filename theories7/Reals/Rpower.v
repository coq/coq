(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)
(*i Due to L.Thery i*) 

(************************************************************)
(* Definitions of log and Rpower : R->R->R; main properties *)
(************************************************************)

Require Rbase.
Require Rfunctions.
Require SeqSeries.
Require Rtrigo.
Require Ranalysis1.
Require Exp_prop.
Require Rsqrt_def.
Require R_sqrt.
Require MVT.
Require Ranalysis4.
V7only [Import R_scope.]. Open Local Scope R_scope.

Lemma P_Rmin: (P : R ->  Prop) (x, y : R) (P x) -> (P y) ->  (P (Rmin x y)).
Intros P x y H1 H2; Unfold Rmin; Case (total_order_Rle x y); Intro; Assumption.
Qed.

Lemma exp_le_3 :  ``(exp 1)<=3``.
Assert exp_1 : ``(exp 1)<>0``.
Assert H0 := (exp_pos R1); Red; Intro; Rewrite H in H0; Elim (Rlt_antirefl ? H0).
Apply Rle_monotony_contra with ``/(exp 1)``.
Apply Rlt_Rinv; Apply exp_pos.
Rewrite <- Rinv_l_sym.
Apply Rle_monotony_contra with ``/3``.
Apply Rlt_Rinv; Sup0.
Rewrite Rmult_1r; Rewrite <- (Rmult_sym ``3``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Replace ``/(exp 1)`` with ``(exp (-1))``.
Unfold exp; Case (exist_exp ``-1``); Intros; Simpl; Unfold exp_in in e; Assert H := (alternated_series_ineq [i:nat]``/(INR (fact i))`` x (S O)).
Cut ``(sum_f_R0 (tg_alt [([i:nat]``/(INR (fact i))``)]) (S (mult (S (S O)) (S O)))) <= x <= (sum_f_R0 (tg_alt [([i:nat]``/(INR (fact i))``)]) (mult (S (S O)) (S O)))``.
Intro; Elim H0; Clear H0; Intros H0 _; Simpl in H0; Unfold tg_alt in H0; Simpl in H0.
Replace ``/3`` with ``1*/1+ -1*1*/1+ -1*( -1*1)*/2+ -1*( -1*( -1*1))*/(2+1+1+1+1)``.
Apply H0.
Repeat Rewrite Rinv_R1; Repeat Rewrite Rmult_1r; Rewrite Ropp_mul1; Rewrite Rmult_1l; Rewrite Ropp_Ropp; Rewrite Rplus_Ropp_r; Rewrite Rmult_1r; Rewrite Rplus_Ol; Rewrite Rmult_1l; Apply r_Rmult_mult with ``6``.
Rewrite Rmult_Rplus_distr; Replace ``2+1+1+1+1`` with ``6``.
Rewrite <- (Rmult_sym ``/6``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Replace ``6`` with ``2*3``.
Do 2 Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Rewrite (Rmult_sym ``3``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Ring.
DiscrR.
DiscrR.
Ring.
DiscrR.
Ring.
DiscrR.
Apply H.
Unfold Un_decreasing; Intros; Apply Rle_monotony_contra with ``(INR (fact n))``.
Apply INR_fact_lt_0.
Apply Rle_monotony_contra with ``(INR (fact (S n)))``.
Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Apply le_INR; Apply fact_growing; Apply le_n_Sn.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Assert H0 := (cv_speed_pow_fact R1); Unfold Un_cv; Unfold Un_cv in H0; Intros; Elim (H0 ? H1); Intros; Exists x0; Intros; Unfold R_dist in H2; Unfold R_dist; Replace ``/(INR (fact n))`` with ``(pow 1 n)/(INR (fact n))``.
Apply (H2 ? H3).
Unfold Rdiv; Rewrite pow1; Rewrite Rmult_1l; Reflexivity.
Unfold infinit_sum in e; Unfold Un_cv tg_alt; Intros; Elim (e ? H0); Intros; Exists x0; Intros; Replace (sum_f_R0 ([i:nat]``(pow ( -1) i)*/(INR (fact i))``) n) with (sum_f_R0 ([i:nat]``/(INR (fact i))*(pow ( -1) i)``) n).
Apply (H1 ? H2).
Apply sum_eq; Intros; Apply Rmult_sym.
Apply r_Rmult_mult with ``(exp 1)``.
Rewrite <- exp_plus; Rewrite Rplus_Ropp_r; Rewrite exp_0; Rewrite <- Rinv_r_sym.
Reflexivity.
Assumption.
Assumption.
DiscrR.
Assumption.
Qed.

(******************************************************************)
(*                        Properties of  Exp                      *)
(******************************************************************)

Theorem exp_increasing: (x, y : R) ``x<y`` -> ``(exp x)<(exp y)``.
Intros x y H.
Assert H0 : (derivable exp).
Apply derivable_exp.
Assert H1 := (positive_derivative ? H0).
Unfold strict_increasing in H1.
Apply H1.
Intro.
Replace (derive_pt exp x0 (H0 x0)) with (exp x0).
Apply exp_pos.
Symmetry; Apply derive_pt_eq_0.
Apply (derivable_pt_lim_exp x0).
Apply H.
Qed.
 
Theorem exp_lt_inv: (x, y : R) ``(exp x)<(exp y)`` -> ``x<y``.
Intros x y H; Case (total_order x y); [Intros H1 | Intros [H1|H1]].
Assumption.
Rewrite H1 in H; Elim (Rlt_antirefl ? H).
Assert H2 := (exp_increasing ? ? H1).
Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H H2)).
Qed.
 
Lemma exp_ineq1 : (x:R) ``0<x`` -> ``1+x < (exp x)``.
Intros; Apply Rlt_anti_compatibility with ``-(exp 0)``; Rewrite <- (Rplus_sym (exp x)); Assert H0 := (MVT_cor1 exp R0 x derivable_exp H); Elim H0; Intros; Elim H1; Intros; Unfold Rminus in H2; Rewrite H2; Rewrite Ropp_O; Rewrite Rplus_Or; Replace (derive_pt exp x0 (derivable_exp x0)) with (exp x0).
Rewrite exp_0; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Pattern 1 x; Rewrite <- Rmult_1r; Rewrite (Rmult_sym (exp x0)); Apply Rlt_monotony.
Apply H.
Rewrite <- exp_0; Apply exp_increasing; Elim H3; Intros; Assumption.
Symmetry; Apply derive_pt_eq_0; Apply derivable_pt_lim_exp.
Qed.

Lemma ln_exists1 : (y:R) ``0<y``->``1<=y``->(sigTT R [z:R]``y==(exp z)``).
Intros; Pose f := [x:R]``(exp x)-y``; Cut ``(f 0)<=0``.
Intro; Cut (continuity f).
Intro; Cut ``0<=(f y)``.
Intro; Cut ``(f 0)*(f y)<=0``.
Intro; Assert X := (IVT_cor f R0 y H2 (Rlt_le ? ? H) H4); Elim X; Intros t H5; Apply existTT with t; Elim H5; Intros; Unfold f in H7; Apply Rminus_eq_right; Exact H7.
Pattern 2 R0; Rewrite <- (Rmult_Or (f y)); Rewrite (Rmult_sym (f R0)); Apply Rle_monotony; Assumption.
Unfold f; Apply Rle_anti_compatibility with y; Left; Apply Rlt_trans with ``1+y``.
Rewrite <- (Rplus_sym y); Apply Rlt_compatibility; Apply Rlt_R0_R1.
Replace ``y+((exp y)-y)`` with (exp y); [Apply (exp_ineq1 y H) | Ring].
Unfold f; Change (continuity (minus_fct exp (fct_cte y))); Apply continuity_minus; [Apply derivable_continuous; Apply derivable_exp | Apply derivable_continuous; Apply derivable_const].
Unfold f; Rewrite exp_0; Apply Rle_anti_compatibility with y; Rewrite Rplus_Or; Replace ``y+(1-y)`` with R1; [Apply H0 | Ring].
Qed.

(**********)
Lemma ln_exists : (y:R) ``0<y`` -> (sigTT R [z:R]``y==(exp z)``).
Intros; Case (total_order_Rle R1 y); Intro.
Apply (ln_exists1 ? H r).
Assert H0 : ``1<=/y``.
Apply Rle_monotony_contra with y.
Apply H.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Left; Apply (not_Rle ? ? n).
Red; Intro; Rewrite H0 in H; Elim (Rlt_antirefl ? H).
Assert H1 : ``0</y``.
Apply Rlt_Rinv; Apply H.
Assert H2 := (ln_exists1 ? H1 H0); Elim H2; Intros; Apply existTT with ``-x``; Apply r_Rmult_mult with ``(exp x)/y``.
Unfold Rdiv; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite <- (Rmult_sym ``/y``); Rewrite Rmult_assoc; Rewrite <- exp_plus; Rewrite Rplus_Ropp_r; Rewrite exp_0; Rewrite Rmult_1r; Symmetry; Apply p.
Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Unfold Rdiv; Apply prod_neq_R0.
Assert H3 := (exp_pos x); Red; Intro; Rewrite H4 in H3; Elim (Rlt_antirefl ? H3).
Apply Rinv_neq_R0; Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Qed.

(* Definition of log R+* -> R *)
Definition Rln [y:posreal] : R := Cases (ln_exists (pos y) (RIneq.cond_pos y)) of (existTT a b) => a end.

(* Extension on R *)
Definition ln : R->R := [x:R](Cases (total_order_Rlt R0 x) of
      (leftT a) => (Rln (mkposreal x a)) 
    | (rightT a) => R0 end).

Lemma exp_ln :  (x : R) ``0<x`` ->  (exp (ln x)) == x.
Intros; Unfold ln; Case (total_order_Rlt R0 x); Intro.
Unfold Rln; Case (ln_exists (mkposreal x r) (RIneq.cond_pos (mkposreal x r))); Intros.
Simpl in e; Symmetry; Apply e.
Elim n; Apply H.
Qed.

Theorem exp_inv: (x, y : R) (exp x) == (exp y) ->  x == y.
Intros x y H; Case (total_order x y); [Intros H1 | Intros [H1|H1]]; Auto; Assert H2 := (exp_increasing ? ? H1); Rewrite H in H2; Elim (Rlt_antirefl ? H2).
Qed.
 
Theorem exp_Ropp: (x : R)  ``(exp (-x)) == /(exp x)``.
Intros x; Assert H : ``(exp x)<>0``.
Assert H := (exp_pos x); Red; Intro; Rewrite H0 in H; Elim (Rlt_antirefl ? H).
Apply r_Rmult_mult with r := (exp x).
Rewrite <- exp_plus; Rewrite Rplus_Ropp_r; Rewrite exp_0.
Apply Rinv_r_sym.
Apply H.
Apply H.
Qed.
 
(******************************************************************)
(*                        Properties of  Ln                       *)
(******************************************************************)

Theorem ln_increasing:
 (x, y : R) ``0<x`` -> ``x<y`` -> ``(ln x) < (ln y)``.
Intros x y H H0; Apply exp_lt_inv.
Repeat  Rewrite exp_ln. 
Apply H0.
Apply Rlt_trans with x; Assumption.
Apply H.
Qed.

Theorem ln_exp: (x : R)  (ln (exp x)) == x.
Intros x; Apply exp_inv.
Apply exp_ln.
Apply exp_pos.
Qed.
 
Theorem ln_1: ``(ln 1) == 0``.
Rewrite <- exp_0; Rewrite ln_exp; Reflexivity.
Qed.
 
Theorem ln_lt_inv:
 (x, y : R) ``0<x`` -> ``0<y`` -> ``(ln x)<(ln y)`` ->  ``x<y``.
Intros x y H H0 H1; Rewrite <- (exp_ln x); Try Rewrite <- (exp_ln y).
Apply exp_increasing; Apply H1.
Assumption. 
Assumption.
Qed.
 
Theorem ln_inv: (x, y : R) ``0<x`` -> ``0<y`` -> (ln x) == (ln y) ->  x == y.
Intros x y H H0 H'0; Case (total_order x y); [Intros H1 | Intros [H1|H1]]; Auto.
Assert H2 := (ln_increasing ? ? H H1); Rewrite H'0 in H2; Elim (Rlt_antirefl ? H2).
Assert H2 := (ln_increasing ? ? H0 H1); Rewrite H'0 in H2; Elim (Rlt_antirefl ? H2).
Qed.
 
Theorem ln_mult: (x, y : R) ``0<x`` -> ``0<y`` ->  ``(ln (x*y)) == (ln x)+(ln y)``.
Intros x y H H0; Apply exp_inv.
Rewrite exp_plus.
Repeat Rewrite exp_ln.
Reflexivity.
Assumption.
Assumption.
Apply Rmult_lt_pos; Assumption.
Qed.

Theorem ln_Rinv: (x : R) ``0<x`` ->  ``(ln (/x)) == -(ln x)``.
Intros x H; Apply exp_inv; Repeat (Rewrite exp_ln Orelse Rewrite exp_Ropp).
Reflexivity.
Assumption. 
Apply Rlt_Rinv; Assumption.
Qed.

Theorem ln_continue:
 (y : R) ``0<y`` ->  (continue_in ln [x : R]  (Rlt R0 x) y).
Intros y H.
Unfold continue_in limit1_in limit_in; Intros eps Heps.
Cut (Rlt R1 (exp eps)); [Intros H1 | Idtac].
Cut (Rlt (exp (Ropp eps)) R1); [Intros H2 | Idtac].
Exists
 (Rmin (Rmult y (Rminus (exp eps) R1)) (Rmult y (Rminus R1 (exp (Ropp eps)))));
 Split.
Red; Apply P_Rmin.
Apply Rmult_lt_pos.
Assumption.
Apply Rlt_anti_compatibility with R1.
Rewrite Rplus_Or; Replace ``(1+((exp eps)-1))`` with (exp eps); [Apply H1 | Ring].
Apply Rmult_lt_pos.
Assumption.
Apply Rlt_anti_compatibility with ``(exp (-eps))``.
Rewrite Rplus_Or; Replace ``(exp ( -eps))+(1-(exp ( -eps)))`` with R1; [Apply H2 | Ring].
Unfold dist R_met R_dist; Simpl.
Intros x ((H3, H4), H5).
Cut (Rmult y (Rmult x (Rinv y))) == x.
Intro Hxyy. 
Replace (Rminus (ln x) (ln y)) with (ln (Rmult x (Rinv y))).
Case (total_order x y); [Intros Hxy | Intros [Hxy|Hxy]].
Rewrite Rabsolu_left.
Apply Ropp_Rlt; Rewrite Ropp_Ropp.
Apply exp_lt_inv.
Rewrite exp_ln.
Apply Rlt_monotony_contra with z := y.
Apply H.
Rewrite Hxyy.
Apply Ropp_Rlt.
Apply Rlt_anti_compatibility with r := y.
Replace (Rplus y (Ropp (Rmult y (exp (Ropp eps)))))
     with (Rmult y (Rminus R1 (exp (Ropp eps)))); [Idtac | Ring].
Replace (Rplus y (Ropp x)) with (Rabsolu (Rminus x y)); [Idtac | Ring].
Apply Rlt_le_trans with 1 := H5; Apply Rmin_r.
Rewrite Rabsolu_left; [Ring | Idtac].
Apply (Rlt_minus ? ? Hxy).
Apply Rmult_lt_pos; [Apply H3  | Apply (Rlt_Rinv ? H)].
Rewrite <- ln_1.
Apply ln_increasing.
Apply Rmult_lt_pos; [Apply H3  | Apply (Rlt_Rinv ? H)].
Apply Rlt_monotony_contra with z := y.
Apply H.
Rewrite Hxyy; Rewrite Rmult_1r; Apply Hxy.
Rewrite Hxy; Rewrite Rinv_r.
Rewrite ln_1; Rewrite Rabsolu_R0; Apply Heps.
Red; Intro; Rewrite H0 in H; Elim (Rlt_antirefl ? H).
Rewrite Rabsolu_right.
Apply exp_lt_inv.
Rewrite exp_ln.
Apply Rlt_monotony_contra with z := y.
Apply H.
Rewrite Hxyy.
Apply Rlt_anti_compatibility with r := (Ropp y).
Replace (Rplus (Ropp y) (Rmult y (exp eps)))
     with (Rmult y (Rminus (exp eps) R1)); [Idtac | Ring].
Replace (Rplus (Ropp y) x) with (Rabsolu (Rminus x y)); [Idtac | Ring].
Apply Rlt_le_trans with 1 := H5; Apply Rmin_l.
Rewrite Rabsolu_right; [Ring | Idtac].
Left; Apply (Rgt_minus ? ? Hxy).
Apply Rmult_lt_pos; [Apply H3  | Apply (Rlt_Rinv ? H)].
Rewrite <- ln_1.
Apply Rgt_ge; Red; Apply ln_increasing.
Apply Rlt_R0_R1.
Apply Rlt_monotony_contra with z := y.
Apply H.
Rewrite Hxyy; Rewrite Rmult_1r; Apply Hxy.
Rewrite ln_mult.
Rewrite ln_Rinv.
Ring.
Assumption.
Assumption.
Apply Rlt_Rinv; Assumption.
Rewrite (Rmult_sym x); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Ring.
Red; Intro; Rewrite H0 in H; Elim (Rlt_antirefl ? H).
Apply Rlt_monotony_contra with (exp eps).
Apply exp_pos.
Rewrite <- exp_plus; Rewrite Rmult_1r; Rewrite Rplus_Ropp_r; Rewrite exp_0; Apply H1.
Rewrite <- exp_0.
Apply exp_increasing; Apply Heps.
Qed.

(******************************************************************)
(*                        Definition of  Rpower                   *)
(******************************************************************)
 
Definition Rpower := [x : R] [y : R]  ``(exp (y*(ln x)))``.

Infix Local "^R" Rpower (at level 2, left associativity) : R_scope.

(******************************************************************)
(*                        Properties of  Rpower                   *)
(******************************************************************)
 
Theorem Rpower_plus:
 (x, y, z : R)  ``(Rpower z (x+y)) == (Rpower z x)*(Rpower z y)``.
Intros x y z; Unfold Rpower.
Rewrite Rmult_Rplus_distrl; Rewrite exp_plus; Auto.
Qed.
 
Theorem Rpower_mult:
 (x, y, z : R)  ``(Rpower (Rpower x y) z) == (Rpower x (y*z))``.
Intros x y z; Unfold Rpower.
Rewrite ln_exp.
Replace (Rmult z (Rmult y (ln x))) with (Rmult (Rmult y z) (ln x)).
Reflexivity.
Ring.
Qed.
 
Theorem Rpower_O: (x : R) ``0<x`` ->  ``(Rpower x 0) == 1``.
Intros x H; Unfold Rpower.
Rewrite Rmult_Ol; Apply exp_0.
Qed.
 
Theorem Rpower_1: (x : R) ``0<x`` ->  ``(Rpower x 1) == x``.
Intros x H; Unfold Rpower.
Rewrite Rmult_1l; Apply exp_ln; Apply H.
Qed.
 
Theorem Rpower_pow:
 (n : nat) (x : R) ``0<x`` ->  (Rpower x (INR n)) == (pow x n).
Intros n; Elim n; Simpl; Auto; Fold INR.
Intros x H; Apply Rpower_O; Auto.
Intros n1; Case n1.
Intros H x H0; Simpl; Rewrite Rmult_1r; Apply Rpower_1; Auto.
Intros n0 H x H0; Rewrite Rpower_plus; Rewrite H; Try Rewrite Rpower_1; Try Apply Rmult_sym Orelse Assumption.
Qed.
 
Theorem Rpower_lt: (x, y, z : R) ``1<x`` -> ``0<=y`` -> ``y<z`` ->  ``(Rpower x y) < (Rpower x z)``.
Intros x y z H H0 H1.
Unfold Rpower.
Apply exp_increasing.
Apply Rlt_monotony_r.
Rewrite <- ln_1; Apply ln_increasing.
Apply Rlt_R0_R1.
Apply H.
Apply H1.
Qed.
 
Theorem Rpower_sqrt: (x : R) ``0<x`` ->  ``(Rpower x (/2)) == (sqrt x)``.
Intros x H.
Apply ln_inv.
Unfold Rpower; Apply exp_pos.
Apply sqrt_lt_R0; Apply H.
Apply r_Rmult_mult with (INR (S (S O))).
Apply exp_inv.
Fold Rpower.
Cut (Rpower (Rpower x (Rinv (Rplus R1 R1))) (INR (S (S O)))) == (Rpower (sqrt x) (INR (S (S O)))).
Unfold Rpower; Auto.
Rewrite Rpower_mult.
Rewrite Rinv_l.
Replace R1 with (INR (S O)); Auto.
Repeat Rewrite Rpower_pow; Simpl.
Pattern 1 x; Rewrite <- (sqrt_sqrt x (Rlt_le ? ? H)).
Ring.
Apply sqrt_lt_R0; Apply H.
Apply H.
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Qed.
 
Theorem Rpower_Ropp: (x, y : R) ``(Rpower x (-y)) == /(Rpower x y)``.
Unfold Rpower.
Intros x y; Rewrite Ropp_mul1.
Apply exp_Ropp.
Qed.
 
Theorem Rle_Rpower: (e,n,m : R) ``1<e`` -> ``0<=n`` -> ``n<=m`` ->  ``(Rpower e n)<=(Rpower e m)``.
Intros e n m H H0 H1; Case H1.
Intros H2; Left; Apply Rpower_lt; Assumption.
Intros H2; Rewrite H2; Right; Reflexivity.
Qed.
  
Theorem ln_lt_2: ``/2<(ln 2)``.
Apply Rlt_monotony_contra with z := (Rplus R1 R1).
Sup0.
Rewrite Rinv_r.
Apply exp_lt_inv.
Apply Rle_lt_trans with 1 := exp_le_3.
Change (Rlt (Rplus R1 (Rplus R1 R1)) (Rpower (Rplus R1 R1) (Rplus R1 R1))).
Repeat Rewrite Rpower_plus; Repeat Rewrite Rpower_1.
Repeat Rewrite Rmult_Rplus_distrl; Repeat Rewrite Rmult_Rplus_distr;
 Repeat Rewrite Rmult_1l.
Pattern 1 ``3``; Rewrite <- Rplus_Or; Replace ``2+2`` with ``3+1``; [Apply Rlt_compatibility; Apply Rlt_R0_R1 | Ring].
Sup0.
DiscrR.
Qed.

(**************************************)
(* Differentiability of Ln and Rpower *)
(**************************************)

Theorem limit1_ext: (f, g : R ->  R)(D : R ->  Prop)(l, x : R) ((x : R) (D x) ->  (f x) == (g x)) -> (limit1_in f D l x) ->  (limit1_in g D l x).
Intros f g D l x H; Unfold limit1_in limit_in.
Intros H0 eps H1; Case (H0 eps); Auto.
Intros x0 (H2, H3); Exists x0; Split; Auto.
Intros x1 (H4, H5); Rewrite <- H; Auto.
Qed.

Theorem limit1_imp: (f : R ->  R)(D, D1 : R ->  Prop)(l, x : R) ((x : R) (D1 x) ->  (D x)) -> (limit1_in f D l x) ->  (limit1_in f D1 l x).
Intros f D D1 l x H; Unfold limit1_in limit_in.
Intros H0 eps H1; Case (H0 eps H1); Auto.
Intros alpha (H2, H3); Exists alpha; Split; Auto.
Intros d (H4, H5); Apply H3; Split; Auto.
Qed.

Theorem Rinv_Rdiv: (x, y : R) ``x<>0`` -> ``y<>0`` ->  ``/(x/y) == y/x``.
Intros x y H1 H2; Unfold Rdiv; Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Apply Rmult_sym.
Assumption.
Assumption.
Apply Rinv_neq_R0; Assumption.
Qed.

Theorem Dln: (y : R) ``0<y`` ->  (D_in ln Rinv [x:R]``0<x`` y).
Intros y Hy; Unfold D_in.
Apply limit1_ext with f := [x : R](Rinv (Rdiv (Rminus (exp (ln x)) (exp (ln y))) (Rminus (ln x) (ln y)))).
Intros x (HD1, HD2); Repeat Rewrite exp_ln.
Unfold Rdiv; Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Apply Rmult_sym.
Apply Rminus_eq_contra.
Red; Intros H2; Case HD2.
Symmetry; Apply (ln_inv ? ? HD1 Hy H2).
Apply Rminus_eq_contra; Apply (not_sym ? ? HD2).
Apply Rinv_neq_R0; Apply Rminus_eq_contra; Red; Intros H2; Case HD2; Apply ln_inv; Auto.
Assumption.
Assumption.
Apply limit_inv with f := [x : R]  (Rdiv (Rminus (exp (ln x)) (exp (ln y))) (Rminus (ln x) (ln y))).
Apply limit1_imp with f := [x : R] ([x : R]  (Rdiv (Rminus (exp x) (exp (ln y))) (Rminus x (ln y))) (ln x)) D := (Dgf (D_x [x : R]  (Rlt R0 x) y) (D_x [x : R]  True (ln y)) ln).
Intros x (H1, H2); Split.
Split; Auto.
Split; Auto.
Red; Intros H3; Case H2; Apply ln_inv; Auto.
Apply limit_comp with l := (ln y) g := [x : R]  (Rdiv (Rminus (exp x) (exp (ln y))) (Rminus x (ln y))) f := ln.
Apply ln_continue; Auto.
Assert H0 := (derivable_pt_lim_exp (ln y)); Unfold derivable_pt_lim in H0; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Elim (H0 ? H); Intros; Exists (pos x); Split.
Apply (RIneq.cond_pos x).
Intros; Pattern 3 y; Rewrite <- exp_ln.
Pattern 1 x0; Replace x0 with ``(ln y)+(x0-(ln y))``; [Idtac | Ring].
Apply H1.
Elim H2; Intros H3 _; Unfold D_x in H3; Elim H3; Clear H3; Intros _ H3; Apply Rminus_eq_contra; Apply not_sym; Apply H3.
Elim H2; Clear H2; Intros _ H2; Apply H2.
Assumption.
Red; Intro; Rewrite H in Hy; Elim (Rlt_antirefl ? Hy).
Qed.

Lemma derivable_pt_lim_ln : (x:R) ``0<x`` -> (derivable_pt_lim ln x ``/x``).
Intros; Assert H0 := (Dln x H); Unfold D_in in H0; Unfold limit1_in in H0; Unfold limit_in in H0; Simpl in H0; Unfold R_dist in H0; Unfold derivable_pt_lim; Intros; Elim (H0 ? H1); Intros; Elim H2; Clear H2; Intros; Pose alp := (Rmin x0 ``x/2``); Assert H4 : ``0<alp``.
Unfold alp; Unfold Rmin; Case (total_order_Rle x0 ``x/2``); Intro.
Apply H2.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Exists (mkposreal ? H4); Intros; Pattern 2 h; Replace h with ``(x+h)-x``; [Idtac | Ring].
Apply H3; Split.
Unfold D_x; Split.
Case (case_Rabsolu h); Intro.
Assert H7 : ``(Rabsolu h)<x/2``.
Apply Rlt_le_trans with alp.
Apply H6.
Unfold alp; Apply Rmin_r.
Apply Rlt_trans with ``x/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Rewrite Rabsolu_left in H7.
Apply Rlt_anti_compatibility with ``-h-x/2``.
Replace ``-h-x/2+x/2`` with ``-h``; [Idtac | Ring].
Pattern 2 x; Rewrite double_var.
Replace ``-h-x/2+(x/2+x/2+h)`` with ``x/2``; [Apply H7 | Ring].
Apply r.
Apply gt0_plus_ge0_is_gt0; [Assumption | Apply Rle_sym2; Apply r].
Apply not_sym; Apply Rminus_not_eq; Replace ``x+h-x`` with h; [Apply H5 | Ring].
Replace ``x+h-x`` with h; [Apply Rlt_le_trans with alp; [Apply H6 | Unfold alp; Apply Rmin_l] | Ring].
Qed.

Theorem D_in_imp: (f, g : R ->  R)(D, D1 : R ->  Prop)(x : R) ((x : R) (D1 x) ->  (D x)) -> (D_in f g D x) ->  (D_in f g D1 x).
Intros f g D D1 x H; Unfold D_in.
Intros H0; Apply limit1_imp with D := (D_x D x); Auto.
Intros x1 (H1, H2); Split; Auto.
Qed.

Theorem D_in_ext: (f, g, h : R ->  R)(D : R ->  Prop) (x : R) (f x) == (g x) -> (D_in h f D x) ->  (D_in h g D x).
Intros f g h D x H; Unfold D_in.
Rewrite H; Auto.
Qed.

Theorem Dpower: (y, z : R) ``0<y`` -> (D_in [x:R](Rpower x z) [x:R](Rmult z (Rpower x (Rminus z R1))) [x:R]``0<x`` y).
Intros y z H; Apply D_in_imp with D := (Dgf [x : R]  (Rlt R0 x) [x : R]  True ln).
Intros x H0; Repeat Split.
Assumption.
Apply D_in_ext with f := [x : R]  (Rmult (Rinv x) (Rmult z (exp (Rmult z (ln x))))).
Unfold Rminus; Rewrite Rpower_plus; Rewrite Rpower_Ropp; Rewrite (Rpower_1 ? H); Ring.
Apply Dcomp with f := ln g := [x : R]  (exp (Rmult z x)) df := Rinv dg := [x : R]  (Rmult z (exp (Rmult z x))).
Apply (Dln ? H).
Apply D_in_imp with D := (Dgf [x : R]  True [x : R]  True [x : R]  (Rmult z x)).
Intros x H1; Repeat Split; Auto.
Apply (Dcomp [_ : R]  True [_ : R]  True [x : ?]  z exp [x : R]  (Rmult z x) exp); Simpl.
Apply D_in_ext with f := [x : R]  (Rmult z R1).
Apply Rmult_1r.
Apply (Dmult_const [x : ?]  True [x : ?]  x [x : ?]  R1); Apply Dx.
Assert H0 := (derivable_pt_lim_D_in exp exp ``z*(ln y)``); Elim H0; Clear H0; Intros _ H0; Apply H0; Apply derivable_pt_lim_exp.
Qed.

Theorem derivable_pt_lim_power: (x, y : R) (Rlt R0 x) -> (derivable_pt_lim [x : ?]  (Rpower x y) x (Rmult y (Rpower x (Rminus y R1)))).
Intros x y H.
Unfold Rminus; Rewrite Rpower_plus.
Rewrite Rpower_Ropp.
Rewrite Rpower_1; Auto.
Rewrite <- Rmult_assoc.
Unfold Rpower.
Apply derivable_pt_lim_comp with f1 := ln f2 := [x : ?]  (exp (Rmult y x)).
Apply derivable_pt_lim_ln; Assumption.
Rewrite (Rmult_sym y).
Apply derivable_pt_lim_comp with f1 := [x : ?]  (Rmult y x) f2 := exp.
Pattern 2 y; Replace y with (Rplus (Rmult R0 (ln x)) (Rmult y R1)).
Apply derivable_pt_lim_mult with f1 := [x : R]  y f2 := [x : R]  x.
Apply derivable_pt_lim_const with a := y.
Apply derivable_pt_lim_id.
Ring.
Apply derivable_pt_lim_exp.
Qed.
